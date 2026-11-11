//! Deploys the token, hook, vulnerable vault and fixed vault to NEAR **testnet** and replays the
//! ghost-funds attack found by `exorcist check deposit-vulnerable` against both vaults, checking
//! the chain state after every transaction against the model and printing explorer links.
//!
//! Env:  EXORCIST_TESTNET_ACCOUNT      funded testnet account, e.g. you.testnet (needs ~13 NEAR)
//!       EXORCIST_TESTNET_PRIVATE_KEY  optional: its full-access key; if unset, read from the standard
//!                                     ~/.near-credentials/testnet/<account>.json (as near-cli writes it)
//!       EXORCIST_TESTNET_RPC          optional, default https://rpc.testnet.near.org
//! Refuses to run if anything points at mainnet. Run through scripts/testnet-replay.sh.
use anyhow::{bail, Result};
use exorcist_sandbox::*;
use near_workspaces::types::{KeyType, NearToken, SecretKey};
use near_workspaces::{Account, AccountId, Contract};

const EXPLORER: &str = "https://testnet.nearblocks.io";

fn guard(account: &str, rpc: &str) -> Result<()> {
    let all = format!("{account} {rpc}").to_lowercase();
    if all.contains("mainnet") || !account.ends_with(".testnet") || !rpc.contains("testnet") || account.ends_with(".near") {
        bail!("refusing to run: account must end in .testnet and the RPC must be a testnet RPC (got {account}, {rpc})");
    }
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    let account = std::env::var("EXORCIST_TESTNET_ACCOUNT").map_err(|_| anyhow::anyhow!("set EXORCIST_TESTNET_ACCOUNT"))?;
    let key = match std::env::var("EXORCIST_TESTNET_PRIVATE_KEY") {
        Ok(k) => k,
        Err(_) => {
            let home = std::env::var("HOME")?;
            let p = format!("{home}/.near-credentials/testnet/{account}.json");
            let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&p)
                .map_err(|_| anyhow::anyhow!("set EXORCIST_TESTNET_PRIVATE_KEY or create {p} (near-cli legacy keychain)"))?)?;
            v["private_key"].as_str().ok_or_else(|| anyhow::anyhow!("no private_key in {p}"))?.to_string()
        }
    };
    let rpc = std::env::var("EXORCIST_TESTNET_RPC").unwrap_or_else(|_| "https://rpc.testnet.near.org".into());
    guard(&account, &rpc)?;

    let worker = near_workspaces::testnet().rpc_addr(&rpc).await?;
    let id: AccountId = account.parse()?;
    let sk: SecretKey = key.parse()?;
    let root = Account::from_secret_key(id, sk, &worker);
    let bal = root.view_account().await?.balance;
    // storage staking: 1 NEAR per 100 kB of contract code, plus a margin for state and gas
    let need = |w: &str| -> Result<NearToken> {
        let bytes = std::fs::read(format!("{}/res/{}", env!("CARGO_MANIFEST_DIR"), w))?.len() as u128;
        Ok(NearToken::from_yoctonear(bytes * 10u128.pow(19) + NearToken::from_millinear(60).as_yoctonear()))
    };
    let (n_tok, n_hook) = (need("token.wasm")?, need("hook.wasm")?);
    let (n_vv, n_vf) = (need("vault_deposit_vulnerable.wasm")?, need("vault_fixed.wasm")?);
    let user_near = NearToken::from_millinear(300);
    let total = n_tok.as_yoctonear() + n_hook.as_yoctonear() + n_vv.as_yoctonear() + n_vf.as_yoctonear()
        + 4 * user_near.as_yoctonear() + NearToken::from_millinear(400).as_yoctonear();
    println!("root {} balance {} (this run needs about {:.2} NEAR)", root.id(), bal, total as f64 / 1e24);
    let total = if std::env::var("EXORCIST_TESTNET_REUSE").is_ok() { total - n_tok.as_yoctonear() - n_hook.as_yoctonear() } else { total };
    let total = match std::env::var("EXORCIST_TESTNET_ONLY").ok().as_deref() {
        Some("fixed") => total - n_vv.as_yoctonear() - 2 * user_near.as_yoctonear(),
        Some("vulnerable") => total - n_vf.as_yoctonear() - 2 * user_near.as_yoctonear(),
        _ => total,
    };
    if bal.as_yoctonear() < total {
        bail!("{} needs about {:.2} testnet NEAR; get more from a testnet faucet", root.id(), total as f64 / 1e24);
    }

    // EXORCIST_TESTNET_REUSE=<tag>: reuse the token + hook of an earlier run (e.g. after an RPC rate limit)
    // EXORCIST_TESTNET_ONLY=vulnerable|fixed: replay only one vault
    let reuse = std::env::var("EXORCIST_TESTNET_REUSE").ok();
    let only = std::env::var("EXORCIST_TESTNET_ONLY").ok();
    let tag = reuse.clone().unwrap_or(format!("x{}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_secs() % 1_000_000));
    let shared = if reuse.is_some() {
        println!("reusing token + hook of run {tag} ...");
        // view-only handles: calls on these contracts are signed by other accounts
        let dummy = || SecretKey::from_random(KeyType::ED25519);
        let tid: AccountId = format!("token-{tag}.{}", root.id()).parse()?;
        let hid: AccountId = format!("hook-{tag}.{}", root.id()).parse()?;
        Shared { token: Contract::from_secret_key(tid, dummy(), &worker), hook: Contract::from_secret_key(hid, dummy(), &worker),
                 hook_owner: root.clone() }
    } else {
        println!("deploying token + hook (shared) ...");
        deploy_shared_sized(&root, &format!("-{tag}"), 400, &root, "ok", n_tok, n_hook).await?
    };
    println!("  token {EXPLORER}/address/{}\n  hook  {EXPLORER}/address/{}", shared.token.id(), shared.hook.id());

    let d = load("deposit-vulnerable")?;
    for (variant, wasm_name, rep, contract_near) in [
        ("vulnerable", "vault_deposit_vulnerable.wasm", &d["violation"]["replay_vulnerable"], n_vv),
        ("fixed", "vault_fixed.wasm", &d["violation"]["replay_fixed"], n_vf),
    ] {
        if only.as_deref().is_some_and(|o| o != variant) { continue; }
        let suffix = std::env::var("EXORCIST_TESTNET_SUFFIX").unwrap_or_default();
        let p = format!("-{tag}{}{suffix}", &variant[..1]);
        println!("\n== {variant} vault: setting up alice (100 deposited) and eve (100 tokens) ...");
        let alice = sub(&root, &format!("alice{p}"), user_near).await?;
        let eve = sub(&root, &format!("eve{p}"), user_near).await?;
        let env = setup_run(&root, &shared, &p, wasm_name, alice, eve, contract_near).await?;
        println!("  vault {EXPLORER}/address/{}", env.vault.id());
        let hashes = replay_on(&env, &format!("deposit attack on the {variant} vault"), &d["initial_state"], rep).await?;
        for (i, h) in hashes.iter().enumerate() {
            println!("  tx{} {EXPLORER}/txns/{h}", i + 1);
        }
        let s = env.state().await?;
        println!("  final: vault holds {} tokens, ledger alice={} eve={}, eve holds {}",
                 s["ft.vault"], s["ledger.alice"], s["ledger.eve"], s["ft.eve"]);
    }
    println!("\nDone. Both runs matched the Lean model transaction by transaction.");
    Ok(())
}
