//! Deploys the token, hook, vulnerable vault and fixed vault to NEAR **testnet** and replays the
//! ghost-funds attack found by `exorcist check deposit-vulnerable` against both vaults, checking
//! the chain state after every transaction against the model and printing explorer links.
//!
//! Env:  EXORCIST_TESTNET_ACCOUNT      funded testnet account, e.g. you.testnet (needs ~13 NEAR)
//!       EXORCIST_TESTNET_PRIVATE_KEY  its full-access key, ed25519:...
//!       EXORCIST_TESTNET_RPC          optional, default https://rpc.testnet.near.org
//! Refuses to run if anything points at mainnet. Run through scripts/testnet-replay.sh.
use anyhow::{bail, Result};
use exorcist_sandbox::*;
use near_workspaces::types::{NearToken, SecretKey};
use near_workspaces::{Account, AccountId};

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
    let key = std::env::var("EXORCIST_TESTNET_PRIVATE_KEY").map_err(|_| anyhow::anyhow!("set EXORCIST_TESTNET_PRIVATE_KEY"))?;
    let rpc = std::env::var("EXORCIST_TESTNET_RPC").unwrap_or_else(|_| "https://rpc.testnet.near.org".into());
    guard(&account, &rpc)?;

    let worker = near_workspaces::testnet().rpc_addr(&rpc).await?;
    let id: AccountId = account.parse()?;
    let sk: SecretKey = key.parse()?;
    let root = Account::from_secret_key(id, sk, &worker);
    let bal = root.view_account().await?.balance;
    println!("root {} balance {}", root.id(), bal);
    if bal < NearToken::from_near(13) {
        bail!("{} needs about 13 testnet NEAR (storage for 4 contracts); get some from a testnet faucet", root.id());
    }

    let tag = format!("x{}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_secs() % 1_000_000);
    let contract_near = NearToken::from_millinear(2600);
    let user_near = NearToken::from_millinear(500);
    println!("deploying token + hook (shared) ...");
    let shared = deploy_shared(&root, &format!("-{tag}"), 400, &root, "ok", contract_near).await?;
    println!("  token {EXPLORER}/address/{}\n  hook  {EXPLORER}/address/{}", shared.token.id(), shared.hook.id());

    let d = load("deposit-vulnerable")?;
    for (variant, wasm_name, rep) in [
        ("vulnerable", "vault_deposit_vulnerable.wasm", &d["violation"]["replay_vulnerable"]),
        ("fixed", "vault_fixed.wasm", &d["violation"]["replay_fixed"]),
    ] {
        let p = format!("-{tag}{}", &variant[..1]);
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
