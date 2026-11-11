//! Replays the traces exported by `exorcist check <model> --json` against the real Rust contracts
//! in a local NEAR sandbox, and checks after every transaction that
//!   * every token balance and ledger entry equals the model's prediction, and
//!   * the receipts that ran (and which of them failed) match the model's receipts.
//! Any mismatch is a bug in the model (or in a contract) and fails the test.

use anyhow::{anyhow, bail, Context, Result};
use near_workspaces::network::Sandbox;
use near_workspaces::result::ExecutionFinalResult;
use near_workspaces::types::NearToken;
use near_workspaces::{Account, AccountId, Contract, Worker};
use serde_json::{json, Value};
use std::collections::BTreeMap;

struct Env {
    _worker: Worker<Sandbox>,
    root: Account,
    alice: Account,
    eve: Account,
    token: Contract,
    vault: Contract,
    hook: Contract,
}

impl Env {
    fn id(&self, name: &str) -> Result<AccountId> {
        Ok(match name {
            "alice" => self.alice.id().clone(),
            "eve" => self.eve.id().clone(),
            "token" => self.token.id().clone(),
            "vault" => self.vault.id().clone(),
            "hook" => self.hook.id().clone(),
            other => bail!("unknown actor {other}"),
        })
    }

    fn name(&self, id: &AccountId) -> String {
        for n in ["alice", "eve", "token", "vault", "hook"] {
            if self.id(n).ok().as_ref() == Some(id) {
                return n.to_string();
            }
        }
        id.to_string()
    }

    fn account(&self, name: &str) -> Result<&Account> {
        match name {
            "alice" => Ok(&self.alice),
            "eve" => Ok(&self.eve),
            other => bail!("{other} cannot sign transactions in the replay"),
        }
    }

    async fn ft(&self, who: &str) -> Result<u128> {
        let v: String = self.token.view("ft_balance_of").args_json(json!({ "account_id": self.id(who)? })).await?.json()?;
        Ok(v.parse()?)
    }

    async fn ledger(&self, who: &str) -> Result<u128> {
        let v: String = self.vault.view("ledger_of").args_json(json!({ "account_id": self.id(who)? })).await?.json()?;
        Ok(v.parse()?)
    }

    /// Read the observable state in the same shape as the model's `state_after`.
    async fn state(&self) -> Result<BTreeMap<String, u128>> {
        let mut m = BTreeMap::new();
        for a in ["alice", "eve", "vault", "hook"] {
            m.insert(format!("ft.{a}"), self.ft(a).await?);
        }
        for a in ["alice", "eve"] {
            m.insert(format!("ledger.{a}"), self.ledger(a).await?);
        }
        Ok(m)
    }
}

fn wasm(name: &str) -> Result<Vec<u8>> {
    let p = format!("{}/res/{}", env!("CARGO_MANIFEST_DIR"), name);
    std::fs::read(&p).with_context(|| format!("missing {p}; run sandbox/build-wasm.sh"))
}

fn model_state(v: &Value) -> Result<BTreeMap<String, u128>> {
    let mut m = BTreeMap::new();
    for a in ["alice", "eve", "vault", "hook"] {
        m.insert(format!("ft.{a}"), v["ft"][a].as_u64().ok_or_else(|| anyhow!("bad ft.{a}"))? as u128);
    }
    for a in ["alice", "eve"] {
        m.insert(format!("ledger.{a}"), v["ledger"][a].as_u64().ok_or_else(|| anyhow!("bad ledger.{a}"))? as u128);
    }
    Ok(m)
}

fn ok(r: ExecutionFinalResult, what: &str) -> Result<()> {
    if r.is_failure() {
        bail!("setup step '{what}' failed: {:?}", r.into_result().err());
    }
    Ok(())
}

async fn sub(root: &Account, name: &str) -> Result<Account> {
    let r = root.create_subaccount(name).initial_balance(NearToken::from_near(20)).transact().await?;
    Ok(r.into_result()?)
}

/// Deploy token, vault variant and hook; reach the model's initial state with real transactions:
/// alice and eve get 100 tokens each, alice deposits her 100 into the vault.
async fn setup(vault_wasm: &str, hook_mode: &str) -> Result<Env> {
    let worker = near_workspaces::sandbox().await?;
    let root = worker.root_account()?;
    let alice = sub(&root, "alice").await?;
    let eve = sub(&root, "eve").await?;
    let token = sub(&root, "token").await?.deploy(&wasm("token.wasm")?).await?.into_result()?;
    let vault = sub(&root, "vault").await?.deploy(&wasm(vault_wasm)?).await?.into_result()?;
    let hook = sub(&root, "hook").await?.deploy(&wasm("hook.wasm")?).await?.into_result()?;

    ok(token.call("new").args_json(json!({ "owner_id": root.id(), "total_supply": "200" })).transact().await?, "token.new")?;
    ok(vault.call("new").args_json(json!({ "token": token.id() })).transact().await?, "vault.new")?;
    ok(hook.call("new").args_json(json!({ "owner": eve.id(), "mode": hook_mode })).transact().await?, "hook.new")?;
    for a in [alice.id(), eve.id(), vault.id(), hook.id()] {
        ok(root.call(token.id(), "register").args_json(json!({ "account_id": a }))
            .deposit(NearToken::from_millinear(10)).transact().await?, "register")?;
    }
    for a in [alice.id(), eve.id()] {
        ok(root.call(token.id(), "ft_transfer").args_json(json!({ "receiver_id": a, "amount": "100" }))
            .deposit(NearToken::from_yoctonear(1)).transact().await?, "fund")?;
    }
    ok(alice.call(token.id(), "ft_transfer_call")
        .args_json(json!({ "receiver_id": vault.id(), "amount": "100", "msg": "" }))
        .deposit(NearToken::from_yoctonear(1)).max_gas().transact().await?, "alice deposit")?;
    Ok(Env { _worker: worker, root, alice, eve, token, vault, hook })
}

/// Translate the model's argument names/values into the contracts' JSON.
fn real_args(env: &Env, args: &Value) -> Result<Value> {
    let mut out = serde_json::Map::new();
    for (k, v) in args.as_object().ok_or_else(|| anyhow!("args not an object"))? {
        let nv = match (k.as_str(), v) {
            ("amount", Value::Number(n)) => json!(n.to_string()),
            ("msg", Value::String(s)) if s.starts_with("notify ") => {
                json!(format!("notify {}", env.id(&s["notify ".len()..])?))
            }
            (_, Value::String(s)) if ["alice", "eve", "token", "vault", "hook"].contains(&s.as_str()) => {
                json!(env.id(s)?.to_string())
            }
            _ => v.clone(),
        };
        out.insert(k.clone(), nv);
    }
    Ok(Value::Object(out))
}

/// Make the failures the model injected actually happen in the sandbox.
async fn inject(env: &Env, tx: &Value, on: bool, hook_mode: &str) -> Result<()> {
    for inj in tx["inject"].as_array().unwrap_or(&vec![]) {
        match (inj["receiver"].as_str(), inj["method"].as_str()) {
            (Some("hook"), Some("on_deposit")) => {
                let mode = if on { "panic" } else { hook_mode };
                ok(env.eve.call(env.hook.id(), "set_mode").args_json(json!({ "mode": mode })).transact().await?, "hook.set_mode")?;
            }
            (Some("token"), Some("ft_transfer")) => {
                // the payout fails because the receiver is not registered with the token
                let who = env.account(tx["signer"].as_str().unwrap_or(""))?;
                if on {
                    ok(who.call(env.token.id(), "unregister").deposit(NearToken::from_yoctonear(1)).transact().await?, "unregister")?;
                } else {
                    ok(env.root.call(env.token.id(), "register").args_json(json!({ "account_id": who.id() }))
                        .deposit(NearToken::from_millinear(10)).transact().await?, "re-register")?;
                }
            }
            other => bail!("no sandbox recipe for injected failure {other:?}"),
        }
    }
    Ok(())
}

/// Receipts tagged by our contracts' `EXORCIST <method>` log line, with success/failure.
fn observed_receipts(env: &Env, r: &ExecutionFinalResult) -> Vec<(String, String, String)> {
    let mut v: Vec<(String, String, String)> = r
        .receipt_outcomes()
        .iter()
        .filter_map(|o| {
            let m = o.logs.iter().find_map(|l| l.strip_prefix("EXORCIST ").map(str::to_string))?;
            let outcome = if o.is_success() { "ok" } else { "failed" };
            Some((env.name(&o.executor_id), m, outcome.to_string()))
        })
        .collect();
    v.sort();
    v
}

fn expected_receipts(tx: &Value) -> Vec<(String, String, String)> {
    let mut v: Vec<(String, String, String)> = tx["receipts"]
        .as_array()
        .unwrap_or(&vec![])
        .iter()
        .map(|r| {
            (r["receiver"].as_str().unwrap_or("").to_string(),
             r["method"].as_str().unwrap_or("").to_string(),
             r["outcome"].as_str().unwrap_or("").to_string())
        })
        .collect();
    v.sort();
    v
}

/// Replay one exported replay object (`{vault_wasm, hook_mode, txs}`).
async fn replay(label: &str, initial: &Value, rep: &Value) -> Result<()> {
    let vault_wasm = rep["vault_wasm"].as_str().unwrap();
    let hook_mode = rep["hook_mode"].as_str().unwrap();
    println!("── {label}: {vault_wasm}, hook mode {hook_mode}");
    let env = setup(vault_wasm, hook_mode).await?;
    let s0 = env.state().await?;
    assert_eq!(s0, model_state(initial)?, "{label}: initial state differs from the model");
    for (i, tx) in rep["txs"].as_array().unwrap().iter().enumerate() {
        let signer = env.account(tx["signer"].as_str().unwrap())?;
        let receiver = env.id(tx["receiver"].as_str().unwrap())?;
        let method = tx["method"].as_str().unwrap();
        let args = real_args(&env, &tx["args"])?;
        inject(&env, tx, true, hook_mode).await?;
        let res = signer
            .call(&receiver, method)
            .args_json(args)
            .deposit(NearToken::from_yoctonear(tx["deposit_yocto"].as_u64().unwrap() as u128))
            .max_gas()
            .transact()
            .await?;
        let seen = observed_receipts(&env, &res);
        inject(&env, tx, false, hook_mode).await?;
        let state = env.state().await?;
        println!("   tx{} {} → {}.{}  receipts {:?}", i + 1, tx["signer"], tx["receiver"], method, seen);
        println!("        sandbox {:?}", state);
        assert_eq!(seen, expected_receipts(tx), "{label} tx{}: receipt outcomes differ from the model", i + 1);
        assert_eq!(state, model_state(&tx["state_after"])?, "{label} tx{}: state differs from the model", i + 1);
    }
    println!("   ✓ {label}: sandbox matches the model after every transaction");
    Ok(())
}

fn load(model: &str) -> Result<Value> {
    let p = format!("{}/traces/{}.json", env!("CARGO_MANIFEST_DIR"), model);
    let s = std::fs::read_to_string(&p).with_context(|| format!("missing {p}; run `make traces`"))?;
    Ok(serde_json::from_str(&s)?)
}

async fn replay_violation(model: &str, which: &str) -> Result<()> {
    let d = load(model)?;
    replay(&format!("{model} [{which}]"), &d["initial_state"], &d["violation"][which]).await
}

async fn replay_liveness(model: &str) -> Result<()> {
    let d = load(model)?;
    for (i, g) in d["liveness"].as_array().unwrap().iter().enumerate() {
        replay(&format!("{model} happy path {}: {}", i + 1, g["goal"].as_str().unwrap()), &d["initial_state"], &g["replay"]).await?;
    }
    Ok(())
}

#[tokio::test]
async fn happy_path_fixed_vault() -> Result<()> { replay_liveness("deposit-fixed").await }

#[tokio::test]
async fn happy_path_fixed_vault_noreturn_hook() -> Result<()> { replay_liveness("noreturn-fixed").await }

#[tokio::test]
async fn deposit_attack_on_vulnerable_vault() -> Result<()> { replay_violation("deposit-vulnerable", "replay_vulnerable").await }

#[tokio::test]
async fn deposit_attack_fails_on_fixed_vault() -> Result<()> { replay_violation("deposit-vulnerable", "replay_fixed").await }

#[tokio::test]
async fn noreturn_attack_on_vulnerable_vault() -> Result<()> { replay_violation("noreturn-vulnerable", "replay_vulnerable").await }

#[tokio::test]
async fn noreturn_attack_fails_on_fixed_vault() -> Result<()> { replay_violation("noreturn-vulnerable", "replay_fixed").await }

#[tokio::test]
async fn withdraw_without_restore_on_vulnerable_vault() -> Result<()> { replay_violation("withdraw-vulnerable", "replay_vulnerable").await }

#[tokio::test]
async fn withdraw_restores_on_fixed_vault() -> Result<()> { replay_violation("withdraw-vulnerable", "replay_fixed").await }

/// Negative control: the harness must notice when the contract does not behave as predicted.
/// Replays the vulnerable vault's expected states against the fixed vault's wasm.
#[tokio::test]
#[should_panic(expected = "differ")]
async fn harness_detects_model_mismatch() {
    let d = load("deposit-vulnerable").unwrap();
    let mut rep = d["violation"]["replay_vulnerable"].clone();
    rep["vault_wasm"] = json!("vault_fixed.wasm");
    replay("negative control", &d["initial_state"], &rep).await.unwrap();
}
