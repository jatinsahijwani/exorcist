//! Sandbox validation: every exported trace, replayed against the real contracts.
use anyhow::Result;
use exorcist_sandbox::*;
use serde_json::{json, Value};

async fn replay(label: &str, initial: &Value, rep: &Value) -> Result<()> {
    let worker = near_workspaces::sandbox().await?;
    let root = worker.root_account()?;
    println!("── {label}: {}, hook mode {}", rep["vault_wasm"], rep["hook_mode"]);
    let env = setup_sandbox(&root, rep["vault_wasm"].as_str().unwrap(), rep["hook_mode"].as_str().unwrap()).await?;
    replay_on(&env, label, initial, rep).await?;
    Ok(())
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
