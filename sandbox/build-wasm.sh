#!/usr/bin/env bash
# Build the sandbox contracts to wasm (res/). Variants of the vault are separate builds.
set -euo pipefail
cd "$(dirname "$0")"
T=wasm32-unknown-unknown
OUT=target/$T/release
cargo build -q --target $T --release -p exorcist-token -p exorcist-hook
cp $OUT/exorcist_token.wasm res/token.wasm
cp $OUT/exorcist_hook.wasm res/hook.wasm
cargo build -q --target $T --release -p exorcist-vault
cp $OUT/exorcist_vault.wasm res/vault_fixed.wasm
cargo build -q --target $T --release -p exorcist-vault --features ghost_funds_bug
cp $OUT/exorcist_vault.wasm res/vault_deposit_vulnerable.wasm
cargo build -q --target $T --release -p exorcist-vault --features withdraw_no_restore_bug
cp $OUT/exorcist_vault.wasm res/vault_withdraw_vulnerable.wasm
ls -la res/*.wasm
