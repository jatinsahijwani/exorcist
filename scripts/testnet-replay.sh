#!/usr/bin/env bash
# Replay the ghost-funds attack on NEAR TESTNET against the vulnerable and the fixed vault.
#   export EXORCIST_TESTNET_ACCOUNT=you.testnet
#   export EXORCIST_TESTNET_PRIVATE_KEY=ed25519:...     (never commit this)
#   scripts/testnet-replay.sh
# Needs ~13 testnet NEAR on the account (storage for 4 small contracts). Never touches mainnet.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${EXORCIST_TESTNET_ACCOUNT:?set EXORCIST_TESTNET_ACCOUNT (a .testnet account)}"
: "${EXORCIST_TESTNET_PRIVATE_KEY:?set EXORCIST_TESTNET_PRIVATE_KEY}"
RPC="${EXORCIST_TESTNET_RPC:-https://rpc.testnet.near.org}"
case "$EXORCIST_TESTNET_ACCOUNT" in *.testnet) ;; *) echo "refusing: $EXORCIST_TESTNET_ACCOUNT is not a .testnet account"; exit 1;; esac
case "$RPC" in *mainnet*) echo "refusing: RPC points at mainnet"; exit 1;; *testnet*) ;; *) echo "refusing: RPC $RPC is not a testnet RPC"; exit 1;; esac
for v in NEAR_ENV NEAR_NETWORK; do
  case "${!v:-}" in *mainnet*) echo "refusing: $v=${!v}"; exit 1;; esac
done
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
make traces >/dev/null
(cd sandbox && ./build-wasm.sh >/dev/null)
cd sandbox && cargo run -q --release --bin testnet-replay
