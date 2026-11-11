#!/usr/bin/env bash
# Replay the ghost-funds attack on NEAR TESTNET against the vulnerable and the fixed vault.
#   export EXORCIST_TESTNET_ACCOUNT=you.testnet
#   (key from ~/.near-credentials/testnet/<account>.json, or export EXORCIST_TESTNET_PRIVATE_KEY; never commit it)
#   scripts/testnet-replay.sh
# Needs about 10 testnet NEAR on the account (storage for 4 small contracts). Never touches mainnet.
# Optional: EXORCIST_TESTNET_RPC (default rpc.testnet.near.org; rpc.testnet.fastnear.com rate-limits less),
#           EXORCIST_TESTNET_ONLY=vulnerable|fixed, EXORCIST_TESTNET_REUSE=<run tag> (reuse that run's token + hook),
#           EXORCIST_TESTNET_SUFFIX=<s> (fresh alice/eve/vault names when re-running a variant).
set -euo pipefail
cd "$(dirname "$0")/.."
: "${EXORCIST_TESTNET_ACCOUNT:?set EXORCIST_TESTNET_ACCOUNT (a .testnet account)}"
RPC="${EXORCIST_TESTNET_RPC:-https://rpc.testnet.near.org}"
case "$EXORCIST_TESTNET_ACCOUNT" in *.testnet) ;; *) echo "refusing: $EXORCIST_TESTNET_ACCOUNT is not a .testnet account"; exit 1;; esac
case "$RPC" in *mainnet*) echo "refusing: RPC points at mainnet"; exit 1;; *testnet*) ;; *) echo "refusing: RPC $RPC is not a testnet RPC"; exit 1;; esac
for v in NEAR_ENV NEAR_NETWORK; do
  case "${!v:-}" in *mainnet*) echo "refusing: $v=${!v}"; exit 1;; esac
done
# key: EXORCIST_TESTNET_PRIVATE_KEY, or ~/.near-credentials/testnet/<account>.json (near-cli legacy keychain)
if [ -z "${EXORCIST_TESTNET_PRIVATE_KEY:-}" ] && [ ! -f "$HOME/.near-credentials/testnet/$EXORCIST_TESTNET_ACCOUNT.json" ]; then
  echo "no key: set EXORCIST_TESTNET_PRIVATE_KEY or create ~/.near-credentials/testnet/$EXORCIST_TESTNET_ACCOUNT.json"; exit 1
fi
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
make traces >/dev/null
(cd sandbox && ./build-wasm.sh >/dev/null)
cd sandbox && cargo run -q --release --bin testnet-replay
