#!/usr/bin/env bash
# Check that the four testnet transactions in the README exist and are final (public RPC, no account needed).
set -euo pipefail
RPC="${EXORCIST_TESTNET_RPC:-https://rpc.testnet.fastnear.com}"
ok=0
while read -r hash sender what; do
  r=$(curl -sS -m 30 -X POST "$RPC" -H 'content-type: application/json' \
    -d "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tx\",\"params\":{\"tx_hash\":\"$hash\",\"sender_account_id\":\"$sender\",\"wait_until\":\"FINAL\"}}")
  if echo "$r" | grep -q '"final_execution_status":"FINAL"'; then ok=$((ok+1)); echo "FINAL  $what  https://testnet.nearblocks.io/txns/$hash"; else echo "MISSING $what $hash"; fi
done <<'TXS'
EBigWS13rHHqTDYNKMsamY9d4bhcdpuR4v1GFUkMxycN eve-x404319v.exorcist-replay-35b9fa.testnet vulnerable-vault deposit (refunded and credited)
qSjvAX1otfxW8iBi2SJ9ebh5cMcYqhry2ftW5Wo3czm eve-x404319v.exorcist-replay-35b9fa.testnet vulnerable-vault withdraw (pays out)
G9f5oowAE1Y1tmjBR1ePsAxmPtdSdtZ6aYcYkuPKppqG eve-x404319f2.exorcist-replay-35b9fa.testnet fixed-vault deposit (refunded, not credited)
FNioJzWavui9B3AN4jqMkuL5FUUQeTz2RYzaPjDDCDzV eve-x404319f2.exorcist-replay-35b9fa.testnet fixed-vault withdraw (rejected)
TXS
echo "$ok/4 FINAL"
