#!/usr/bin/env bash
# Offline test of the `exorcist draft` pipeline against scripts/mock-nearai.py (no key, no network).
set -euo pipefail
cd "$(dirname "$0")/.."
PORT=${PORT:-18765}
python3 scripts/mock-nearai.py "$PORT" & MP=$!
trap 'kill $MP 2>/dev/null; wait $MP 2>/dev/null; rm -rf Verifier/Drafts' EXIT
sleep 1
OUT=out/drafts-mock EXORCIST_AI_BASE_URL="http://127.0.0.1:$PORT/v1" NEARAI_API_KEY=mock AI_MODEL=mock \
  scripts/drafts.sh > out/drafts-mock.log 2>&1
grep -q "round 2: ✓ the draft compiles: out/drafts-mock/VaultFixed.lean" out/drafts-mock.log   # repair loop ran
test "$(grep -c '✓ same' out/drafts-mock/ASSESSMENT.md)" -eq 8
echo "DRAFT PIPELINE PASS (mock API: request, compile, repair loop, semantic comparison, assessment)"
