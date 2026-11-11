#!/usr/bin/env bash
# Re-check the committed NEAR AI drafts WITHOUT any key: compile each draft and re-run the semantic
# comparison with the hand-written models (drafts/Compare.lean). Expected: 8 lines ending "✓ same".
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p Verifier/Drafts
trap 'rm -rf Verifier/Drafts' EXIT
for n in Token Hook VaultFixed VaultGhost VaultNoRestore; do
  cp "drafts/$n.lean" "Verifier/Drafts/$n.lean"
  lake build "Verifier.Drafts.$n" >/dev/null
done
lake env lean drafts/Compare.lean
