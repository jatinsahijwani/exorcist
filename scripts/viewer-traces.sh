#!/usr/bin/env bash
# Regenerates the trace viewer's data from real `exorcist check --json` output. Nothing in
# web/public/traces/ is written by hand: this script is the only source, and CI checks that the
# committed files equal its fresh output (scripts/viewer-traces.sh --check).
#
# The only change made to the CLI output: `search_ms` (wall-clock time, machine-dependent) is
# dropped, via scripts/strip-timing.py, so the files are reproducible byte for byte.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
EXORCIST=./.lake/build/bin/exorcist
[ -x "$EXORCIST" ] || lake build exorcist >/dev/null
OUT=web/public/traces
mkdir -p "$OUT"

# 1. the attack, found automatically on the vulnerable model (exit code 1 = violation found, expected)
set +e
"$EXORCIST" check incident-2026-10 --json "$OUT/incident-2026-10.json" >/dev/null; c1=$?
# 2. the fixed model, plus the same attack re-run on it (exit code 0 = no violation, expected)
"$EXORCIST" check incident-2026-10-fixed --attack-from incident-2026-10 \
  --json "$OUT/incident-2026-10-fixed.json" >/dev/null; c2=$?
set -e
[ "$c1" -eq 1 ] || { echo "expected a violation on incident-2026-10 (exit 1), got $c1"; exit 1; }
[ "$c2" -eq 0 ] || { echo "expected no violation on incident-2026-10-fixed (exit 0), got $c2"; exit 1; }
python3 scripts/strip-timing.py "$OUT/incident-2026-10.json" "$OUT/incident-2026-10-fixed.json"

if [ "${1:-}" = "--check" ]; then
  if [ -z "$(git status --porcelain -- "$OUT")" ]; then
    echo "OK: committed viewer traces equal fresh exorcist output"
  else
    git status --porcelain -- "$OUT"; git --no-pager diff --stat -- "$OUT"
    echo "MISMATCH: web/public/traces differs from fresh exorcist output (run scripts/viewer-traces.sh and commit)"
    exit 1
  fi
else
  echo "wrote $OUT/incident-2026-10.json and $OUT/incident-2026-10-fixed.json"
fi
