#!/usr/bin/env bash
# One-command reproduction: build, find the bugs, check witnesses, prove the fixes, replay in the
# NEAR sandbox, and print a PASS/FAIL table. No keys, no network beyond fetching toolchains/crates.
#   scripts/demo.sh          full run (includes the near-workspaces sandbox)
#   QUICK=1 scripts/demo.sh  skip the sandbox (fast screening)
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
DEPTH="${DEPTH:-10}"
QUICK="${QUICK:-0}"
EX=./.lake/build/bin/exorcist
ROWS=()
FAILED=0
row() { ROWS+=("$1|$2|$3"); [ "$1" = "PASS" ] || FAILED=1; }
hr() { printf '\n\033[1m== %s\033[0m\n' "$1"; }

command -v lake >/dev/null || { echo "Lean is not installed. Install elan: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none"; exit 2; }

hr "1. Build the Lean models, the proofs and the exorcist CLI (lake build)"
if lake build 2>&1 | tail -1; then
  row PASS "lake build: semantics, models, witness + liveness theorems, unbounded proof" "kernel-checked"
else
  row FAIL "lake build" "-"; echo "build failed"; exit 1
fi

mkdir -p out
hr "2. Find the bugs (exorcist check, bounded search) — starting with a minimal model of the Oct 2026 NEAR Intents mechanism (not their contract)"
for m in incident-2026-10 deposit-vulnerable noreturn-vulnerable withdraw-vulnerable withdraw-fixed-callback-fail; do
  echo; echo "\$ exorcist check $m --depth $DEPTH"
  out=$($EX check "$m" --depth "$DEPTH" --json "out/$m.json" 2>&1; echo "exit=$?")
  echo "$out" | sed -n '/^NOTE/p;/^RESULT/,/kernel/p'
  code=$(echo "$out" | tail -1 | cut -d= -f2)
  d=$(python3 -c "import json;d=json.load(open('out/$m.json'));print(f\"{d['violation']['depth']} ({d['states_explored']} states)\")" 2>/dev/null || echo "?")
  if [ "$code" = "1" ] && [ -f "out/$m.witness.lean" ] && lake env lean "out/$m.witness.lean" >/dev/null 2>&1; then
    row PASS "$m: attack found, witness theorem kernel-checked" "found at depth $d"
  else
    row FAIL "$m: expected a violation with a checked witness" "-"
  fi
done

hr "3. Check the fixed contracts (bounded search) and that honest use still works"
for m in incident-2026-10-fixed deposit-fixed noreturn-fixed withdraw-fixed; do
  echo; echo "\$ exorcist check $m --depth $DEPTH"
  out=$($EX check "$m" --depth "$DEPTH" --json "out/$m.json" 2>&1; echo "exit=$?")
  echo "$out" | sed -n '/^RESULT/,/^JSON/p' | grep -v '^JSON'
  code=$(echo "$out" | tail -1 | cut -d= -f2)
  if [ "$code" = "0" ]; then
    row PASS "$m: no violation, honest deposit + withdraw reachable" "bounded to depth $DEPTH"
  else
    row FAIL "$m: check exited $code" "bounded to depth $DEPTH"
  fi
done

hr "4. Prove the fixes (exorcist prove, unbounded, offline)"
for m in incident-2026-10-fixed deposit-fixed noreturn-fixed withdraw-fixed; do
  echo; echo "\$ exorcist prove $m"
  if $EX prove "$m" | tee "out/prove-$m.axioms.txt"; then
    row PASS "$m: solvent (sum of ledger <= tokens held)" "proven for all traces"
  else
    row FAIL "$m: prove" "-"
  fi
done
for m in withdraw-fixed noreturn-fixed; do
  if grep -q "no_stuck_all_traces' depends on axioms" "out/prove-$m.axioms.txt" 2>/dev/null; then
    row PASS "$m: no stuck funds (assumes: callbacks don't fail, no donations)" "proven for all traces"
  else
    row FAIL "$m: no stuck funds proof" "-"
  fi
done

hr "5. Agent gate (MCP server): an AI agent is blocked from deploying the vulnerable vault, allowed after the fix"
if python3 mcp/agent_gate_demo.py | tee out/agent-gate.txt | tail -12; then
  row PASS "agent gate (MCP): vulnerable blocked, fixed allowed" "check + prove via MCP"
else
  row FAIL "agent gate (MCP)" "-"
fi

if [ "$QUICK" != "1" ]; then
  hr "6. Replay every trace against the real Rust contracts in a local NEAR sandbox (near-workspaces)"
  if make -s traces >/dev/null && (cd sandbox && ./build-wasm.sh >/dev/null && cargo test --test replay -- --test-threads=4 2>&1 | tee /tmp/exorcist-sandbox.log | grep -E '^test |test result'); then
    while read -r line; do
      name=$(echo "$line" | sed -E 's/^test ([a-z_]+) .*/\1/')
      label="matches model step by step"
      [ "$name" = "harness_detects_model_mismatch" ] && label="negative control: harness rejects a wrong prediction"
      if echo "$line" | grep -q ' ok$'; then row PASS "sandbox: $name" "$label"; else row FAIL "sandbox: $name" "-"; fi
    done < <(grep -E '^test [a-z_]+ .*\.\.\. ' /tmp/exorcist-sandbox.log)
  else
    row FAIL "sandbox tests" "see /tmp/exorcist-sandbox.log"
  fi
else
  row PASS "sandbox replay skipped (QUICK=1)" "-"
fi

hr "SUMMARY"
printf '%-6s  %-72s  %s\n' "" "result" "label"
for r in "${ROWS[@]}"; do
  IFS='|' read -r s what label <<<"$r"
  printf '%-6s  %-72s  %s\n' "$s" "$what" "$label"
done
if [ "$FAILED" = "0" ]; then echo; echo "ALL PASS"; else echo; echo "SOME CHECKS FAILED"; fi
exit $FAILED
