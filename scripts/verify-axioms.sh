#!/usr/bin/env bash
# Print `#print axioms` for every headline theorem and fail if any depends on sorryAx (a `sorry`)
# or Lean.ofReduceBool (`native_decide`).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
F=$(mktemp -t axioms).lean
{
  echo "import Verifier"
  for t in Proof.fixed_vault_solvent_forever Proof.fixed_vault_no_stuck_funds Proof.concrete_fixed_solvent_from \
           Proof.concrete_no_stuck_from Witness.ghost_funds_insolvent Witness.ghost_funds_theft Witness.fixed_attack_fails \
           Witness.no_return_insolvent Witness.withdraw_funds_stuck Witness.withdraw_fixed_restores \
           Witness.fixed_deposit_is_credited Witness.fixed_withdraw_pays_out Witness.incident_repeated_theft \
           Witness.incident_repeated_fixed_safe; do
    echo "#print axioms NearAsync.Vault.$t"
  done
} > "$F"
out=$(lake env lean "$F"); rm -f "$F"
echo "$out"
if echo "$out" | grep -qE "sorryAx|ofReduceBool"; then echo "FAIL: sorry or native_decide found"; exit 1; fi
echo "OK: $(echo "$out" | grep -c "depends on axioms") theorems, standard axioms only (no sorryAx, no Lean.ofReduceBool)"
