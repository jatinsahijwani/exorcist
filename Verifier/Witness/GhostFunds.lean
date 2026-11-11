import Verifier.Models.Vault

/-!
# Witness: ghost funds through a failed notification (`deposit-vulnerable`)

The trace is the shortest one found by `exorcist check deposit-vulnerable`. Every theorem re-runs
it through the semantics and is checked by the Lean kernel with `decide` (no `native_decide`).

Receipt ids: 0 eve's `ft_transfer_call`; 1 `vault.ft_on_transfer`; 2 `token.ft_resolve_transfer`;
3 `hook.on_deposit`; 5.. eve's withdraw and its receipts.
-/

namespace NearAsync.Vault.Witness
open NearAsync NearAsync.Vault

def vulnerable : Config := { depositFixed := false }
def fixedCfg : Config := {}

def ghostTrace : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0,     -- token moves 100 eve → vault, schedules ft_on_transfer, then ft_resolve_transfer
    .run 1,     -- vault credits eve 100, returns the notification promise
    .fail 3,    -- eve's own hook panics, so the chain ft_on_transfer returned has failed
    .run 2 ]    -- token sees Failed ⇒ unused = 100 ⇒ refunds 100 vault → eve

theorem ghost_funds_insolvent :
    ((run (system vulnerable .attackerCode) init ghostTrace).map solvent) = some false := by decide

theorem ghost_funds_numbers :
    ((run (system vulnerable .attackerCode) init ghostTrace).map fun w =>
      (w.app.ledger.total, w.app.ft.get .vault, w.app.ft.get .eve)) = some (200, 100, 100) := by
  decide

/-- Then eve withdraws the ghost credit: she ends with 200 tokens, the vault is empty, and
alice's ledger still says 100. -/
def theftTrace : Tr := ghostTrace ++ [ .submit .eve .vault (.withdraw 100) 0, .run 5, .run 6, .run 7 ]

theorem ghost_funds_theft :
    ((run (system vulnerable .attackerCode) init theftTrace).map fun w =>
      (w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .alice)) = some (200, 0, 100) := by
  decide

/-- The same attack against the fixed vault. Ids differ: 3 `hook.on_deposit`, 4 `vault.after_notify`. -/
def fixedAttempt : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0, .run 1,
    .fail 3,    -- eve's hook panics
    .run 4,     -- after_notify sees Failed: credits nothing, reports 100 unused
    .run 2,     -- token refunds 100 to eve
    .submit .eve .vault (.withdraw 100) 0,
    .run 6 ]    -- withdraw panics: eve's ledger balance is 0

theorem fixed_attack_fails :
    ((run (system fixedCfg .attackerCode) init fixedAttempt).map fun w =>
      (accounting w, w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .eve)) =
      some (true, 100, 100, 0) := by
  decide

end NearAsync.Vault.Witness
