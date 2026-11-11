import Verifier.Models.Vault

/-!
# Witness: ghost funds with no failure at all (`noreturn-vulnerable`)

The hook succeeds but returns no value. The token cannot parse the result of the chain as a
number, so the reference `ft_resolve_transfer` treats the whole amount as unused and refunds it.
The vulnerable vault has already credited the ledger. No receipt fails; the adversary is `.none`.
-/

namespace NearAsync.Vault.Witness
open NearAsync NearAsync.Vault

def noReturnVulnerable : Config := { depositFixed := false, hookReturns := .unit }
def noReturnFixed : Config := { hookReturns := .unit }

def noReturnTrace : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0, .run 1,
    .run 3,     -- hook succeeds, returns nothing
    .run 2 ]    -- token: result is not a number ⇒ unused = 100 ⇒ refund

theorem no_return_insolvent :
    ((run (system noReturnVulnerable .none) init noReturnTrace).map fun w =>
      (solvent w, w.app.ledger.total, w.app.ft.get .vault)) = some (false, 200, 100) := by
  decide

/-- Fixed vault, same hook: `after_notify` returns its own "0", so the deposit is credited
and nothing is refunded. -/
def noReturnFixedTrace : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0, .run 1, .run 3, .run 4, .run 2 ]

theorem no_return_fixed_credits :
    ((run (system noReturnFixed .none) init noReturnFixedTrace).map fun w =>
      (accounting w, w.app.ledger.get .eve, w.app.ft.get .vault)) = some (true, 100, 200) := by
  decide

end NearAsync.Vault.Witness
