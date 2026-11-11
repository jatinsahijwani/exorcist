import Verifier.Models.Vault

/-!
# The fixes are not vacuous

A contract that rejects everything is trivially "safe". These theorems show that every fixed
configuration still does its job with no forced failures: an honest deposit through a succeeding
hook is credited, and a withdraw pays out real tokens. Checked by the kernel with `decide`.
-/

namespace NearAsync.Vault.Witness
open NearAsync NearAsync.Vault

/-- eve deposits 100 with a notification; the hook succeeds; then she withdraws 100.
Fixed vault ids: 3 `hook.on_deposit`, 4 `vault.after_notify`, 5 withdraw, 6 `ft_transfer`,
7 `after_withdraw`. -/
def honestTrace : Tr :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0, .run 1, .run 3, .run 4, .run 2 ]

def honestRoundTrip : Tr :=
  honestTrace ++ [ .submit .eve .vault (.withdraw 100) 0, .run 5, .run 6, .run 7 ]

/-- Every fixed configuration (hook returns "0", or nothing). -/
def fixedConfigs : List Config := [{}, { hookReturns := .unit }]

theorem fixed_deposit_is_credited :
    fixedConfigs.all (fun cfg =>
      ((run (system cfg .none) init honestTrace).map fun w =>
        accounting w && quiescent w && w.app.ledger.get .eve == 100 && w.app.ft.get .eve == 0 &&
        w.app.ft.get .vault == 200) == some true) = true := by
  decide

theorem fixed_withdraw_pays_out :
    fixedConfigs.all (fun cfg =>
      ((run (system cfg .none) init honestRoundTrip).map fun w =>
        accounting w && quiescent w && w.app.ledger.get .eve == 0 && w.app.ft.get .eve == 100 &&
        w.app.ft.get .vault == 100) == some true) = true := by
  decide

/-- alice withdraws her existing 100. -/
theorem fixed_alice_withdraw_pays_out :
    fixedConfigs.all (fun cfg =>
      ((run (system cfg .none) init [ .submit .alice .vault (.withdraw 100) 0, .run 0, .run 1, .run 2 ]).map
        fun w => accounting w && quiescent w && w.app.ft.get .alice == 100 &&
                 w.app.ledger.get .alice == 0) == some true) = true := by
  decide

end NearAsync.Vault.Witness
