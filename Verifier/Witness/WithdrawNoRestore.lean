import Verifier.Models.Vault

/-!
# Witness: withdraw without restore (`withdraw-vulnerable`)

alice withdraws 100. The vault debits her ledger and calls `ft_transfer`; that receipt fails
(in practice: too little gas, or alice is not registered with the token). The vulnerable
callback does not restore the ledger: the vault keeps 100 tokens that no ledger entry accounts for.
Receipt ids: 0 withdraw; 1 `token.ft_transfer`; 2 `vault.after_withdraw`; 3 refund of the 1 yocto.
-/

namespace NearAsync.Vault.Witness
open NearAsync NearAsync.Vault

def withdrawVulnerable : Config := { withdrawFixed := false }

def withdrawTrace : Tr :=
  [ .submit .alice .vault (.withdraw 100) 0, .run 0, .fail 1, .run 2, .run 3 ]

theorem withdraw_funds_stuck :
    ((run (system withdrawVulnerable .nonCallback) init withdrawTrace).map fun w =>
      (noStuck w, quiescent w, w.app.ledger.get .alice, w.app.ft.get .alice, w.app.ft.get .vault)) =
      some (false, true, 0, 0, 100) := by
  decide

theorem withdraw_fixed_restores :
    ((run (system {} .nonCallback) init withdrawTrace).map fun w =>
      (accounting w, w.app.ledger.get .alice, w.app.ft.get .vault)) = some (true, 100, 100) := by
  decide

end NearAsync.Vault.Witness
