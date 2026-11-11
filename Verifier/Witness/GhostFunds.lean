import Verifier.Models.Deposit

/-!
# Kernel-checked witness: ghost funds in the vulnerable vault

`ghostTrace` is the shortest violating trace found by the bounded explorer
(`nearcheck check deposit-vulnerable`). Each theorem below re-runs the trace through the
semantics and is checked by the Lean kernel with `decide` (no `native_decide`).

Receipt ids: 0 = eve's `ft_transfer_call`, 1 = `vault.ft_on_transfer`, 2 = `token.ft_resolve_transfer`,
3 = `hook.on_deposit` (the notification), 5.. = eve's withdraw and its receipts.
-/

namespace NearAsync.Deposit

open NearAsync

/-- Found by the explorer: eve deposits 100 with a notification, makes her own hook fail. -/
def ghostTrace : List (Step Acct (Call Acct)) :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0,     -- token moves 100 eve → vault, schedules ft_on_transfer + ft_resolve_transfer
    .run 1,     -- vault credits eve 100 in its ledger, returns the notification promise
    .fail 3,    -- eve's hook panics: the promise chain ft_on_transfer returned has failed
    .run 2 ]    -- token sees Failed ⇒ unused = 100 ⇒ refunds 100 vault → eve

/-- …then eve withdraws the ghost credit as real tokens (alice's tokens). -/
def theftTrace : List (Step Acct (Call Acct)) :=
  ghostTrace ++ [ .submit .eve .vault (.withdraw 100) 0, .run 5, .run 6, .run 7 ]

abbrev vulnSys := system .vulnerable .attackerCode

/-- Bounded result made concrete: the vulnerable vault becomes insolvent after 5 steps. -/
theorem ghost_funds_insolvent :
    ((run vulnSys init ghostTrace).map solvent) = some false := by decide

/-- After the 5 steps: the ledger owes 200 but the vault holds 100. -/
theorem ghost_funds_numbers :
    ((run vulnSys init ghostTrace).map fun w =>
      (w.app.ledger.total, w.app.ft.get .vault, w.app.ft.get .eve)) = some (200, 100, 100) := by
  decide

/-- Full attack: eve started with 100 tokens and ends with 200; the vault is empty while
alice's ledger still says 100. -/
theorem ghost_funds_theft :
    ((run vulnSys init theftTrace).map fun w =>
      (w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .alice)) = some (200, 0, 100) := by
  decide

/-! ## The same attack against the fixed vault

Receipt ids differ because the fixed `ft_on_transfer` creates two promises:
3 = `hook.on_deposit`, 4 = `vault.after_notify` (the token's resolve now waits on 4). -/

def fixedAttempt : List (Step Acct (Call Acct)) :=
  [ .submit .eve .token (.ft_transfer_call .vault 100 (.notify .hook)) 1,
    .run 0, .run 1,
    .fail 3,    -- eve's hook panics
    .run 4,     -- after_notify sees Failed: credits nothing, reports 100 unused
    .run 2,     -- token refunds 100 to eve
    .submit .eve .vault (.withdraw 100) 0,
    .run 6 ]    -- withdraw panics: eve's ledger balance is 0

abbrev fixedSys := system .fixed .attackerCode

theorem fixed_attack_fails :
    ((run fixedSys init fixedAttempt).map fun w =>
      (solvent w, w.app.ft.get .eve, w.app.ft.get .vault, w.app.ledger.get .eve)) =
      some (true, 100, 100, 0) := by
  decide

end NearAsync.Deposit
