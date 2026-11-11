import Verifier.Models.Vault

/-! The models `exorcist` knows about. Each is the vault with some switches, an adversary,
and the honest-use goals (liveness) that a fix must still allow. -/

namespace NearAsync.Vault

open NearAsync

structure Goal where
  name : String
  /-- the only transactions allowed while searching for this goal -/
  txs : List (Acct × Acct × Call Acct × Nat)
  holds : W → Bool

structure Model where
  name : String
  pattern : String
  summary : String
  cfg : Config
  adv : Adversary
  /-- `true` if we expect the explorer to find a violation -/
  vulnerable : Bool
  /-- name of the committed proof that covers this model, if any -/
  proof : Option String := none

/-- Honest deposit with a hook that succeeds ends up credited. -/
def goalDepositCredited : Goal :=
  { name := "honest deposit via ft_transfer_call(\"notify hook\"), hook succeeds: eve credited 100, vault holds 200",
    txs := [(.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1)],
    holds := fun w => quiescent w && w.app.ledger.get .eve == 100 && w.app.ft.get .eve == 0 &&
                      w.app.ft.get .vault == 200 }

/-- Withdraw pays out real tokens. -/
def goalWithdrawPays : Goal :=
  { name := "withdraw pays out: alice receives 100 tokens, her ledger goes to 0",
    txs := [(.alice, .vault, .withdraw 100, 0)],
    holds := fun w => quiescent w && w.app.ft.get .alice == 100 && w.app.ledger.get .alice == 0 }

def goals : List Goal := [goalDepositCredited, goalWithdrawPays]

def models : List Model :=
  [ { name := "deposit-vulnerable", pattern := "ghost funds (notify failure)",
      summary := "credits the ledger in ft_on_transfer, then returns the notification promise",
      cfg := { depositFixed := false }, adv := .attackerCode, vulnerable := true },
    { name := "deposit-fixed", pattern := "ghost funds (notify failure)",
      summary := "credits only in the after_notify callback, when the notification succeeded",
      cfg := {}, adv := .attackerCode, vulnerable := false,
      proof := some "NearAsync.Vault.Proof.fixed_vault_solvent_forever" },
    { name := "noreturn-vulnerable", pattern := "ghost funds (hook returns nothing)",
      summary := "same vulnerable vault; the hook succeeds but returns no value",
      cfg := { depositFixed := false, hookReturns := .unit }, adv := .none, vulnerable := true },
    { name := "noreturn-fixed", pattern := "ghost funds (hook returns nothing)",
      summary := "fixed vault with the same hook that returns no value",
      cfg := { hookReturns := .unit }, adv := .none, vulnerable := false,
      proof := some "NearAsync.Vault.Proof.fixed_vault_solvent_forever" },
    { name := "withdraw-vulnerable", pattern := "withdraw without restore",
      summary := "debits the ledger, calls ft_transfer, never restores the ledger if it fails",
      cfg := { withdrawFixed := false }, adv := .nonCallback, vulnerable := true },
    { name := "withdraw-fixed", pattern := "withdraw without restore",
      summary := "restores the ledger in after_withdraw when ft_transfer failed",
      cfg := {}, adv := .nonCallback, vulnerable := false,
      proof := some "NearAsync.Vault.Proof.fixed_vault_no_stuck_funds" } ]

def findModel (n : String) : Option Model := models.find? (·.name == n)

end NearAsync.Vault
