import Verifier.Models.Registry
import Verifier.Explore
import Verifier.Drafts.Token
import Verifier.Drafts.Hook
import Verifier.Drafts.VaultFixed
import Verifier.Drafts.VaultGhost
import Verifier.Drafts.VaultNoRestore
open NearAsync NearAsync.Vault

/-- A network with some handlers replaced by drafts. -/
def net (tok : Ctx Acct → Call Acct → St Acct → Outcome (St Acct) Acct (Call Acct))
    (vault : Ctx Acct → Call Acct → St Acct → Outcome (St Acct) Acct (Call Acct)) (cfg : Config) (adv : Adversary) :
    System (St Acct) Acct (Call Acct) :=
  { dispatch := fun a => match a with
      | .token => tok | .vault => vault | .hook => hookHandle cfg.hookReturns
      | _ => fun _ _ _ => .panic "no contract",
    canFail := canFail adv }

def verdict (sys : System (St Acct) Acct (Call Acct)) : String :=
  match (explore { sys, init, menu, ok := accounting } 7).trace with
  | some t => s!"violation@{t.length}"
  | none => "clean≤7"

def row (what : String) (hand drafted : System (St Acct) Acct (Call Acct)) : String :=
  let a := verdict hand; let b := verdict drafted
  s!"| {what} | {a} | {b} | {if a == b then "✓ same" else "✗ DIFFERENT"} |"
#eval IO.println (row "vault (fixed build)" (system {} .attackerCode) (net tokenHandle Draft.VaultFixed.handle {} .attackerCode))
#eval IO.println (row "vault (fixed build) (withdraw adversary)" (system {} .nonCallback) (net tokenHandle Draft.VaultFixed.handle {} .nonCallback))
#eval IO.println (row "vault (ghost_funds_bug build)" (system { depositFixed := false } .attackerCode) (net tokenHandle Draft.VaultGhost.handle { depositFixed := false } .attackerCode))
#eval IO.println (row "vault (ghost_funds_bug build) (withdraw adversary)" (system { depositFixed := false } .nonCallback) (net tokenHandle Draft.VaultGhost.handle { depositFixed := false } .nonCallback))
#eval IO.println (row "vault (withdraw_no_restore_bug build)" (system { withdrawFixed := false } .attackerCode) (net tokenHandle Draft.VaultNoRestore.handle { withdrawFixed := false } .attackerCode))
#eval IO.println (row "vault (withdraw_no_restore_bug build) (withdraw adversary)" (system { withdrawFixed := false } .nonCallback) (net tokenHandle Draft.VaultNoRestore.handle { withdrawFixed := false } .nonCallback))
#eval IO.println (row "token, with the vulnerable vault" (system { depositFixed := false } .attackerCode) (net Draft.Token.handle (vaultHandle { depositFixed := false } .token) { depositFixed := false } .attackerCode))
#eval IO.println (row "token, with the fixed vault" (system {} .attackerCode) (net Draft.Token.handle (vaultHandle {} .token) {} .attackerCode))
