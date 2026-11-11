import Verifier.Models.Registry
namespace NearAsync.Vault.Draft.Hook
open NearAsync NearAsync.Vault

/-
  The hook's own storage (`owner`, `mode`) cannot be stored in `St Acct`,
  which only has the `ft` and `ledger` fields.

  `set_mode` and `mode` have no `Call Acct` constructor, so they cannot be
  invoked here. The mode is therefore modelled as a fixed deployment
  parameter, `hookMode`. `handleWith` is the general model for any mode.

  `handle` instantiates the "ok" mode. On-chain, the owner can change the
  mode at any time. A verifier that wants that behaviour should also check
  `handleWith .none` and `handleWith .panic`.
-/
inductive HookMode
  | ok     -- returns "0" (a U128 JSON string, i.e. `.nat 0`)
  | none   -- succeeds and returns nothing
  | panic  -- any other mode string: panics with "hook refuses"

def hookMode : HookMode := .ok

def handleWith (mode : HookMode) (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) :
    Outcome (St Acct) Acct (Call Acct) :=
  let _ := ctx
  match c with
  | .on_deposit _who _amount =>
    -- There are no storage writes and no promises.
    match mode with
    | .ok    => .ok s [] (.val (.nat 0))
    | .none  => .ok s [] (.val .unit)
    | .panic => .panic "hook refuses"
  | _ => .panic "method not found"

def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .on_deposit who amount => handleWith hookMode ctx (.on_deposit who amount) s
  | _ => .panic "method not found"

end NearAsync.Vault.Draft.Hook