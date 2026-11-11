import Exorcist.Prove

/-!
# `exorcist draft --from <lib.rs> --role token|vault|hook` (EXPERIMENTAL)

Asks a model on NEAR AI Cloud to draft a Lean model of a near-sdk Rust contract in Exorcist's DSL.
The draft is compiled; Lean's errors go back to the model for up to `--rounds` rounds. The result is
written to `drafts/<Name>.lean`. A draft is a starting point for a human, never a trusted model:
`scripts/drafts.sh` compares drafts semantically with the hand-written models.
-/

namespace Exorcist

open Lean

def dslReference : String := "
You write Lean 4 (v4.34.0, no Mathlib) for the Exorcist DSL. Available definitions (already imported):
- `Acct` : `.alice | .eve | .token | .vault | .hook` (token = the NEP-141 token, vault = the receiver contract).
- `Call Acct` constructors (all the methods that exist):
  `.ft_transfer (receiver) (amount)`, `.ft_transfer_call (receiver) (amount) (msg : Msg Acct)`,
  `.ft_resolve_transfer (sender receiver) (amount)`, `.ft_on_transfer (sender) (amount) (msg)`,
  `.on_deposit (who) (amount)`, `.after_notify (who) (amount)`, `.withdraw (amount)`, `.after_withdraw (who) (amount)`.
  `Msg Acct` : `.plain` (msg = \"\") | `.notify (hook : Acct)` (msg = \"notify <account>\").
- `Ctx Acct` fields: `self pred signer : Acct`, `deposit : Nat` (yoctoNEAR attached),
  `input : Option PResult` (in a callback: `some (.ok v)` or `some .failed`; `none` if not a callback).
  `PResult` : `.ok (v : Val) | .failed`; `Val` : `.unit | .nat (n : Nat)` (U128 results are `.nat n`, no value is `.unit`).
- State `St Acct` fields: `ft : Bal Acct` (token balances), `ledger : Bal Acct` (the vault's internal ledger).
  `Bal` ops: `m.get a`, `m.add a n`, `m.sub a n` (truncating), `m.set a v`.
- A method returns `Outcome (St Acct) Acct (Call Acct)`:
  `.panic \"reason\"` (the receipt fails, all its changes are discarded) or
  `.ok newState promises result` with `promises : List (Emit Acct (Call Acct))`, each
  `{ recv := account, call := c, deposit := yocto, after := some i }` (`after := some i` = `.then` of the i-th promise
  created by this same call, `none` = independent), and `result : Ret` = `.val v` or `.promise i` (return promise i).
- Model only storage writes, panics (require!/assert/insufficient balance/predecessor checks), created promises with their
  `.then` structure, and return values. Ignore gas amounts, logs and events.
Output: ONE complete Lean file, nothing else:
```
import Verifier.Models.Registry
namespace NearAsync.Vault.Draft.<NAME>
open NearAsync NearAsync.Vault
def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | ... => ...
  | _ => .panic \"method not found\"
end NearAsync.Vault.Draft.<NAME>
```
"

structure DraftOpts where
  file : String := ""
  role : String := ""
  name : String := ""
  feature : Option String := none
  rounds : Nat := 4
  aiModel : Option String := none
  out : Option String := none

def parseDraft : List String → DraftOpts → Except String DraftOpts
  | [], o => .ok o
  | "--from" :: f :: r, o => parseDraft r { o with file := f }
  | "--role" :: x :: r, o => parseDraft r { o with role := x }
  | "--name" :: x :: r, o => parseDraft r { o with name := x }
  | "--feature" :: x :: r, o => parseDraft r { o with feature := some x }
  | "--rounds" :: n :: r, o => match n.toNat? with
    | some k => parseDraft r { o with rounds := k }
    | none => .error s!"bad --rounds {n}"
  | "--ai-model" :: m :: r, o => parseDraft r { o with aiModel := some m }
  | "--out" :: f :: r, o => parseDraft r { o with out := some f }
  | x :: _, _ => .error s!"unexpected {x}"

def draft (args : List String) : IO UInt32 := do
  let o ← match parseDraft args {} with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  if o.file.isEmpty || !(["token", "vault", "hook"].contains o.role) then
    IO.eprintln "usage: exorcist draft --from <lib.rs> --role token|vault|hook [--name Name] [--feature F] [--rounds N] [--ai-model ID]"
    return 2
  IO.println "EXPERIMENTAL: the draft is written by a language model. A human must review it against the Rust"
  IO.println "              before any result about it is trusted (see docs/DRAFT.md)."
  let some key ← IO.getEnv "NEARAI_API_KEY"
    | do IO.eprintln "draft needs NEARAI_API_KEY (NEAR AI Cloud, https://cloud.near.ai)"; return 2
  let rust ← IO.FS.readFile o.file
  let name := if o.name.isEmpty then identOf' o.role else o.name
  let model ← match ← pickModelId o.aiModel with
    | .ok x => pure x
    | .error e => do IO.eprintln e; return 2
  let featureNote := match o.feature with
    | some f => s!"The crate is compiled WITH cargo feature `{f}` enabled (so `cfg!(feature = \"{f}\")` is true); all other features are off."
    | none => "No cargo features are enabled (every `cfg!(feature = ...)` is false)."
  let roleNote := s!"This contract is deployed at account `.{o.role}`. In `handle`, `ctx.self = .{o.role}`."
  let user := s!"Model this near-sdk Rust contract. {roleNote} {featureNote} Use NAME = {name}.\n\n```rust\n{rust}\n```"
  IO.println s!"drafting {o.file} as `{o.role}` with {model} on {← getBaseUrl} (up to {o.rounds} rounds)"
  let out := o.out.getD s!"drafts/{name}.lean"
  IO.FS.createDirAll ((System.FilePath.mk out).parent.getD ".")
  let mut msgs : List (String × String) := [("system", dslReference), ("user", user)]
  for i in [1:o.rounds+1] do
    let proposal ← match ← chat key model msgs with
      | .ok s => pure (stripFences s)
      | .error e => do IO.eprintln s!"round {i}: {e}"; return 2
    IO.FS.writeFile out proposal
    let bad := ["sorry", "admit", "native_decide", "axiom "].filter fun f => (proposal.splitOn f).length > 1
    let (ok, errs) ← if bad.isEmpty then runLean out else pure (false, s!"forbidden constructs {bad}")
    if ok then
      IO.println s!"round {i}: ✓ the draft compiles: {out}"
      IO.println "next: review it against the Rust; scripts/drafts.sh compares drafts with the hand-written models."
      return 0
    IO.println s!"round {i}: ✗ does not compile yet ({(errs.take 120).toString.replace "\n" " "} …)"
    msgs := msgs ++ [("assistant", proposal), ("user", s!"Lean rejected it:\n{(errs.take 3000).toString}\nSend the corrected complete file.")]
  IO.println s!"no compiling draft after {o.rounds} rounds; last attempt in {out}"
  return 1
where
  identOf' (role : String) : String := role.capitalize

end Exorcist
