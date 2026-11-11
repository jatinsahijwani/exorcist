/-! `exorcist new <name>`: scaffold a user model and register it. See docs/WRITE-A-MODEL.md. -/

namespace Exorcist

def identOf (name : String) : String :=
  let parts := (name.splitOn "-").filter (· ≠ "")
  String.join (parts.map fun p => p.capitalize) |>.toList.filter Char.isAlphanum |> String.mk

def template (name ident : String) : String :=
s!"import Verifier.Models.Registry

/-! Model `{name}` (created by `exorcist new {name}`). Edit `handle`, then:
    lake build exorcist && ./.lake/build/bin/exorcist check {name}
See docs/WRITE-A-MODEL.md. -/

namespace NearAsync.Vault.User.{ident}
open NearAsync NearAsync.Vault

/-- Your contract, deployed at `vault`: takes NEP-141 deposits, pays out withdrawals. -/
def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .ft_on_transfer sender amt _ =>
    if ctx.pred ≠ .token then .panic \"only the token\" else
    .ok \{ s with ledger := s.ledger.add sender amt } [] (.val (.nat 0))   -- credit; 0 unused
  | .withdraw amt =>
    if amt = 0 ∨ s.ledger.get ctx.pred < amt then .panic \"insufficient balance\" else
    .ok \{ s with ledger := s.ledger.sub ctx.pred amt }                    -- debit first
      [ \{ recv := .token, call := .ft_transfer ctx.pred amt, deposit := 1 },
        \{ recv := .vault, call := .after_withdraw ctx.pred amt, after := some 0 } ] (.val .unit)
  | .after_withdraw who amt =>
    if ctx.pred ≠ ctx.self then .panic \"private\" else
    match ctx.input with
    | some .failed => .ok \{ s with ledger := s.ledger.add who amt } [] (.val .unit)  -- restore
    | _ => .ok s [] (.val .unit)
  | _ => .panic \"method not found\"

/-! Below: wiring and scenario. You rarely need to change these. -/

def network (adv : Adversary) : System (St Acct) Acct (Call Acct) :=
  \{ dispatch := fun a => match a with
      | .token => tokenHandle
      | .vault => handle
      | .hook => hookHandle (.nat 0)
      | _ => fun _ _ _ => .panic \"no contract\",
    canFail := canFail adv }

/-- Transactions the explorer may send (each at most once, any order). -/
def txs : List TxT :=
  [ (.eve, .token, .ft_transfer_call .vault 100 .plain, 1),
    (.alice, .vault, .withdraw 100, 0),
    (.alice, .vault, .withdraw 100, 0),
    (.eve, .vault, .withdraw 100, 0) ]

def model : Model :=
  \{ name := \"{name}\", pattern := \"user model\", summary := \"see Verifier/Models/User/{ident}.lean\",
    adv := .nonCallback, vulnerable := false,
    custom := some (network .nonCallback), customHonest := some (network .none),
    leanName := \"NearAsync.Vault.User.{ident}.model\", leanModule := \"Verifier.Models.User.{ident}\",
    menu := txs, sandbox := false,
    -- the property: alice never gets more than she owns, and when nothing is in flight the
    -- ledger is backed by the tokens the vault holds
    prop := fun w => decide (w.app.ft.get .alice ≤ 100) && (!quiescent w || solvent w),
    propText := [\"alice never receives more than her 100, and the ledger is backed whenever nothing is in flight\"],
    goals := [ \{ name := \"alice withdraws her 100\", txs := [(.alice, .vault, .withdraw 100, 0)],
                 holds := fun w => quiescent w && w.app.ft.get .alice == 100 } ] }

end NearAsync.Vault.User.{ident}
"

/-- Create `Verifier/Models/User/<Ident>.lean` and register it in `Verifier/Models/User.lean`. -/
def newModel (name : String) : IO UInt32 := do
  if name.isEmpty || !(name.all fun c => c.isAlphanum || c == '-') then
    IO.eprintln "usage: exorcist new <name>   (letters, digits and '-')"; return 2
  let ident := identOf name
  let file := s!"Verifier/Models/User/{ident}.lean"
  if ← System.FilePath.pathExists file then
    IO.eprintln s!"{file} already exists"; return 2
  let reg := "Verifier/Models/User.lean"
  let src ← IO.FS.readFile reg
  if (src.splitOn s!"User.{ident}.model").length > 1 then
    IO.eprintln s!"{name} is already registered"; return 2
  IO.FS.createDirAll "Verifier/Models/User"
  IO.FS.writeFile file (template name ident)
  let src := src.replace "-- EXORCIST-USER-IMPORTS" s!"import Verifier.Models.User.{ident}\n-- EXORCIST-USER-IMPORTS"
  let src := src.replace "  -- EXORCIST-USER-MODELS" s!"  ++ [NearAsync.Vault.User.{ident}.model]\n  -- EXORCIST-USER-MODELS"
  IO.FS.writeFile reg src
  IO.println s!"created {file} and registered model '{name}' in {reg}"
  IO.println "next:"
  IO.println s!"  lake build exorcist"
  IO.println s!"  ./.lake/build/bin/exorcist check {name}"
  IO.println s!"  ./.lake/build/bin/exorcist prove {name} --bounded 4"
  return 0

end Exorcist
