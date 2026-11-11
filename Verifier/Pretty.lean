import Verifier.Models.Deposit
import Verifier.Explore

/-! Human-readable rendering of traces for the deposit models. -/

namespace NearAsync.Deposit

open NearAsync

def showMsg : Msg Acct → String
  | .plain => "\"\""
  | .notify h => s!"\"notify {h}\""

def showCall : Call Acct → String
  | .ft_transfer r a => s!"ft_transfer({r}, {a})"
  | .ft_transfer_call r a m => s!"ft_transfer_call({r}, {a}, {showMsg m})"
  | .ft_resolve_transfer s r a => s!"ft_resolve_transfer({s}, {r}, {a})"
  | .ft_on_transfer s a m => s!"ft_on_transfer({s}, {a}, {showMsg m})"
  | .on_deposit w a => s!"on_deposit({w}, {a})"
  | .after_notify w a => s!"after_notify({w}, {a})"
  | .withdraw a => s!"withdraw({a})"
  | .after_withdraw w a => s!"after_withdraw({w}, {a})"

def showReceipt (r : Receipt Acct (Call Acct)) : String :=
  match r.action with
  | .call c _ => s!"{r.recv}.{showCall c}"
  | .refund a => s!"refund {a} yoctoNEAR → {r.recv}"

def showResult : Option PResult → String
  | some (.ok .unit) => "ok"
  | some (.ok (.nat n)) => s!"ok, returns {n}"
  | some .failed => "FAILED"
  | none => "pending (returned a promise)"

def snapshot (w : World St Acct (Call Acct)) : String :=
  s!"ledger: alice={w.app.ledger.get .alice} eve={w.app.ledger.get .eve} (total {w.app.ledger.total}) | " ++
  s!"tokens: vault={w.app.ft.get .vault} alice={w.app.ft.get .alice} eve={w.app.ft.get .eve}" ++
  (if solvent w then "" else "   ⚠ INSOLVENT")

def describeStep (w w' : World St Acct (Call Acct)) : Step Acct (Call Acct) → String
  | .submit sg rv c d => s!"{sg} sends tx: {rv}.{showCall c}" ++ (if d > 0 then s!" (+{d} yocto)" else "")
  | .run rid => match findPending w.pending rid with
    | some r =>
      let res := match r.action with
        | .refund _ => ""
        | .call _ _ =>
          let out := showResult (lookupResult w'.results rid)
          let panicked := (lookupResult w'.results rid) == some PResult.failed
          s!"  ⇒ {if panicked then "panics (state reverted)" else out}"
      s!"run #{rid} {showReceipt r}{res}"
    | none => s!"run #{rid}"
  | .fail rid => match findPending w.pending rid with
    | some r => s!"FAIL #{rid} {showReceipt r}  ⇒ adversary makes it fail"
    | none => s!"FAIL #{rid}"

/-- Render a trace step by step with the state after each step. -/
def renderTrace (sys : System St Acct (Call Acct)) (w0 : World St Acct (Call Acct))
    (t : List (Step Acct (Call Acct))) : List String :=
  go w0 t 1
where
  go (w : World St Acct (Call Acct)) : List (Step Acct (Call Acct)) → Nat → List String
    | [], _ => []
    | s :: rest, i => match step sys w s with
      | none => [s!"{i}. (step not enabled)"]
      | some w' =>
        s!"{i}. {describeStep w w' s}" :: s!"     {snapshot w'}" :: go w' rest (i + 1)

def showActor (a : Acct) : String := s!".{a}"

/-- Lean source for a step, for the generated witness theorem. -/
def stepLean : Step Acct (Call Acct) → String
  | .submit sg rv c d =>
    let cs := match c with
      | .ft_transfer r a => s!"(.ft_transfer {showActor r} {a})"
      | .ft_transfer_call r a .plain => s!"(.ft_transfer_call {showActor r} {a} .plain)"
      | .ft_transfer_call r a (.notify h) => s!"(.ft_transfer_call {showActor r} {a} (.notify {showActor h}))"
      | .withdraw a => s!"(.withdraw {a})"
      | _ => "(sorry)"
    s!".submit {showActor sg} {showActor rv} {cs} {d}"
  | .run r => s!".run {r}"
  | .fail r => s!".fail {r}"

end NearAsync.Deposit
