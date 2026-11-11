import Verifier.Models.Registry
import Verifier.Explore

/-! Human-readable and JSON rendering of traces, and generation of witness theorems. -/

namespace NearAsync.Vault

open NearAsync

def showMsg : Msg Acct → String
  | .plain => "\"\""
  | .notify h => s!"\"notify {h}\""

def methodName : Call Acct → String
  | .ft_transfer .. => "ft_transfer"
  | .ft_transfer_call .. => "ft_transfer_call"
  | .ft_resolve_transfer .. => "ft_resolve_transfer"
  | .ft_on_transfer .. => "ft_on_transfer"
  | .on_deposit .. => "on_deposit"
  | .after_notify .. => "after_notify"
  | .withdraw .. => "withdraw"
  | .after_withdraw .. => "after_withdraw"

def showCall : Call Acct → String
  | .ft_transfer r a => s!"ft_transfer({r}, {a})"
  | .ft_transfer_call r a m => s!"ft_transfer_call({r}, {a}, {showMsg m})"
  | .ft_resolve_transfer s r a => s!"ft_resolve_transfer({s}, {r}, {a})"
  | .ft_on_transfer s a m => s!"ft_on_transfer({s}, {a}, {showMsg m})"
  | .on_deposit w a => s!"on_deposit({w}, {a})"
  | .after_notify w a => s!"after_notify({w}, {a})"
  | .withdraw a => s!"withdraw({a})"
  | .after_withdraw w a => s!"after_withdraw({w}, {a})"

def jStr (s : String) : String := "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def jObj (kvs : List (String × String)) : String :=
  "{" ++ ", ".intercalate (kvs.map fun (k, v) => jStr k ++ ": " ++ v) ++ "}"

def jArr (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def jMsg : Msg Acct → String
  | .plain => jStr ""
  | .notify h => jStr s!"notify {h}"

def jCallArgs : Call Acct → String
  | .ft_transfer r a => jObj [("receiver_id", jStr r.name), ("amount", toString a)]
  | .ft_transfer_call r a m => jObj [("receiver_id", jStr r.name), ("amount", toString a), ("msg", jMsg m)]
  | .ft_resolve_transfer s r a => jObj [("sender_id", jStr s.name), ("receiver_id", jStr r.name), ("amount", toString a)]
  | .ft_on_transfer s a m => jObj [("sender_id", jStr s.name), ("amount", toString a), ("msg", jMsg m)]
  | .on_deposit w a => jObj [("who", jStr w.name), ("amount", toString a)]
  | .after_notify w a => jObj [("who", jStr w.name), ("amount", toString a)]
  | .withdraw a => jObj [("amount", toString a)]
  | .after_withdraw w a => jObj [("who", jStr w.name), ("amount", toString a)]

def holders : List Acct := [.alice, .eve, .vault, .hook]

def jState (w : W) : String :=
  jObj [ ("ft", jObj (holders.map fun a => (a.name, toString (w.app.ft.get a)))),
         ("ledger", jObj ([Acct.alice, .eve].map fun a => (a.name, toString (w.app.ledger.get a)))),
         ("ledger_total", toString w.app.ledger.total),
         ("solvent", toString (solvent w)),
         ("no_stuck_funds", toString (noStuck w)),
         ("quiescent", toString (quiescent w)) ]

def snapshot (w : W) : String :=
  s!"ledger: alice={w.app.ledger.get .alice} eve={w.app.ledger.get .eve} (total {w.app.ledger.total}) | " ++
  s!"tokens: vault={w.app.ft.get .vault} alice={w.app.ft.get .alice} eve={w.app.ft.get .eve}" ++
  (if !solvent w then "   ⚠ INSOLVENT (ledger > tokens held)"
   else if !noStuck w then "   ⚠ FUNDS STUCK (tokens held > ledger, nothing in flight)" else "")

def outcomeOf (w' : W) (rid : Nat) : String :=
  match lookupResult w'.results rid with
  | some (.ok .unit) => "ok"
  | some (.ok (.nat n)) => s!"ok:{n}"
  | some .failed => "failed"
  | none => "promise"

def showOutcome (w' : W) (rid : Nat) : String :=
  match lookupResult w'.results rid with
  | some (.ok .unit) => "ok (no value)"
  | some (.ok (.nat n)) => s!"ok, returns {n}"
  | some .failed => "panics, its state changes are discarded"
  | none => "returns a promise"

/-- What a resolve step did to balances, for readability. -/
def resolveNote (w w' : W) (c : Call Acct) : String :=
  match c with
  | .ft_resolve_transfer s r _ =>
    let moved := w.app.ft.get r - w'.app.ft.get r
    if moved > 0 then s!"  — refunds {moved} {r} → {s}" else "  — no refund"
  | _ => ""

structure Row where
  idx : Nat
  tx : Nat
  kind : String
  text : String
  json : String
  after : W

/-- Render a trace. Each step is attributed to the transaction (by order of submission) it belongs to. -/
def rows (sys : System (St Acct) Acct (Call Acct)) (w0 : W) (t : Tr) : List Row :=
  go w0 t 1 [] 0
where
  go (w : W) : Tr → Nat → List (Nat × Nat) → Nat → List Row
    | [], _, _, _ => []
    | s :: rest, i, txOf, ntx =>
      match step sys w s with
      | none => []
      | some w' =>
        let fresh := (List.range (w'.nextId - w.nextId)).map (w.nextId + ·)
        let lookupTx (rid : Nat) : Nat := (txOf.find? (·.1 == rid)).map (·.2) |>.getD 0
        match s with
        | .submit sg rv c d =>
          let tx := ntx + 1
          let txOf' := fresh.map (·, tx) ++ txOf
          let text := s!"{sg} sends tx: {rv}.{showCall c}" ++ (if d > 0 then s!" (+{d} yocto)" else "")
          let j := jObj [("i", toString i), ("tx", toString tx), ("kind", jStr "submit"),
                         ("signer", jStr sg.name), ("receiver", jStr rv.name),
                         ("method", jStr (methodName c)), ("args", jCallArgs c),
                         ("deposit_yocto", toString d), ("receipt_id", toString w.nextId),
                         ("state_after", jState w')]
          { idx := i, tx, kind := "submit", text, json := j, after := w' } :: go w' rest (i + 1) txOf' tx
        | .run rid | .fail rid =>
          let forced := match s with | .fail _ => true | _ => false
          let tx := lookupTx rid
          let txOf' := fresh.map (·, tx) ++ txOf
          match findPending w.pending rid with
          | none => []
          | some r =>
            let (text, j) := match r.action with
              | .refund a =>
                (s!"run #{rid} refund {a} yoctoNEAR → {r.recv}",
                 jObj [("i", toString i), ("tx", toString tx), ("kind", jStr "refund"),
                       ("receipt_id", toString rid), ("receiver", jStr r.recv.name),
                       ("amount_yocto", toString a), ("state_after", jState w')])
              | .call c _ =>
                let head := if forced then s!"FAIL #{rid} {r.recv}.{showCall c}  ⇒ adversary makes it fail"
                  else s!"run #{rid} {r.recv}.{showCall c}  ⇒ {showOutcome w' rid}{resolveNote w w' c}"
                (head,
                 jObj [("i", toString i), ("tx", toString tx), ("kind", jStr (if forced then "fail" else "run")),
                       ("receipt_id", toString rid), ("predecessor", jStr r.pred.name),
                       ("receiver", jStr r.recv.name), ("method", jStr (methodName c)),
                       ("args", jCallArgs c), ("outcome", jStr (outcomeOf w' rid)),
                       ("state_after", jState w')])
            { idx := i, tx, kind := if forced then "fail" else "run", text, json := j, after := w' } ::
              go w' rest (i + 1) txOf' ntx

def renderText (rs : List Row) : List String :=
  rs.flatMap fun r => [s!"{r.idx}. {r.text}", s!"     {snapshot r.after}"]

def violationKind (w : W) : String :=
  if !solvent w then "insolvent" else if !noStuck w then "funds_stuck" else "none"

/-! ## Witness theorem generation -/

def leanActor (a : Acct) : String := s!".{a}"

def leanMsg : Msg Acct → String
  | .plain => ".plain"
  | .notify h => s!"(.notify {leanActor h})"

def leanCall : Call Acct → String
  | .ft_transfer r a => s!"(.ft_transfer {leanActor r} {a})"
  | .ft_transfer_call r a m => s!"(.ft_transfer_call {leanActor r} {a} {leanMsg m})"
  | .ft_resolve_transfer s r a => s!"(.ft_resolve_transfer {leanActor s} {leanActor r} {a})"
  | .ft_on_transfer s a m => s!"(.ft_on_transfer {leanActor s} {a} {leanMsg m})"
  | .on_deposit w a => s!"(.on_deposit {leanActor w} {a})"
  | .after_notify w a => s!"(.after_notify {leanActor w} {a})"
  | .withdraw a => s!"(.withdraw {a})"
  | .after_withdraw w a => s!"(.after_withdraw {leanActor w} {a})"

def leanStep : Step Acct (Call Acct) → String
  | .submit sg rv c d => s!".submit {leanActor sg} {leanActor rv} {leanCall c} {d}"
  | .run r => s!".run {r}"
  | .fail r => s!".fail {r}"

def leanVal : Val → String
  | .unit => ".unit"
  | .nat n => s!"(.nat {n})"

def leanCfg (c : Config) : String :=
  s!"\{ depositFixed := {c.depositFixed}, withdrawFixed := {c.withdrawFixed}, hookReturns := {leanVal c.hookReturns} }"

def leanAdv : Adversary → String
  | .none => ".none" | .attackerCode => ".attackerCode" | .nonCallback => ".nonCallback"
  | .anyReceipt => ".anyReceipt"

/-- A standalone Lean file stating that the trace is enabled and ends in a violation. -/
def witnessSource (m : Model) (t : Tr) (final : W) : String :=
  let steps := ",\n    ".intercalate (t.map leanStep)
  let (prop, nm) := if !solvent final then ("solvent", "insolvent") else ("noStuck", "funds_stuck")
  s!"import Verifier.Models.Vault\n\n" ++
  s!"/-! Generated by `exorcist check {m.name}`. The kernel re-runs the trace through the\n" ++
  s!"semantics and checks the final state violates the invariant (`decide`, no native code). -/\n\n" ++
  s!"namespace NearAsync.Vault.Generated\nopen NearAsync NearAsync.Vault\n\n" ++
  s!"def trace : Tr :=\n  [ {steps} ]\n\n" ++
  s!"theorem {m.name.replace "-" "_"}_{nm} :\n" ++
  s!"    ((run (system {leanCfg m.cfg} {leanAdv m.adv}) init trace).map {prop}) = some false := by\n  decide\n\n" ++
  s!"end NearAsync.Vault.Generated\n"

end NearAsync.Vault
