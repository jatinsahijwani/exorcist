import Verifier.Models.All
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
  if !solvent w then "insolvent" else if !noStuck w then "funds_stuck" else "property_violated"

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
def witnessSource (m : Model) (t : Tr) (_final : W) : String :=
  let steps := ",\n    ".intercalate (t.map leanStep)
  let M := m.leanName
  s!"import {m.leanModule}\n\n" ++
  s!"/-! Generated by `exorcist check {m.name}`. The kernel re-runs the trace through the\n" ++
  s!"semantics and checks the final state violates the model's property (`decide`, no native code). -/\n\n" ++
  s!"namespace NearAsync.Vault.Generated\nopen NearAsync NearAsync.Vault\n\n" ++
  s!"def trace : Tr :=\n  [ {steps} ]\n\n" ++
  s!"theorem {m.name.replace "-" "_"}_violation :\n" ++
  s!"    ((run ({M}).sys ({M}).init trace).map ({M}).prop) = some false := by\n  decide\n\n" ++
  s!"end NearAsync.Vault.Generated\n"

end NearAsync.Vault

/-! ## Transaction-level replay (for the sandbox)

The sandbox cannot schedule individual receipts or fail one on demand. So a trace is replayed
per transaction: each transaction runs to completion, with failures injected by kind
(`hook.on_deposit` → the hook is put in panic mode; `token.ft_transfer` → the receiver
unregisters from the token first). Lean computes the expected outcome with a deterministic
scheduler: always the oldest ready receipt, failing it iff it is an injected kind. -/

namespace NearAsync.Vault

abbrev Inject := List (Acct × String)

def injected (inj : Inject) (r : Receipt Acct (Call Acct)) : Bool :=
  match r.action with
  | .call c _ => inj.contains (r.recv, methodName c)
  | .refund _ => false

/-- Run all pending receipts to completion (oldest ready first). Records receipt outcomes. -/
def settle (cfg : Config) (inj : Inject) : Nat → W → List (Acct × String × String) → W × List (Acct × String × String)
  | 0, w, log => (w, log.reverse)
  | fuel + 1, w, log =>
    let sys : System (St Acct) Acct (Call Acct) := { dispatch := dispatch cfg, canFail := injected inj }
    match w.pending.find? (fun r => (readiness w r).isSome) with
    | none => (w, log.reverse)
    | some r =>
      let forced := injected inj r
      let st : Step Acct (Call Acct) := if forced then .fail r.id else .run r.id
      match step sys w st with
      | none => (w, log.reverse)
      | some w' =>
        let entry := match r.action with
          | .call c _ =>
            let failed := lookupResult w'.results r.id == some PResult.failed
            [(r.recv, methodName c, if failed then "failed" else "ok")]
          | .refund _ => []
        settle cfg inj fuel w' (entry ++ log)

/-- Injections per transaction, computed by replaying the trace and looking up failed receipts. -/
def injectionsOf (sys : System (St Acct) Acct (Call Acct)) (w0 : W) (t : Tr) : List Inject :=
  go w0 t [] 0 []
where
  go (w : W) : Tr → List (Nat × Nat) → Nat → List Inject → List Inject
    | [], _, _, acc => acc
    | s :: rest, txOf, ntx, acc =>
      match step sys w s with
      | none => acc
      | some w' =>
        let fresh := (List.range (w'.nextId - w.nextId)).map (w.nextId + ·)
        match s with
        | .submit .. =>
          go w' rest (fresh.map (·, ntx) ++ txOf) (ntx + 1) (acc ++ [[]])
        | .run rid =>
          let tx := ((txOf.find? (·.1 == rid)).map (·.2)).getD 0
          go w' rest (fresh.map (·, tx) ++ txOf) ntx acc
        | .fail rid =>
          let tx := ((txOf.find? (·.1 == rid)).map (·.2)).getD 0
          let acc' := match findPending w.pending rid with
            | some { recv, action := .call c _, .. } =>
              acc.zipIdx.map fun (inj, i) => if i == tx then inj ++ [(recv, methodName c)] else inj
            | _ => acc
          go w' rest (fresh.map (·, tx) ++ txOf) ntx acc'

def submitsOf (t : Tr) : List (Acct × Acct × Call Acct × Nat) :=
  t.filterMap fun s => match s with
    | .submit sg rv c d => some (sg, rv, c, d)
    | _ => none

def vaultWasm (cfg : Config) : String :=
  if !cfg.depositFixed then "vault_deposit_vulnerable.wasm"
  else if !cfg.withdrawFixed then "vault_withdraw_vulnerable.wasm"
  else "vault_fixed.wasm"

def hookMode (cfg : Config) : String :=
  match cfg.hookReturns with | .unit => "none" | .nat _ => "ok"

/-- Replay the transactions of trace `t` (found under `cfgFrom`) against configuration `cfg`. -/
def replayJson (cfg : Config) (txs : List (Acct × Acct × Call Acct × Nat)) (injs : List Inject) (w0 : W := init) : String × W :=
  let step1 (acc : List String × W) (p : (Acct × Acct × Call Acct × Nat) × Inject) : List String × W :=
    let (js, w) := acc
    let ((sg, rv, c, d), inj) := p
    let sys : System (St Acct) Acct (Call Acct) := { dispatch := dispatch cfg, canFail := injected inj }
    match step sys w (.submit sg rv c d) with
    | none => (js, w)
    | some w1 =>
      let (w2, log) := settle cfg inj 100 w1 []
      let j := jObj [ ("signer", jStr sg.name), ("receiver", jStr rv.name), ("method", jStr (methodName c)),
                      ("args", jCallArgs c), ("deposit_yocto", toString d),
                      ("inject", jArr (inj.map fun (a, m) => jObj [("receiver", jStr a.name), ("method", jStr m)])),
                      ("receipts", jArr (log.map fun (a, m, o) =>
                          jObj [("receiver", jStr a.name), ("method", jStr m), ("outcome", jStr o)])),
                      ("state_after", jState w2) ]
      (js ++ [j], w2)
  let (js, wEnd) := (txs.zip injs).foldl step1 ([], w0)
  (jObj [ ("vault_wasm", jStr (vaultWasm cfg)), ("hook_mode", jStr (hookMode cfg)),
          ("txs", jArr js) ], wEnd)


/-! ## Re-running another model's attack

Used by `exorcist check <fixed> --attack-from <vulnerable>`: the attack the explorer found on the
vulnerable model, re-run step by step on this model. Receipts are matched by receiver and method,
because receipt ids differ when the contract emits different promises. -/

inductive AttackMove where
  | submit (s : Step Acct (Call Acct))
  | exec (recv : Acct) (meth : String) (forced : Bool)

def callKey (r : Receipt Acct (Call Acct)) : Option (Acct × String) :=
  match r.action with
  | .call c _ => some (r.recv, methodName c)
  | .refund _ => none

/-- The attack as moves that do not depend on receipt ids. -/
def attackMoves (sys : System (St Acct) Acct (Call Acct)) : W → Tr → List AttackMove
  | _, [] => []
  | w, s :: t =>
    let mv : Option AttackMove := match s with
      | .submit .. => some (.submit s)
      | .run rid | .fail rid =>
        match findPending w.pending rid with
        | some r => (callKey r).map fun (rv, m) => .exec rv m (match s with | .fail _ => true | _ => false)
        | none => none
    match step sys w s with
    | none => []
    | some w' => mv.toList ++ attackMoves sys w' t

/-- Same transactions in the same order; each receipt the attack ran or failed is run or failed
again when it exists here. A receipt that is pending but not yet ready waits for the receipts
before it, which then run normally; a receipt that never exists here is skipped. At the end,
everything still in flight runs to completion. -/
def adaptAttack (sys : System (St Acct) Acct (Call Acct)) : Nat → W → List AttackMove → Tr → Tr
  | 0, _, _, acc => acc.reverse
  | fuel + 1, w, moves, acc =>
    let ready := w.pending.filter fun r => (readiness w r).isSome
    let runFirstReady (k : W → Tr → Tr) : Tr :=
      match ready.head? with
      | none => acc.reverse
      | some r => match step sys w (.run r.id) with
        | some w' => k w' (.run r.id :: acc)
        | none => acc.reverse
    match moves with
    | [] => runFirstReady fun w' acc' => adaptAttack sys fuel w' [] acc'
    | .submit s :: ms =>
      match step sys w s with
      | some w' => adaptAttack sys fuel w' ms (s :: acc)
      | none => adaptAttack sys fuel w ms acc
    | .exec rv meth forced :: ms =>
      match ready.find? (callKey · == some (rv, meth)) with
      | some r =>
        let s : Step Acct (Call Acct) := if forced then .fail r.id else .run r.id
        match step sys w s with
        | some w' => adaptAttack sys fuel w' ms (s :: acc)
        | none => adaptAttack sys fuel w ms acc
      | none =>
        if w.pending.any (callKey · == some (rv, meth)) then
          runFirstReady fun w' acc' => adaptAttack sys fuel w' moves acc'
        else adaptAttack sys fuel w ms acc

end NearAsync.Vault
