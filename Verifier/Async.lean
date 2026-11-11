/-!
# A small model of NEAR asynchronous execution

Everything here is generic in the account type `α`, the call type `C` (method + arguments)
and the application state `S`. Contracts plug in through `System.dispatch`.

Rules modelled (see `docs/SEMANTICS.md` for sources):
* every receipt executes and commits on its own; nothing rolls back across receipts;
* a failing receipt discards only its own state changes and the promises it would have created;
* callbacks always run and see `PromiseResult.failed` when their input failed;
* a method may return a promise (`promise_return`), whose result then becomes its own result;
* the attached deposit of a failed call is refunded to the predecessor by a separate refund receipt;
* receipts that are ready may execute in any order.

All definitions are structurally recursive and computable, so concrete runs can be checked by
the Lean kernel with `decide`.
-/

namespace NearAsync

/-! ## Balances as association lists -/

/-- A balance map. Missing keys mean 0. -/
abbrev Bal (α : Type) := List (α × Nat)

namespace Bal
variable {α : Type} [DecidableEq α]

def get : Bal α → α → Nat
  | [], _ => 0
  | (b, v) :: t, a => if b = a then v else get t a

def set (m : Bal α) (a : α) (v : Nat) : Bal α :=
  (a, v) :: m.filter (fun p => !decide (p.1 = a))

def add (m : Bal α) (a : α) (n : Nat) : Bal α := m.set a (m.get a + n)

/-- Truncated subtraction; callers check sufficiency first. -/
def sub (m : Bal α) (a : α) (n : Nat) : Bal α := m.set a (m.get a - n)

def total : Bal α → Nat
  | [] => 0
  | (_, v) :: t => v + total t

end Bal

/-! ## Values, promise results, calls -/

/-- Return value of a function call. `unit` = no value (does not parse as a number). -/
inductive Val where
  | unit
  | nat (n : Nat)
  deriving DecidableEq, Repr

/-- What a callback sees for the promise it waited on. -/
inductive PResult where
  | ok (v : Val)
  | failed
  deriving DecidableEq, Repr

/-- Execution context of one function-call receipt. -/
structure Ctx (α : Type) where
  self : α
  pred : α
  signer : α
  deposit : Nat
  /-- `some r` iff this receipt was created with `.then` and its input promise produced `r`. -/
  input : Option PResult
  deriving Repr

/-- A promise created by a method. `after = some i` means "`.then` of the i-th promise
emitted by this same call" (i must be smaller than this promise's own index). -/
structure Emit (α C : Type) where
  recv : α
  call : C
  deposit : Nat := 0
  after : Option Nat := none
  deriving Repr

/-- How a method finishes: with a value, or by returning one of its emitted promises. -/
inductive Ret where
  | val (v : Val)
  | promise (idx : Nat)
  deriving Repr

inductive Outcome (S α C : Type) where
  | panic (why : String)
  | ok (s : S) (emits : List (Emit α C)) (ret : Ret)

inductive Action (C : Type) where
  | call (c : C) (deposit : Nat)
  | refund (amount : Nat)
  deriving Repr

structure Receipt (α C : Type) where
  id : Nat
  pred : α
  signer : α
  recv : α
  action : Action C
  /-- Id of the receipt whose result this one waits for (a callback), if any. -/
  waitsOn : Option Nat
  deriving Repr

/-- The contracts deployed on the network, plus the adversary's power to fail receipts. -/
structure System (S α C : Type) where
  dispatch : (recv : α) → Ctx α → C → S → Outcome S α C
  /-- Which call receipts the adversary may force to fail (out of gas / attacker-owned code). -/
  canFail : Receipt α C → Bool

structure World (S α C : Type) where
  app : S
  near : Bal α
  pending : List (Receipt α C)
  results : List (Nat × PResult)
  nextId : Nat

/-- One scheduling decision. -/
inductive Step (α C : Type) where
  /-- A new transaction signed by `signer`, calling `recv` with `deposit` attached. -/
  | submit (signer recv : α) (call : C) (deposit : Nat)
  /-- Execute ready receipt `rid` normally. -/
  | run (rid : Nat)
  /-- Execute ready receipt `rid`, forced to fail (adversary). -/
  | fail (rid : Nat)
  deriving Repr

variable {S α C : Type} [DecidableEq α]

def lookupResult : List (Nat × PResult) → Nat → Option PResult
  | [], _ => none
  | (k, r) :: t, i => if k = i then some r else lookupResult t i

def findPending : List (Receipt α C) → Nat → Option (Receipt α C)
  | [], _ => none
  | r :: t, i => if r.id = i then some r else findPending t i

def removePending (ps : List (Receipt α C)) (i : Nat) : List (Receipt α C) :=
  ps.filter (fun r => !decide (r.id = i))

/-- `some inp` iff the receipt may execute now; `inp` is its callback input. -/
def readiness (w : World S α C) (r : Receipt α C) : Option (Option PResult) :=
  match r.waitsOn with
  | none => some none
  | some d => (lookupResult w.results d).map some

def emitsDeposit : List (Emit α C) → Nat
  | [] => 0
  | e :: t => e.deposit + emitsDeposit t

/-- Every `.then` points to an earlier promise of the same call. -/
def emitsWellFormed (es : List (Emit α C)) : Bool :=
  (es.zipIdx.all fun (e, i) => match e.after with
    | none => true
    | some j => decide (j < i))

/-- Turn the emitted promises of receipt `r` into pending receipts with ids `base, base+1, …`. -/
def mkReceipts (r : Receipt α C) (base : Nat) (es : List (Emit α C)) : List (Receipt α C) :=
  es.zipIdx.map fun (e, i) =>
    { id := base + i, pred := r.recv, signer := r.signer, recv := e.recv,
      action := .call e.call e.deposit, waitsOn := e.after.map (base + ·) }

/-- Receipt `r` failed: dependents receive `failed`; a nonzero deposit goes back to the
predecessor via a refund receipt. State changes of `r` are simply never applied. -/
def failReceipt (w : World S α C) (r : Receipt α C) (deposit : Nat) : World S α C :=
  let rest := removePending w.pending r.id
  let refund : List (Receipt α C) :=
    if deposit = 0 then []
    else [{ id := w.nextId, pred := r.recv, signer := r.signer, recv := r.pred,
            action := .refund deposit, waitsOn := none }]
  { w with pending := rest ++ refund,
           results := (r.id, .failed) :: w.results,
           nextId := w.nextId + 1 }

/-- Execute receipt `r` normally (it must be ready with input `inp`). -/
def runReceipt (sys : System S α C) (w : World S α C) (r : Receipt α C)
    (inp : Option PResult) : World S α C :=
  match r.action with
  | .refund amt =>
    { w with near := w.near.add r.recv amt, pending := removePending w.pending r.id }
  | .call c dep =>
    let near1 := w.near.add r.recv dep
    let ctx : Ctx α := { self := r.recv, pred := r.pred, signer := r.signer,
                         deposit := dep, input := inp }
    match sys.dispatch r.recv ctx c w.app with
    | .panic _ => failReceipt w r dep
    | .ok s es ret =>
      let need := emitsDeposit es
      if near1.get r.recv < need || !emitsWellFormed es then failReceipt w r dep else
      let base := w.nextId
      let newRs := mkReceipts r base es
      let rest := removePending w.pending r.id
      let w' : World S α C :=
        { app := s, near := near1.sub r.recv need, pending := rest,
          results := w.results, nextId := base + es.length }
      match ret with
      | .val v => { w' with pending := rest ++ newRs, results := (r.id, .ok v) :: w.results }
      | .promise idx =>
        if idx < es.length then
          -- promise_return: whoever waited on `r` now waits on the returned promise
          let redirected := rest.map fun q =>
            if q.waitsOn = some r.id then { q with waitsOn := some (base + idx) } else q
          { w' with pending := redirected ++ newRs }
        else failReceipt w r dep

/-- One step of the network. `none` means the step is not enabled in `w`. -/
def step (sys : System S α C) (w : World S α C) : Step α C → Option (World S α C)
  | .submit signer recv c dep =>
    if w.near.get signer < dep then none else
    some { w with near := w.near.sub signer dep,
                  pending := w.pending ++ [{ id := w.nextId, pred := signer, signer := signer,
                                             recv := recv, action := .call c dep, waitsOn := none }],
                  nextId := w.nextId + 1 }
  | .run rid => do
    let r ← findPending w.pending rid
    let inp ← readiness w r
    pure (runReceipt sys w r inp)
  | .fail rid => do
    let r ← findPending w.pending rid
    let _ ← readiness w r
    match r.action with
    | .refund _ => none
    | .call _ dep => if sys.canFail r then some (failReceipt w r dep) else none

/-- Run a whole trace; `none` if some step is not enabled. -/
def run (sys : System S α C) : World S α C → List (Step α C) → Option (World S α C)
  | w, [] => some w
  | w, s :: t => match step sys w s with
    | none => none
    | some w' => run sys w' t

end NearAsync
