import Verifier.Async

/-!
# Bounded explorer

Enumerates every execution of up to `depth` steps: at each point it may submit any unused
transaction from the scenario's menu, run any ready receipt, or (if the adversary may) make a
ready receipt fail. Iterative deepening, so the first violation found is a shortest one.

The search runs as ordinary compiled code. Its answer is not trusted: a found trace is re-checked
by the kernel (`run` + `decide`) in a witness theorem; "no violation up to depth N" is a
bounded result and is labelled as such.
-/

namespace NearAsync

variable {S α C : Type} [DecidableEq α]

/-- A transaction template: signer, receiver, call, attached deposit. -/
abbrev Tx (α C : Type) := α × α × C × Nat

structure Scenario (S α C : Type) where
  sys : System S α C
  init : World S α C
  menu : List (Tx α C)
  /-- The property every reachable state must satisfy. -/
  ok : World S α C → Bool

/-- All candidate moves from `w`, each with the menu that remains afterwards. -/
def moves (sys : System S α C) (w : World S α C) (menu : List (Tx α C)) :
    List (Step α C × List (Tx α C)) :=
  let submits := menu.zipIdx.map fun ((sg, rv, c, d), i) => (Step.submit sg rv c d, menu.eraseIdx i)
  let execs := w.pending.flatMap fun r =>
    match readiness w r with
    | none => []
    | some _ =>
      match r.action with
      | .refund _ => [(Step.run r.id, menu)]
      | .call _ _ =>
        (Step.run r.id, menu) :: (if sys.canFail r then [(Step.fail r.id, menu)] else [])
  execs ++ submits

structure SearchResult (α C : Type) where
  /-- A shortest violating trace, if one exists within the bound. -/
  trace : Option (List (Step α C))
  /-- Number of states visited (all depths of the iterative deepening). -/
  visited : Nat
  depth : Nat

/-- Depth-limited DFS. Returns a violating trace (in order) and the count of states visited. -/
def dfs (sc : Scenario S α C) : Nat → World S α C → List (Tx α C) → List (Step α C) →
    Option (List (Step α C)) × Nat
  | 0, _, _, _ => (none, 0)
  | d + 1, w, menu, acc =>
    (moves sc.sys w menu).foldl (init := (none, 0)) fun (found, n) (s, menu') =>
      match found with
      | some t => (some t, n)
      | none =>
        match step sc.sys w s with
        | none => (none, n)
        | some w' =>
          if !sc.ok w' then (some (s :: acc).reverse, n + 1)
          else
            let (r, m) := dfs sc d w' menu' (s :: acc)
            (r, n + 1 + m)

/-- Search for a reachable state satisfying `goal` (used for liveness: "honest use still works"). -/
def reach (sys : System S α C) (init : World S α C) (menu : List (Tx α C)) (goal : World S α C → Bool)
    (depth : Nat) : SearchResult α C :=
  explore' { sys, init, menu, ok := fun w => !goal w } depth
where
  explore' (sc : Scenario S α C) (depth : Nat) : SearchResult α C := Id.run do
    let mut visited := 0
    for d in [1:depth+1] do
      let (r, n) := dfs sc d sc.init sc.menu []
      visited := visited + n
      if let some t := r then return { trace := some t, visited, depth := d }
    return { trace := none, visited, depth }

/-- Iterative deepening up to `depth`. -/
def explore (sc : Scenario S α C) (depth : Nat) : SearchResult α C :=
  go 1 0
where
  go (d visited : Nat) : SearchResult α C :=
    if _h : d ≤ depth then
      let (r, n) := dfs sc d sc.init sc.menu []
      match r with
      | some t => { trace := some t, visited := visited + n, depth := d }
      | none => go (d + 1) (visited + n)
    else { trace := none, visited := visited, depth := depth }
  termination_by depth + 1 - d

end NearAsync
