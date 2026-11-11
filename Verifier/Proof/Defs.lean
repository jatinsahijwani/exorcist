import Verifier.Models.Vault
import Verifier.Proof.Lemmas

/-!
# Definitions for the unbounded proofs

The network for the proofs is fully general:
* any account type `α`, token at `T`, vault at `V` (`T ≠ V`);
* arbitrary code `other a` on every other account (the adversary's contracts, the hook, …),
  which may emit any calls but cannot write the token's or the vault's storage (`Frame`);
* any `canFail` predicate (the adversary may fail any receipt she likes);
* transactions with any call, any arguments, any amounts, from any account except `T` and `V`
  (nobody holds the contracts' keys).
-/

set_option linter.unusedSectionVars false

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α]

abbrev Handler (α : Type) := Ctx α → Call α → St α → Outcome (St α) α (Call α)

/-- Token at `T`, vault at `V`, arbitrary code elsewhere. -/
def gsys (cfg : Config) (T V : α) (other : α → Handler α) (canFail : Receipt α (Call α) → Bool) :
    System (St α) α (Call α) :=
  { dispatch := fun a => if a = T then tokenHandle else if a = V then vaultHandle cfg T else other a,
    canFail }

/-- Other contracts cannot write the token's or the vault's storage. -/
def Frame (other : α → Handler α) : Prop :=
  ∀ a ctx c s s' es ret, other a ctx c s = .ok s' es ret → s' = s

abbrev GW (α : Type) := World (St α) α (Call α)
abbrev GR (α : Type) := Receipt α (Call α)

variable (T V : α)

/-- A pending `token.ft_resolve_transfer(_, V, a)` created by the token: may still refund up to `a`. -/
def resAmt (q : GR α) : Option Nat :=
  match q.action with
  | .call (.ft_resolve_transfer _ rcv a) _ => if q.recv = T ∧ q.pred = T ∧ rcv = V then some a else none
  | _ => none

/-- A pending `vault.after_withdraw(_, a)` created by the vault: may still restore `a`. -/
def awAmt (q : GR α) : Option Nat :=
  match q.action with
  | .call (.after_withdraw _ a) _ => if q.recv = V ∧ q.pred = V then some a else none
  | _ => none

/-- In-flight deposit steps that may credit `a` to the ledger. -/
def depSrc (q : GR α) : Option Nat :=
  match q.action with
  | .call (.ft_on_transfer _ a _) _ => if q.recv = V ∧ q.pred = T then some a else none
  | .call (.after_notify _ a) _ => if q.recv = V ∧ q.pred = V then some a else none
  | _ => none

/-- The vault's own in-flight `ft_transfer` of `a`. -/
def wdSrc (q : GR α) : Option Nat :=
  match q.action with
  | .call (.ft_transfer _ a) _ => if q.recv = T ∧ q.pred = V then some a else none
  | _ => none

/-- What `ft_resolve_transfer` treats as unused, given its input. -/
abbrev unusedOf (r : PResult) (a : Nat) : Nat := unusedAmount r a

def resPot (res : List (Nat × PResult)) (d : Option Nat) (a : Nat) : Nat :=
  match d with
  | none => 0
  | some d => match lookupResult res d with
    | none => a
    | some r => unusedOf r a

def awPot (res : List (Nat × PResult)) (d : Option Nat) (a : Nat) : Nat :=
  match d with
  | none => 0
  | some d => match lookupResult res d with
    | none => a
    | some (.ok _) => 0
    | some .failed => a

/-- How many of the vault's tokens a pending receipt may still move out of the ledger's backing. -/
def contrib (res : List (Nat × PResult)) (q : GR α) : Nat :=
  match resAmt T V q with
  | some a => resPot res q.waitsOn a
  | none => match awAmt V q with
    | some a => awPot res q.waitsOn a
    | none => 0

def pot (w : GW α) : Nat := (w.pending.map (contrib T V w.results)).sum

/-- The inductive invariant. -/
structure Inv (w : GW α) : Prop where
  /-- Σ ledger + every refund/restore still possible ≤ tokens the vault holds -/
  bal : w.app.ledger.total + pot T V w ≤ w.app.ft.get V
  idLt : ∀ q ∈ w.pending, q.id < w.nextId
  waitLt : ∀ q ∈ w.pending, ∀ d, q.waitsOn = some d → d < w.nextId
  resLt : ∀ p ∈ w.results, p.1 < w.nextId
  nodup : (w.pending.map (·.id)).Nodup
  unres : ∀ q ∈ w.pending, lookupResult w.results q.id = none
  /-- every in-flight credit has the token's resolve waiting on it, for at least that amount -/
  pairDep : ∀ o ∈ w.pending, ∀ a, depSrc T V o = some a →
    ∃ R ∈ w.pending, R.waitsOn = some o.id ∧ ∃ a', resAmt T V R = some a' ∧ a ≤ a'
  /-- every in-flight vault transfer has the vault's `after_withdraw` waiting on it -/
  pairWd : ∀ t ∈ w.pending, ∀ a, wdSrc T V t = some a →
    ∃ q ∈ w.pending, q.waitsOn = some t.id ∧ ∃ a', awAmt V q = some a' ∧ a ≤ a'
  /-- the vault never has an `ft_transfer_call` in flight -/
  noVcall : ∀ q ∈ w.pending, q.pred = V → q.recv = T →
    ∀ to a m d, q.action ≠ .call (.ft_transfer_call to a m) d

/-- Initial states: nothing in flight, ledger backed. -/
def Initial (w : GW α) : Prop :=
  w.pending = [] ∧ w.results = [] ∧ w.app.ledger.total ≤ w.app.ft.get V

/-- Transactions are signed by anyone except the two contracts. -/
def honestSigners (tr : List (Step α (Call α))) : Prop :=
  ∀ sg rv c d, Step.submit sg rv c d ∈ tr → sg ≠ T ∧ sg ≠ V

end NearAsync.Vault.Proof
