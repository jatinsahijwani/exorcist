import Verifier.Async

/-! Generic lemmas about balances, lists and the semantics, used by the invariant proofs. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace NearAsync

variable {α : Type} [DecidableEq α]

namespace Bal

theorem get_filter_ne (m : Bal α) (a b : α) (h : b ≠ a) :
    Bal.get (m.filter (fun p => !decide (p.1 = a))) b = m.get b := by
  induction m with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = a
    · subst hk
      have : (k = b) = False := propext ⟨fun e => h e.symm, False.elim⟩
      simp [List.filter, get, ih, this]
    · by_cases hkb : k = b
      · subst hkb; simp [List.filter, get, hk]
      · simp [List.filter, get, hk, hkb, ih]

theorem get_set (m : Bal α) (a b : α) (v : Nat) :
    (m.set a v).get b = if a = b then v else m.get b := by
  by_cases h : a = b
  · subst h; simp [set, get]
  · simp only [set, get, h, ite_false]
    exact get_filter_ne m a b (fun e => h e.symm)

/-- Sum of all entries with key `a`. -/
def keySum : Bal α → α → Nat
  | [], _ => 0
  | (b, v) :: t, a => (if b = a then v else 0) + keySum t a

theorem total_split (m : Bal α) (a : α) :
    m.total = keySum m a + Bal.total (m.filter (fun p => !decide (p.1 = a))) := by
  induction m with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = a
    · subst hk; simp [total, keySum, List.filter, ih]; omega
    · simp [total, keySum, List.filter, hk, ih]; omega

theorem get_le_keySum (m : Bal α) (a : α) : m.get a ≤ keySum m a := by
  induction m with
  | nil => exact Nat.le_refl _
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = a
    · subst hk; simp [get, keySum]
    · simp [get, keySum, hk, ih]

theorem total_set (m : Bal α) (a : α) (v : Nat) :
    (m.set a v).total = v + Bal.total (m.filter (fun p => !decide (p.1 = a))) := rfl

theorem total_add_le (m : Bal α) (a : α) (n : Nat) : (m.add a n).total ≤ m.total + n := by
  have h1 := total_split m a
  have h2 := get_le_keySum m a
  simp only [add, total_set]
  omega

theorem total_sub_le (m : Bal α) (a : α) (n : Nat) (h : n ≤ m.get a) :
    (m.sub a n).total + n ≤ m.total := by
  have h1 := total_split m a
  have h2 := get_le_keySum m a
  simp only [sub, total_set]
  omega

theorem get_add (m : Bal α) (a b : α) (n : Nat) :
    (m.add a n).get b = if a = b then m.get b + n else m.get b := by
  simp only [add, get_set]; split <;> simp_all

theorem get_sub (m : Bal α) (a b : α) (n : Nat) :
    (m.sub a n).get b = if a = b then m.get b - n else m.get b := by
  simp only [sub, get_set]; split <;> simp_all

end Bal

/-! ## List sums -/

theorem sum_map_le {β : Type} (l : List β) (f g : β → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem sum_map_le_dec {β : Type} (l : List β) (f g : β → Nat) (h : ∀ x ∈ l, f x ≤ g x)
    (x0 : β) (hx0 : x0 ∈ l) (a : Nat) (hd : f x0 + a ≤ g x0) :
    (l.map f).sum + a ≤ (l.map g).sum := by
  induction l with
  | nil => simp at hx0
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx0 with e | hm
    · subst e
      have := sum_map_le t f g (fun y hy => h y (List.mem_cons_of_mem _ hy))
      omega
    · have := h x (List.mem_cons_self ..)
      have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hm
      omega

/-! ## Pending-list lemmas -/

variable {C : Type}

theorem mem_removePending {ps : List (Receipt α C)} {i : Nat} {q : Receipt α C} :
    q ∈ removePending ps i ↔ q ∈ ps ∧ q.id ≠ i := by
  simp [removePending, List.mem_filter]

theorem sum_removePending (ps : List (Receipt α C)) (f : Receipt α C → Nat)
    (hnd : (ps.map (·.id)).Nodup) (r : Receipt α C) (hr : r ∈ ps) :
    ((removePending ps r.id).map f).sum + f r = (ps.map f).sum := by
  induction ps with
  | nil => simp at hr
  | cons q t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hq, hnd⟩ := hnd
    rcases List.mem_cons.mp hr with e | hm
    · subst e
      have hall : removePending t r.id = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        have : x.id ≠ r.id := fun e => hq (e ▸ List.mem_map_of_mem hx)
        simp [this]
      have hrm : removePending (r :: t) r.id = t := by
        rw [← hall]; simp [removePending, List.filter]
      rw [hrm, List.map_cons, List.sum_cons]; omega
    · have hne : q.id ≠ r.id := fun e => hq (e ▸ List.mem_map_of_mem hm)
      have := ih hnd hm
      simp [removePending, List.filter, hne, List.sum_cons] at this ⊢
      omega

theorem findPending_spec {ps : List (Receipt α C)} {i : Nat} {r : Receipt α C}
    (h : findPending ps i = some r) : r ∈ ps ∧ r.id = i := by
  induction ps with
  | nil => simp [findPending] at h
  | cons q t ih =>
    simp only [findPending] at h
    split at h
    · cases h; exact ⟨List.mem_cons_self .., by assumption⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

theorem lookupResult_cons (res : List (Nat × PResult)) (k i : Nat) (x : PResult) :
    lookupResult ((k, x) :: res) i = if k = i then some x else lookupResult res i := rfl

theorem lookupResult_none_of_lt (res : List (Nat × PResult)) (i n : Nat)
    (h : ∀ p ∈ res, p.1 < n) (hi : n ≤ i) : lookupResult res i = none := by
  induction res with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, x⟩ := p
    have hk := h (k, x) (List.mem_cons_self ..)
    simp only [lookupResult]
    rw [ite_eq_right_iff.mpr (fun e => absurd e (by simp at hk; omega))]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem mem_mkReceipts {r : Receipt α C} {base : Nat} {es : List (Emit α C)} {q : Receipt α C} :
    q ∈ mkReceipts r base es ↔ ∃ e i, (e, i) ∈ es.zipIdx ∧
      q = { id := base + i, pred := r.recv, signer := r.signer, recv := e.recv,
            action := .call e.call e.deposit, waitsOn := e.after.map (base + ·) } := by
  simp only [mkReceipts, List.mem_map]
  constructor
  · rintro ⟨⟨e, i⟩, hm, rfl⟩; exact ⟨e, i, hm, rfl⟩
  · rintro ⟨e, i, hm, rfl⟩; exact ⟨(e, i), hm, rfl⟩

end NearAsync
