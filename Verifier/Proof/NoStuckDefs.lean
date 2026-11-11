import Verifier.Proof.Theorem

/-!
# Exact accounting for the fixed vault (no stuck funds) — definitions and generic lemmas

Extra assumptions compared with the solvency theorem, all explicit:
* only non-callback receipts may be failed by the adversary (callbacks have gas reserved);
* nobody sends the vault tokens with a plain `ft_transfer` (a donation is not owed to anyone, so it
  would legitimately be "stuck"): neither transactions nor other contracts call `ft_transfer(V, _)`;
* the initial ledger has distinct keys and matches the vault's balance exactly.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

/-- A receipt that carries potential. -/
def bearing (T V : α) (q : GR α) : Prop := (resAmt T V q).isSome ∨ (awAmt V q).isSome

/-- The exact-accounting invariant. -/
structure J (T V : α) (w : GW α) : Prop where
  inv : Inv T V w
  lower : w.app.ft.get V ≤ w.app.ledger.total + pot T V w
  keys : (w.app.ledger.map (·.1)).Nodup
  pairE : ∀ q ∈ w.pending, ∀ d, q.waitsOn = some d → lookupResult w.results d = none →
    (∀ a, resAmt T V q = some a → ∃ s ∈ w.pending, s.id = d ∧ depSrc T V s = some a) ∧
    (∀ a, awAmt V q = some a → ∃ s ∈ w.pending, s.id = d ∧ wdSrc T V s = some a)
  uniq : ∀ q1 ∈ w.pending, ∀ q2 ∈ w.pending, bearing T V q1 → bearing T V q2 →
    ∀ d, q1.waitsOn = some d → q2.waitsOn = some d → q1.id = q2.id
  resSender : ∀ q ∈ w.pending, q.pred = T → q.recv = T →
    ∀ s rcv a d, q.action = .call (.ft_resolve_transfer s rcv a) d → s ≠ V
  noDonation : ∀ q ∈ w.pending, q.recv = T → ∀ a d, q.action ≠ .call (.ft_transfer V a) d
  noVwithdraw : ∀ q ∈ w.pending, q.pred = V → ∀ a d, q.action ≠ .call (.withdraw a) d

/-- Other contracts never donate to the vault. -/
def NoDonate (T V : α) (other : α → Handler α) : Prop :=
  ∀ a ctx c s s' es ret, other a ctx c s = .ok s' es ret →
    ∀ e ∈ es, e.recv = T → ∀ x, e.call ≠ .ft_transfer V x

/-- Transactions: not signed by the contracts, and no plain `ft_transfer` to the vault. -/
def honestTxs (T V : α) (tr : List (Step α (Call α))) : Prop :=
  ∀ sg rv c d, Step.submit sg rv c d ∈ tr → sg ≠ T ∧ sg ≠ V ∧ (rv = T → ∀ x, c ≠ .ft_transfer V x)

def InitialExact (V : α) (w : GW α) : Prop :=
  w.pending = [] ∧ w.results = [] ∧ w.app.ledger.total = w.app.ft.get V ∧ (w.app.ledger.map (·.1)).Nodup

/-! ## Ledger with distinct keys -/

theorem keySum_eq_get (m : Bal α) (a : α) (h : (m.map (·.1)).Nodup) : Bal.keySum m a = m.get a := by
  induction m with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases hk : k = a
    · subst hk
      have : Bal.keySum t k = 0 := by
        have hn := h.1
        clear ih h
        induction t with
        | nil => rfl
        | cons p t ih2 =>
          obtain ⟨k2, v2⟩ := p
          simp only [List.map_cons, List.mem_cons, not_or] at hn
          simp [Bal.keySum, Ne.symm hn.1, ih2 hn.2]
      simp [Bal.keySum, Bal.get, this]
    · simp [Bal.keySum, Bal.get, hk, ih h.2]

theorem total_add_eq (m : Bal α) (a : α) (n : Nat) (h : (m.map (·.1)).Nodup) :
    (m.add a n).total = m.total + n := by
  have h1 := Bal.total_split m a
  have h2 := keySum_eq_get m a h
  simp only [Bal.add, Bal.total_set]; omega

theorem total_sub_eq (m : Bal α) (a : α) (n : Nat) (h : (m.map (·.1)).Nodup) (hn : n ≤ m.get a) :
    (m.sub a n).total + n = m.total := by
  have h1 := Bal.total_split m a
  have h2 := keySum_eq_get m a h
  simp only [Bal.sub, Bal.total_set]; omega

theorem keys_set (m : Bal α) (a : α) (v : Nat) (h : (m.map (·.1)).Nodup) : ((m.set a v).map (·.1)).Nodup := by
  simp only [Bal.set, List.map_cons, List.nodup_cons]
  constructor
  · simp [List.mem_map, List.mem_filter]
  · have : ((m.filter (fun p => !decide (p.1 = a))).map (·.1)).Sublist (m.map (·.1)) :=
      List.filter_sublist.map _
    exact this.nodup h

theorem keys_add (m : Bal α) (a : α) (n : Nat) (h : (m.map (·.1)).Nodup) : ((m.add a n).map (·.1)).Nodup :=
  keys_set m a _ h

theorem keys_sub (m : Bal α) (a : α) (n : Nat) (h : (m.map (·.1)).Nodup) : ((m.sub a n).map (·.1)).Nodup :=
  keys_set m a _ h

/-! ## Sums with at most one exceptional element -/

theorem sum_le_one_exception {β : Type} (l : List β) (key : β → Nat) (hnd : (l.map key).Nodup)
    (P : β → Prop) (hP : ∀ x ∈ l, ∀ y ∈ l, P x → P y → key x = key y)
    (f g : β → Nat) (δ : Nat) (h1 : ∀ x ∈ l, ¬P x → g x ≤ f x) (h2 : ∀ x ∈ l, P x → g x ≤ f x + δ) :
    (l.map g).sum ≤ (l.map f).sum + δ := by
  classical
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : P x
    · -- every other element is unexceptional
      have hrest : ∀ y ∈ t, ¬P y := by
        intro y hy hPy
        have := hP x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy) hx hPy
        exact hnd.1 (this ▸ List.mem_map_of_mem hy)
      have := sum_map_le t g f (fun y hy => h1 y (List.mem_cons_of_mem _ hy) (hrest y hy))
      have := h2 x (List.mem_cons_self ..) hx
      omega
    · have := h1 x (List.mem_cons_self ..) hx
      have := ih hnd.2 (fun a ha b hb => hP a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        (fun y hy => h1 y (List.mem_cons_of_mem _ hy)) (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
      omega

/-! ## Waiters of an executed receipt -/

/-- If `r` is not an in-flight source, no potential depends on its result. -/
theorem contrib_rest_eq {w : GW α} (hJ : J T V w) {r : GR α} (hr : r ∈ w.pending)
    (hd : depSrc T V r = none) (hwd : wdSrc T V r = none) (x : PResult)
    {q : GR α} (hq : q ∈ w.pending) :
    contrib T V ((r.id, x) :: w.results) q = contrib T V w.results q := by
  have hunr := hJ.inv.unres r hr
  unfold contrib
  cases ha : resAmt T V q with
  | some a =>
    simp only
    unfold resPot
    cases hw : q.waitsOn with
    | none => rfl
    | some d =>
      simp only
      by_cases hdr : d = r.id
      · subst hdr
        obtain ⟨s, hs, hsid, hsd⟩ := (hJ.pairE q hq r.id hw hunr).1 a ha
        have := eq_of_id hJ.inv.nodup hs hr hsid
        subst this; rw [hd] at hsd; cases hsd
      · rw [lookupResult_cons, if_neg (Ne.symm hdr)]
  | none =>
    simp only
    cases hb : awAmt V q with
    | some a =>
      simp only
      unfold awPot
      cases hw : q.waitsOn with
      | none => rfl
      | some d =>
        simp only
        by_cases hdr : d = r.id
        · subst hdr
          obtain ⟨s, hs, hsid, hsd⟩ := (hJ.pairE q hq r.id hw hunr).2 a hb
          have := eq_of_id hJ.inv.nodup hs hr hsid
          subst this; rw [hwd] at hsd; cases hsd
        · rw [lookupResult_cons, if_neg (Ne.symm hdr)]
    | none => rfl

/-- Remaining potential when `r` (a source) finishes with result `x`: it drops by at most `δ`,
where `δ` bounds the drop at the (unique) waiter. -/
theorem pot_rest_ge {w : GW α} (hJ : J T V w) {r : GR α} (hr : r ∈ w.pending) (x : PResult) (δ : Nat)
    (hδ : ∀ q ∈ w.pending, bearing T V q → q.waitsOn = some r.id →
      contrib T V w.results q ≤ contrib T V ((r.id, x) :: w.results) q + δ) :
    ((removePending w.pending r.id).map (contrib T V w.results)).sum ≤
      ((removePending w.pending r.id).map (contrib T V ((r.id, x) :: w.results))).sum + δ := by
  have hunr := hJ.inv.unres r hr
  have hagree := agree_cons w.results r.id x hunr
  apply sum_le_one_exception _ (·.id) (nodup_removePending _ _ hJ.inv.nodup)
    (fun q => bearing T V q ∧ q.waitsOn = some r.id)
  · intro a ha b hb hPa hPb
    exact hJ.uniq a (mem_removePending.mp ha).1 b (mem_removePending.mp hb).1 hPa.1 hPb.1 r.id hPa.2 hPb.2
  · intro q hq hnot
    -- not a bearing waiter of r: its potential does not depend on r's result
    have hqm := (mem_removePending.mp hq).1
    unfold contrib
    cases ha : resAmt T V q with
    | some a =>
      simp only; unfold resPot
      cases hw : q.waitsOn with
      | none => exact Nat.le_refl _
      | some d =>
        simp only
        have hdr : d ≠ r.id := fun e => hnot ⟨Or.inl (by simp [ha]), by rw [hw, e]⟩
        rw [lookupResult_cons, if_neg (Ne.symm hdr)]; exact Nat.le_refl _
    | none =>
      simp only
      cases hb : awAmt V q with
      | some a =>
        simp only; unfold awPot
        cases hw : q.waitsOn with
        | none => exact Nat.le_refl _
        | some d =>
          simp only
          have hdr : d ≠ r.id := fun e => hnot ⟨Or.inr (by simp [hb]), by rw [hw, e]⟩
          rw [lookupResult_cons, if_neg (Ne.symm hdr)]; exact Nat.le_refl _
      | none => exact Nat.le_refl _
  · intro q hq hP
    exact hδ q (mem_removePending.mp hq).1 hP.1 hP.2

end NearAsync.Vault.Proof
