import Verifier.Proof.Defs

/-! Structural part of the invariant proof: failures, refunds, and facts shared by all cases. -/

set_option linter.unusedSectionVars false

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

theorem unusedOf_le (r : PResult) (a : Nat) : unusedOf r a ≤ a := by
  cases r with
  | ok v => cases v <;> simp [unusedOf, unusedAmount, Nat.min_le_right]
  | failed => simp [unusedOf, unusedAmount]

theorem resPot_mono (res res' : List (Nat × PResult))
    (hres : ∀ d, lookupResult res d ≠ none → lookupResult res' d = lookupResult res d)
    (d : Option Nat) (a : Nat) : resPot res' d a ≤ resPot res d a := by
  cases d with
  | none => simp [resPot]
  | some d =>
    simp only [resPot]
    cases h : lookupResult res d with
    | none => cases lookupResult res' d <;> simp [unusedOf_le]
    | some r => rw [hres d (by simp [h]), h]; exact Nat.le_refl _

theorem awPot_mono (res res' : List (Nat × PResult))
    (hres : ∀ d, lookupResult res d ≠ none → lookupResult res' d = lookupResult res d)
    (d : Option Nat) (a : Nat) : awPot res' d a ≤ awPot res d a := by
  cases d with
  | none => simp [awPot]
  | some d =>
    simp only [awPot]
    cases h : lookupResult res d with
    | none =>
      cases h' : lookupResult res' d with
      | none => simp
      | some r => cases r <;> simp
    | some r => rw [hres d (by simp [h]), h]; exact Nat.le_refl _

/-- Adding results only lowers potentials. -/
theorem contrib_mono (res res' : List (Nat × PResult))
    (hres : ∀ d, lookupResult res d ≠ none → lookupResult res' d = lookupResult res d) (q : GR α) :
    contrib T V res' q ≤ contrib T V res q := by
  unfold contrib
  cases resAmt T V q with
  | some a => exact resPot_mono res res' hres _ a
  | none =>
    cases awAmt V q with
    | some a => exact awPot_mono res res' hres _ a
    | none => exact Nat.le_refl _

theorem agree_cons (res : List (Nat × PResult)) (k : Nat) (x : PResult)
    (hk : lookupResult res k = none) :
    ∀ d, lookupResult res d ≠ none → lookupResult ((k, x) :: res) d = lookupResult res d := by
  intro d hd
  rw [lookupResult_cons]
  split
  · subst_vars; exact absurd hk hd
  · rfl

theorem eq_of_id {ps : List (GR α)} (hnd : (ps.map (·.id)).Nodup) {a b : GR α}
    (ha : a ∈ ps) (hb : b ∈ ps) (h : a.id = b.id) : a = b := by
  induction ps with
  | nil => simp at ha
  | cons q t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (h ▸ List.mem_map_of_mem hb') hnd.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (h.symm ▸ List.mem_map_of_mem ha') hnd.1
      · exact ih hnd.2 ha' hb'

theorem readiness_some {w : GW α} {r : GR α} {inp : Option PResult} (h : readiness w r = some inp) :
    ∀ d, r.waitsOn = some d → lookupResult w.results d ≠ none := by
  intro d hd
  unfold readiness at h
  rw [hd] at h
  intro hn; simp only [hn] at h; simp at h

/-- A receipt that waits on a pending receipt is not the receipt being executed. -/
theorem waiter_ne {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp)
    {o R : GR α} (ho : o ∈ w.pending) (hR : R ∈ w.pending) (hw : R.waitsOn = some o.id) :
    R.id ≠ r.id := by
  intro h
  have := eq_of_id hI.nodup hR hr h
  subst this
  exact readiness_some hrd o.id hw (hI.unres o ho)

theorem mem_rest {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp)
    {o R : GR α} (ho : o ∈ w.pending) (hR : R ∈ w.pending) (hw : R.waitsOn = some o.id) :
    R ∈ removePending w.pending r.id :=
  mem_removePending.mpr ⟨hR, waiter_ne hI hr hrd ho hR hw⟩

theorem nodup_removePending (ps : List (GR α)) (i : Nat) (h : (ps.map (·.id)).Nodup) :
    ((removePending ps i).map (·.id)).Nodup := by
  unfold removePending
  exact (List.filter_sublist.map (fun q : GR α => q.id)).nodup h

/-- Pot of the remaining receipts after `r` leaves, with results that only grew at `r.id`. -/
theorem pot_rest_le {w : GW α} (hI : Inv T V w) {r : GR α} (hr : r ∈ w.pending)
    (res' : List (Nat × PResult))
    (hres : ∀ d, lookupResult w.results d ≠ none → lookupResult res' d = lookupResult w.results d) :
    ((removePending w.pending r.id).map (contrib T V res')).sum + contrib T V w.results r ≤
      pot T V w := by
  have h1 := sum_removePending w.pending (contrib T V w.results) hI.nodup r hr
  have h2 := sum_map_le (removePending w.pending r.id) (contrib T V res') (contrib T V w.results)
    (fun q _ => contrib_mono w.results res' hres q)
  unfold pot; omega

/-- **Failures preserve the invariant**: a failed receipt changes no storage, its dependents see
`failed` (which never raises a potential), and the refund receipt moves only NEAR. -/
theorem fail_inv {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) (dep : Nat) :
    Inv T V (failReceipt w r dep) := by
  have hrid := hI.idLt r hr
  have hunr := hI.unres r hr
  have hagree := agree_cons w.results r.id .failed hunr
  -- the refund receipt, if any
  have hrf : ∀ q ∈ (if dep = 0 then ([] : List (GR α)) else
      [{ id := w.nextId, pred := r.recv, signer := r.signer, recv := r.pred,
         action := .refund dep, waitsOn := none }]),
      q.id = w.nextId ∧ q.waitsOn = none ∧ ∃ n, q.action = .refund n := by
    intro q hq; split at hq
    · simp at hq
    · simp at hq; subst hq; exact ⟨rfl, rfl, dep, rfl⟩
  constructor
  · -- bal
    show w.app.ledger.total + ((removePending w.pending r.id ++ _).map _).sum ≤ w.app.ft.get V
    rw [List.map_append, List.sum_append]
    have hz : ((if dep = 0 then ([] : List (GR α)) else
        [{ id := w.nextId, pred := r.recv, signer := r.signer, recv := r.pred,
           action := .refund dep, waitsOn := none }]).map (contrib T V ((r.id, .failed) :: w.results))).sum = 0 := by
      split <;> simp [contrib, resAmt, awAmt]
    have := pot_rest_le hI hr _ hagree
    have := hI.bal
    simp only [show (failReceipt w r dep).results = (r.id, PResult.failed) :: w.results from rfl] at hz ⊢
    omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact Nat.lt_succ_of_lt (hI.idLt q (mem_removePending.mp h).1)
    · rw [(hrf q h).1]; exact Nat.lt_succ_self _
  · intro q hq d hd
    rcases List.mem_append.mp hq with h | h
    · exact Nat.lt_succ_of_lt (hI.waitLt q (mem_removePending.mp h).1 d hd)
    · rw [(hrf q h).2.1] at hd; cases hd
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | h
    · exact Nat.lt_succ_of_lt hrid
    · exact Nat.lt_succ_of_lt (hI.resLt p h)
  · show ((removePending w.pending r.id ++ _).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨nodup_removePending _ _ hI.nodup, ?_, ?_⟩
    · split <;> simp
    · intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨q1, hq1, rfl⟩ := ha
      obtain ⟨q2, hq2, rfl⟩ := hb
      have := hI.idLt q1 (mem_removePending.mp hq1).1
      rw [(hrf q2 hq2).1]; omega
  · intro q hq
    show lookupResult ((r.id, .failed) :: w.results) q.id = none
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨hm, hne⟩ := mem_removePending.mp h
      rw [lookupResult_cons, ite_eq_right_iff.mpr (fun e => absurd e.symm hne)]; exact hI.unres q hm
    · rw [(hrf q h).1]
      apply lookupResult_none_of_lt _ _ w.nextId _ (Nat.le_refl _)
      intro p hp
      rcases List.mem_cons.mp hp with rfl | h
      · exact hrid
      · exact hI.resLt p h
  · intro o ho a ha
    rcases List.mem_append.mp ho with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      obtain ⟨R, hR, hw, rest⟩ := hI.pairDep o hm a ha
      exact ⟨R, List.mem_append_left _ (mem_rest hI hr hrd hm hR hw), hw, rest⟩
    · obtain ⟨_, _, n, hn⟩ := hrf o h
      simp [depSrc, hn] at ha
  · intro t ht a ha
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      obtain ⟨q, hq, hw, rest⟩ := hI.pairWd t hm a ha
      exact ⟨q, List.mem_append_left _ (mem_rest hI hr hrd hm hq hw), hw, rest⟩
    · obtain ⟨_, _, n, hn⟩ := hrf t h
      simp [wdSrc, hn] at ha
  · intro q hq h1 h2 to a m d
    rcases List.mem_append.mp hq with h | h
    · exact hI.noVcall q (mem_removePending.mp h).1 h1 h2 to a m d
    · obtain ⟨_, _, n, hn⟩ := hrf q h
      rw [hn]; simp

end NearAsync.Vault.Proof
