import Verifier.Proof.Generic

/-! Structural facts about a receipt that finishes normally (with a value or a returned promise). -/

set_option linter.unusedSectionVars false

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

/-- World after `r` finishes with value `v`, emitting `es`. -/
def okVal (w : GW α) (r : GR α) (dep : Nat) (s : St α) (es : List (Emit α (Call α))) (v : Val) : GW α :=
  { app := s, near := (w.near.add r.recv dep).sub r.recv (emitsDeposit es),
    pending := removePending w.pending r.id ++ mkReceipts r w.nextId es,
    results := (r.id, .ok v) :: w.results, nextId := w.nextId + es.length }

def redirect (rid new : Nat) (q : GR α) : GR α :=
  if q.waitsOn = some rid then { q with waitsOn := some new } else q

/-- World after `r` returns its emitted promise number `idx`. -/
def okProm (w : GW α) (r : GR α) (dep : Nat) (s : St α) (es : List (Emit α (Call α))) (idx : Nat) : GW α :=
  { app := s, near := (w.near.add r.recv dep).sub r.recv (emitsDeposit es),
    pending := (removePending w.pending r.id).map (redirect r.id (w.nextId + idx)) ++
      mkReceipts r w.nextId es,
    results := w.results, nextId := w.nextId + es.length }

/-- `runReceipt` on a call, spelled out. -/
theorem runReceipt_call (sys : System (St α) α (Call α)) (w : GW α) (r : GR α) (inp : Option PResult)
    (c : Call α) (dep : Nat) (hact : r.action = .call c dep) :
    runReceipt sys w r inp =
      match sys.dispatch r.recv { self := r.recv, pred := r.pred, signer := r.signer,
                                  deposit := dep, input := inp } c w.app with
      | .panic _ => failReceipt w r dep
      | .ok s es ret =>
        if (w.near.add r.recv dep).get r.recv < emitsDeposit es || !emitsWellFormed es then
          failReceipt w r dep
        else match ret with
          | .val v => okVal w r dep s es v
          | .promise idx => if idx < es.length then okProm w r dep s es idx else failReceipt w r dep := by
  unfold runReceipt
  rw [hact]
  simp only
  cases sys.dispatch r.recv { self := r.recv, pred := r.pred, signer := r.signer,
                              deposit := dep, input := inp } c w.app with
  | panic _ => rfl
  | ok s es ret =>
    simp only
    split
    · rfl
    · cases ret with
      | val v => rfl
      | promise idx =>
        simp only
        split
        · rfl
        · rfl

/-! ## Facts about freshly created receipts -/

theorem zipIdx_ids (es : List (Emit α (Call α))) (base n : Nat) :
    (es.zipIdx n).map (fun p => base + p.2) = List.range' (base + n) es.length := by
  induction es generalizing n with
  | nil => rfl
  | cons e t ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ]
    rw [ih (n + 1)]; simp [Nat.add_assoc]

theorem mk_ids (r : GR α) (base : Nat) (es : List (Emit α (Call α))) :
    (mkReceipts r base es).map (·.id) = List.range' base es.length := by
  unfold mkReceipts
  rw [List.map_map]
  have := zipIdx_ids es base 0
  simpa [Function.comp_def] using this

theorem mk_id_range {r : GR α} {base : Nat} {es : List (Emit α (Call α))} {q : GR α}
    (hq : q ∈ mkReceipts r base es) : base ≤ q.id ∧ q.id < base + es.length := by
  have : q.id ∈ (mkReceipts r base es).map (·.id) := List.mem_map_of_mem hq
  rw [mk_ids, List.mem_range'] at this
  obtain ⟨i, hi, he⟩ := this
  omega

theorem mk_wait {r : GR α} {base : Nat} {es : List (Emit α (Call α))} (hwf : emitsWellFormed es = true)
    {q : GR α} (hq : q ∈ mkReceipts r base es) :
    ∀ d, q.waitsOn = some d → base ≤ d ∧ d < q.id := by
  obtain ⟨e, i, hm, rfl⟩ := mem_mkReceipts.mp hq
  intro d hd
  unfold emitsWellFormed at hwf
  have := List.all_eq_true.mp hwf (e, i) hm
  simp only at hd this ⊢
  cases he : e.after with
  | none => rw [he] at hd; cases hd
  | some j =>
    rw [he] at hd this
    simp at hd this
    omega

theorem mk_pred {r : GR α} {base : Nat} {es : List (Emit α (Call α))} {q : GR α}
    (hq : q ∈ mkReceipts r base es) : q.pred = r.recv := by
  obtain ⟨e, i, _, rfl⟩ := mem_mkReceipts.mp hq; rfl

theorem fresh_none {w : GW α} (_hI : Inv T V w) (res : List (Nat × PResult))
    (hres : ∀ p ∈ res, p.1 < w.nextId) {i : Nat} (hi : w.nextId ≤ i) : lookupResult res i = none :=
  lookupResult_none_of_lt res i w.nextId hres hi

theorem res_cons_lt {w : GW α} (hI : Inv T V w) {r : GR α} (hr : r ∈ w.pending) (v : PResult) :
    ∀ p ∈ (r.id, v) :: w.results, p.1 < w.nextId := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h
  · exact hI.idLt r hr
  · exact hI.resLt p h

/-- A new receipt waiting on a fresh id: its potential is its full amount (no result yet). -/
theorem contrib_fresh {w : GW α} (hI : Inv T V w) (res : List (Nat × PResult))
    (hres : ∀ p ∈ res, p.1 < w.nextId) (q : GR α) (d : Nat) (hd : q.waitsOn = some d)
    (hfresh : w.nextId ≤ d) :
    contrib T V res q = (match resAmt T V q with
      | some a => a
      | none => match awAmt V q with | some a => a | none => 0) := by
  have hn := fresh_none hI res hres hfresh
  unfold contrib
  cases resAmt T V q <;> cases awAmt V q <;> simp [resPot, awPot, hd, hn]

/-! ## Structural invariants of the success worlds -/

structure NewOk (T V : α) (w' : GW α) (news : List (GR α)) : Prop where
  dep : ∀ o ∈ news, ∀ a, depSrc T V o = some a →
    ∃ R ∈ w'.pending, R.waitsOn = some o.id ∧ ∃ a', resAmt T V R = some a' ∧ a ≤ a'
  wd : ∀ t ∈ news, ∀ a, wdSrc T V t = some a →
    ∃ q ∈ w'.pending, q.waitsOn = some t.id ∧ ∃ a', awAmt V q = some a' ∧ a ≤ a'
  noV : ∀ q ∈ news, q.pred = V → q.recv = T → ∀ to a m d, q.action ≠ .call (.ft_transfer_call to a m) d

theorem okVal_inv {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {dep : Nat} {s : St α}
    {es : List (Emit α (Call α))} {v : Val} (hwf : emitsWellFormed es = true)
    (hbal : s.ledger.total + pot T V (okVal w r dep s es v) ≤ s.ft.get V)
    (hnew : NewOk T V (okVal w r dep s es v) (mkReceipts r w.nextId es)) :
    Inv T V (okVal w r dep s es v) := by
  have hrid := hI.idLt r hr
  have hunr := hI.unres r hr
  have hreslt := res_cons_lt hI hr (.ok v)
  constructor
  · exact hbal
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · have := hI.idLt q (mem_removePending.mp h).1; simp only [okVal]; omega
    · exact (mk_id_range h).2
  · intro q hq d hd
    rcases List.mem_append.mp hq with h | h
    · have := hI.waitLt q (mem_removePending.mp h).1 d hd; simp only [okVal]; omega
    · have := mk_wait hwf h d hd; have := (mk_id_range h).2; simp only [okVal]; omega
  · intro p hp; have := hreslt p hp; simp only [okVal]; omega
  · show ((removePending w.pending r.id ++ mkReceipts r w.nextId es).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append, mk_ids]
    refine ⟨nodup_removePending _ _ hI.nodup, List.nodup_range' _ (by decide), ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨q1, hq1, rfl⟩ := ha
    have := hI.idLt q1 (mem_removePending.mp hq1).1
    rw [List.mem_range'] at hb; omega
  · intro q hq
    show lookupResult ((r.id, .ok v) :: w.results) q.id = none
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨hm, hne⟩ := mem_removePending.mp h
      rw [lookupResult_cons, ite_eq_right_iff.mpr (fun e => absurd e.symm hne)]; exact hI.unres q hm
    · exact fresh_none hI _ hreslt (mk_id_range h).1
  · intro o ho a ha
    rcases List.mem_append.mp ho with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      obtain ⟨R, hR, hw, rest⟩ := hI.pairDep o hm a ha
      exact ⟨R, List.mem_append_left _ (mem_rest hI hr hrd hm hR hw), hw, rest⟩
    · exact hnew.dep o h a ha
  · intro t ht a ha
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      obtain ⟨q, hq, hw, rest⟩ := hI.pairWd t hm a ha
      exact ⟨q, List.mem_append_left _ (mem_rest hI hr hrd hm hq hw), hw, rest⟩
    · exact hnew.wd t h a ha
  · intro q hq h1 h2
    rcases List.mem_append.mp hq with h | h
    · exact hI.noVcall q (mem_removePending.mp h).1 h1 h2
    · exact hnew.noV q h h1 h2

theorem redirect_id (rid new : Nat) (q : GR α) : (redirect rid new q).id = q.id := by
  unfold redirect; split <;> rfl

theorem redirect_action (rid new : Nat) (q : GR α) : (redirect rid new q).action = q.action := by
  unfold redirect; split <;> rfl

theorem redirect_pred (rid new : Nat) (q : GR α) : (redirect rid new q).pred = q.pred := by
  unfold redirect; split <;> rfl

theorem redirect_recv (rid new : Nat) (q : GR α) : (redirect rid new q).recv = q.recv := by
  unfold redirect; split <;> rfl

theorem redirect_same (rid new : Nat) (q : GR α) (h : q.waitsOn ≠ some rid) : redirect rid new q = q := by
  unfold redirect; simp [h]

theorem resAmt_redirect (rid new : Nat) (q : GR α) : resAmt T V (redirect rid new q) = resAmt T V q := by
  unfold resAmt; rw [redirect_action, redirect_recv, redirect_pred]

theorem awAmt_redirect (rid new : Nat) (q : GR α) : awAmt V (redirect rid new q) = awAmt V q := by
  unfold awAmt; rw [redirect_action, redirect_recv, redirect_pred]

theorem depSrc_redirect (rid new : Nat) (q : GR α) : depSrc T V (redirect rid new q) = depSrc T V q := by
  unfold depSrc; rw [redirect_action, redirect_recv, redirect_pred]

theorem wdSrc_redirect (rid new : Nat) (q : GR α) : wdSrc T V (redirect rid new q) = wdSrc T V q := by
  unfold wdSrc; rw [redirect_action, redirect_recv, redirect_pred]

/-- Redirecting from one unresolved id to another does not change a potential. -/
theorem contrib_redirect (res : List (Nat × PResult)) (rid new : Nat)
    (h1 : lookupResult res rid = none) (h2 : lookupResult res new = none) (q : GR α) :
    contrib T V res (redirect rid new q) = contrib T V res q := by
  unfold redirect
  split
  · rename_i hw
    unfold contrib
    have e1 : resAmt T V { q with waitsOn := some new } = resAmt T V q := rfl
    have e2 : awAmt V { q with waitsOn := some new } = awAmt V q := rfl
    rw [e1, e2]
    simp only [hw]
    cases resAmt T V q <;> cases awAmt V q <;> simp [resPot, awPot, h1, h2]
  · rfl

theorem okProm_inv {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {dep : Nat} {s : St α}
    {es : List (Emit α (Call α))} {idx : Nat} (hwf : emitsWellFormed es = true) (hidx : idx < es.length)
    (hbal : s.ledger.total + pot T V (okProm w r dep s es idx) ≤ s.ft.get V)
    (hnew : NewOk T V (okProm w r dep s es idx) (mkReceipts r w.nextId es)) :
    Inv T V (okProm w r dep s es idx) := by
  have hrid := hI.idLt r hr
  have hunr := hI.unres r hr
  constructor
  · exact hbal
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_id]; have := hI.idLt q0 (mem_removePending.mp hq0).1; simp only [okProm]; omega
    · exact (mk_id_range h).2
  · intro q hq d hd
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      unfold redirect at hd
      split at hd
      · cases hd; simp only [okProm]; omega
      · have := hI.waitLt q0 (mem_removePending.mp hq0).1 d hd; simp only [okProm]; omega
    · have := mk_wait hwf h d hd; have := (mk_id_range h).2; simp only [okProm]; omega
  · intro p hp; have := hI.resLt p hp; simp only [okProm]; omega
  · show (((removePending w.pending r.id).map (redirect r.id (w.nextId + idx)) ++
      mkReceipts r w.nextId es).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append, mk_ids, List.map_map]
    have hids : (removePending w.pending r.id).map ((·.id) ∘ redirect r.id (w.nextId + idx)) =
        (removePending w.pending r.id).map (·.id) := by
      apply List.map_congr_left; intro q _; simp [redirect_id]
    rw [hids]
    refine ⟨nodup_removePending _ _ hI.nodup, List.nodup_range' _ (by decide), ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨q1, hq1, rfl⟩ := ha
    have := hI.idLt q1 (mem_removePending.mp hq1).1
    rw [List.mem_range'] at hb; omega
  · intro q hq
    show lookupResult w.results q.id = none
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_id]; exact hI.unres q0 (mem_removePending.mp hq0).1
    · exact fresh_none hI _ hI.resLt (mk_id_range h).1
  · intro o ho a ha
    rcases List.mem_append.mp ho with h | h
    · obtain ⟨o0, ho0, rfl⟩ := List.mem_map.mp h
      rw [depSrc_redirect] at ha
      obtain ⟨hm, hne⟩ := mem_removePending.mp ho0
      obtain ⟨R, hR, hw, rest⟩ := hI.pairDep o0 hm a ha
      have hRr := mem_rest hI hr hrd hm hR hw
      have hsame : redirect r.id (w.nextId + idx) R = R :=
        redirect_same _ _ _ (by rw [hw]; intro e; exact hne (Option.some.inj e))
      refine ⟨R, List.mem_append_left _ (List.mem_map.mpr ⟨R, hRr, hsame⟩), ?_, rest⟩
      rw [hw, redirect_id]
    · exact hnew.dep o h a ha
  · intro t ht a ha
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp h
      rw [wdSrc_redirect] at ha
      obtain ⟨hm, hne⟩ := mem_removePending.mp ht0
      obtain ⟨q, hq, hw, rest⟩ := hI.pairWd t0 hm a ha
      have hqr := mem_rest hI hr hrd hm hq hw
      have hsame : redirect r.id (w.nextId + idx) q = q :=
        redirect_same _ _ _ (by rw [hw]; intro e; exact hne (Option.some.inj e))
      refine ⟨q, List.mem_append_left _ (List.mem_map.mpr ⟨q, hqr, hsame⟩), ?_, rest⟩
      rw [hw, redirect_id]
    · exact hnew.wd t h a ha
  · intro q hq h1 h2
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_pred] at h1; rw [redirect_recv] at h2
      intro to a m d; rw [redirect_action]
      exact hI.noVcall q0 (mem_removePending.mp hq0).1 h1 h2 to a m d
    · exact hnew.noV q h h1 h2

end NearAsync.Vault.Proof
