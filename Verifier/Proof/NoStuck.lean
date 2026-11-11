import Verifier.Proof.NoStuckDefs

/-! # Exact accounting is preserved by every step (fixed vault, non-callback failures, no donations) -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

theorem contrib_failed_eq (res : List (Nat × PResult)) (k : Nat) (hk : lookupResult res k = none) (q : GR α) :
    contrib T V ((k, .failed) :: res) q = contrib T V res q := by
  unfold contrib
  cases resAmt T V q <;> cases awAmt V q <;> simp only <;>
    (first
      | (unfold resPot; cases hw : q.waitsOn <;> simp only <;>
          (rename_i d; by_cases h : k = d
           · subst h; simp [lookupResult_cons, hk, unusedOf, unusedAmount]
           · simp [lookupResult_cons, h]))
      | (unfold awPot; cases hw : q.waitsOn <;> simp only <;>
          (rename_i d; by_cases h : k = d
           · subst h; simp [lookupResult_cons, hk]
           · simp [lookupResult_cons, h]))
      | rfl)

theorem not_bearing_contrib {res : List (Nat × PResult)} {q : GR α} (h : ¬ bearing T V q) :
    contrib T V res q = 0 := by
  unfold bearing at h
  apply contrib_zero
  · cases e : resAmt T V q <;> simp_all
  · cases e : awAmt V q <;> simp_all

theorem bearing_of_contrib {res : List (Nat × PResult)} {q : GR α} (h : contrib T V res q ≠ 0) :
    bearing T V q := by
  exact Classical.byContradiction fun hn => h (not_bearing_contrib hn)

/-! ## Failures and refunds -/

theorem J_fail {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) (dep : Nat)
    (hc : contrib T V w.results r = 0) : J T V (failReceipt w r dep) := by
  have hunr := hJ.inv.unres r hr
  have hrf : ∀ q ∈ (if dep = 0 then ([] : List (GR α)) else
      [{ id := w.nextId, pred := r.recv, signer := r.signer, recv := r.pred,
         action := .refund dep, waitsOn := none }]), q.id = w.nextId ∧ q.waitsOn = none ∧ ∃ n, q.action = .refund n := by
    intro q hq; split at hq
    · simp at hq
    · simp at hq; subst hq; exact ⟨rfl, rfl, dep, rfl⟩
  have hnb : ∀ q ∈ (if dep = 0 then ([] : List (GR α)) else
      [{ id := w.nextId, pred := r.recv, signer := r.signer, recv := r.pred,
         action := .refund dep, waitsOn := none }]), ¬ bearing T V q := by
    intro q hq
    obtain ⟨_, _, n, hn⟩ := hrf q hq
    simp [bearing, resAmt, awAmt, hn]
  refine ⟨fail_inv hJ.inv hr hrd dep, ?_, hJ.keys, ?_, ?_, ?_, ?_, ?_⟩
  · show w.app.ft.get V ≤ w.app.ledger.total + ((removePending w.pending r.id ++ _).map _).sum
    rw [List.map_append, List.sum_append]
    have h1 := sum_removePending w.pending (contrib T V w.results) hJ.inv.nodup r hr
    have h2 : (removePending w.pending r.id).map (contrib T V ((r.id, PResult.failed) :: w.results)) =
        (removePending w.pending r.id).map (contrib T V w.results) :=
      List.map_congr_left (fun q _ => contrib_failed_eq _ _ hunr q)
    simp only [show (failReceipt w r dep).results = (r.id, PResult.failed) :: w.results from rfl, h2]
    have := hJ.lower; unfold pot at this; omega
  · intro q hq d hw hl
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      have hdr : d ≠ r.id := fun e => by
        simp only [show (failReceipt w r dep).results = (r.id, PResult.failed) :: w.results from rfl,
          lookupResult_cons, e, if_true] at hl; cases hl
      have hl0 : lookupResult w.results d = none := by
        simp only [show (failReceipt w r dep).results = (r.id, PResult.failed) :: w.results from rfl,
          lookupResult_cons, if_neg (Ne.symm hdr)] at hl; exact hl
      obtain ⟨h1, h2⟩ := hJ.pairE q hm d hw hl0
      constructor
      · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h1 a ha
        exact ⟨s, List.mem_append_left _ (mem_removePending.mpr ⟨hs, hsid ▸ hdr⟩), hsid, hsd⟩
      · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h2 a ha
        exact ⟨s, List.mem_append_left _ (mem_removePending.mpr ⟨hs, hsid ▸ hdr⟩), hsid, hsd⟩
    · rw [(hrf q h).2.1] at hw; cases hw
  · intro q1 h1 q2 h2 b1 b2 d w1 w2
    rcases List.mem_append.mp h1 with h1 | h1
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact hJ.uniq q1 (mem_removePending.mp h1).1 q2 (mem_removePending.mp h2).1 b1 b2 d w1 w2
      · exact absurd b2 (hnb q2 h2)
    · exact absurd b1 (hnb q1 h1)
  · intro q hq h1 h2
    rcases List.mem_append.mp hq with h | h
    · exact hJ.resSender q (mem_removePending.mp h).1 h1 h2
    · obtain ⟨_, _, n, hn⟩ := hrf q h; intro s rcv a d e; rw [hn] at e; cases e
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noDonation q (mem_removePending.mp h).1 h1
    · obtain ⟨_, _, n, hn⟩ := hrf q h; intro a d e; rw [hn] at e; cases e
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noVwithdraw q (mem_removePending.mp h).1 h1
    · obtain ⟨_, _, n, hn⟩ := hrf q h; intro a d e; rw [hn] at e; cases e

theorem J_refund {sys : System (St α) α (Call α)} {w : GW α} (hJ : J T V w) {r : GR α}
    {inp : Option PResult} (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {amt : Nat}
    (hact : r.action = .refund amt) : J T V (runReceipt sys w r inp) := by
  have h : runReceipt sys w r inp =
      { w with near := w.near.add r.recv amt, pending := removePending w.pending r.id } := by
    unfold runReceipt; rw [hact]
  have hI := refund_inv (sys := sys) hJ.inv hr hrd hact
  rw [h] at hI ⊢
  have hc : contrib T V w.results r = 0 := contrib_zero (by simp [resAmt, hact]) (by simp [awAmt, hact])
  refine ⟨hI, ?_, hJ.keys, ?_, ?_, ?_, ?_, ?_⟩
  · show w.app.ft.get V ≤ w.app.ledger.total + ((removePending w.pending r.id).map (contrib T V w.results)).sum
    have h1 := sum_removePending w.pending (contrib T V w.results) hJ.inv.nodup r hr
    have := hJ.lower; unfold pot at this; omega
  · intro q hq d hw hl
    obtain ⟨hm, _⟩ := mem_removePending.mp hq
    obtain ⟨h1, h2⟩ := hJ.pairE q hm d hw hl
    constructor
    · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h1 a ha
      by_cases e : s.id = r.id
      · have := eq_of_id hJ.inv.nodup hs hr e; subst this; simp [depSrc, hact] at hsd
      · exact ⟨s, mem_removePending.mpr ⟨hs, e⟩, hsid, hsd⟩
    · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h2 a ha
      by_cases e : s.id = r.id
      · have := eq_of_id hJ.inv.nodup hs hr e; subst this; simp [wdSrc, hact] at hsd
      · exact ⟨s, mem_removePending.mpr ⟨hs, e⟩, hsid, hsd⟩
  · intro q1 h1 q2 h2; exact hJ.uniq q1 (mem_removePending.mp h1).1 q2 (mem_removePending.mp h2).1
  · intro q hq; exact hJ.resSender q (mem_removePending.mp hq).1
  · intro q hq; exact hJ.noDonation q (mem_removePending.mp hq).1
  · intro q hq; exact hJ.noVwithdraw q (mem_removePending.mp hq).1

theorem J_submit {w : GW α} (hJ : J T V w) (sg rv : α) (c : Call α) (dep : Nat)
    (hsT : sg ≠ T) (hsV : sg ≠ V) (hdon : rv = T → ∀ x, c ≠ .ft_transfer V x) :
    J T V { w with near := w.near.sub sg dep,
                   pending := w.pending ++ [{ id := w.nextId, pred := sg, signer := sg, recv := rv,
                                              action := .call c dep, waitsOn := none }],
                   nextId := w.nextId + 1 } := by
  have hz : contrib T V w.results
      { id := w.nextId, pred := sg, signer := sg, recv := rv, action := .call c dep, waitsOn := none } = 0 := by
    rw [contrib_call]; cases c <;> simp [hsT, hsV]
  have hnb : ¬ bearing T V ({ id := w.nextId, pred := sg, signer := sg, recv := rv, action := .call c dep, waitsOn := none } : GR α) := by
    simp only [bearing, resAmt, awAmt]; cases c <;> simp [hsT, hsV]
  refine ⟨submit_inv hJ.inv sg rv c dep hsT hsV, ?_, hJ.keys, ?_, ?_, ?_, ?_, ?_⟩
  · show w.app.ft.get V ≤ w.app.ledger.total + ((w.pending ++ _).map (contrib T V w.results)).sum
    rw [List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hz]
    have := hJ.lower; unfold pot at this; omega
  · intro q hq d hw hl
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨h1, h2⟩ := hJ.pairE q h d hw hl
      exact ⟨fun a ha => let ⟨s, hs, x⟩ := h1 a ha; ⟨s, List.mem_append_left _ hs, x⟩,
             fun a ha => let ⟨s, hs, x⟩ := h2 a ha; ⟨s, List.mem_append_left _ hs, x⟩⟩
    · simp at h; subst h; cases hw
  · intro q1 h1 q2 h2 b1 b2
    rcases List.mem_append.mp h1 with h1 | h1
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact hJ.uniq q1 h1 q2 h2 b1 b2
      · simp at h2; subst h2; exact absurd b2 hnb
    · simp at h1; subst h1; exact absurd b1 hnb
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.resSender q h h1
    · simp at h; subst h; exact absurd h1 hsT
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noDonation q h h1
    · simp at h; subst h; intro a d e; simp at e; exact hdon h1 a e.1
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noVwithdraw q h h1
    · simp at h; subst h; exact absurd h1 hsV


/-! ## Success worlds -/

theorem J_okVal {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {dep : Nat} {s : St α}
    {es : List (Emit α (Call α))} {v : Val} (hwf : emitsWellFormed es = true)
    (hI : Inv T V (okVal w r dep s es v))
    (hlower : s.ft.get V ≤ s.ledger.total + pot T V (okVal w r dep s es v))
    (hkeys : (s.ledger.map (·.1)).Nodup)
    (hE : ∀ q ∈ mkReceipts r w.nextId es, ∀ d, q.waitsOn = some d →
      (∀ a, resAmt T V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = d ∧ depSrc T V x = some a) ∧
      (∀ a, awAmt V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = d ∧ wdSrc T V x = some a))
    (hU : ∀ q1 ∈ mkReceipts r w.nextId es, ∀ q2 ∈ mkReceipts r w.nextId es, bearing T V q1 → bearing T V q2 →
      ∀ d, q1.waitsOn = some d → q2.waitsOn = some d → q1.id = q2.id)
    (hRS : ∀ q ∈ mkReceipts r w.nextId es, q.pred = T → q.recv = T →
      ∀ s rcv a d, q.action = .call (.ft_resolve_transfer s rcv a) d → s ≠ V)
    (hND : ∀ q ∈ mkReceipts r w.nextId es, q.recv = T → ∀ a d, q.action ≠ .call (.ft_transfer V a) d)
    (hNW : ∀ q ∈ mkReceipts r w.nextId es, q.pred = V → ∀ a d, q.action ≠ .call (.withdraw a) d) :
    J T V (okVal w r dep s es v) := by
  have hunr := hJ.inv.unres r hr
  refine ⟨hI, hlower, hkeys, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq d hw hl
    change lookupResult ((r.id, .ok v) :: w.results) d = none at hl
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨hm, _⟩ := mem_removePending.mp h
      have hdr : d ≠ r.id := fun e => by rw [e, lookupResult_cons, if_pos rfl] at hl; cases hl
      rw [lookupResult_cons, if_neg (Ne.symm hdr)] at hl
      obtain ⟨h1, h2⟩ := hJ.pairE q hm d hw hl
      constructor
      · intro a ha; obtain ⟨x, hx, hxid, hxd⟩ := h1 a ha
        exact ⟨x, List.mem_append_left _ (mem_removePending.mpr ⟨hx, hxid ▸ hdr⟩), hxid, hxd⟩
      · intro a ha; obtain ⟨x, hx, hxid, hxd⟩ := h2 a ha
        exact ⟨x, List.mem_append_left _ (mem_removePending.mpr ⟨hx, hxid ▸ hdr⟩), hxid, hxd⟩
    · obtain ⟨h1, h2⟩ := hE q h d hw
      exact ⟨fun a ha => let ⟨x, hx, y⟩ := h1 a ha; ⟨x, List.mem_append_right _ hx, y⟩,
             fun a ha => let ⟨x, hx, y⟩ := h2 a ha; ⟨x, List.mem_append_right _ hx, y⟩⟩
  · intro q1 h1 q2 h2 b1 b2 d w1 w2
    rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
    · exact hJ.uniq q1 (mem_removePending.mp h1).1 q2 (mem_removePending.mp h2).1 b1 b2 d w1 w2
    · have := hJ.inv.waitLt q1 (mem_removePending.mp h1).1 d w1
      have := (mk_wait hwf h2 d w2).1; omega
    · have := hJ.inv.waitLt q2 (mem_removePending.mp h2).1 d w2
      have := (mk_wait hwf h1 d w1).1; omega
    · exact hU q1 h1 q2 h2 b1 b2 d w1 w2
  · intro q hq h1 h2
    rcases List.mem_append.mp hq with h | h
    · exact hJ.resSender q (mem_removePending.mp h).1 h1 h2
    · exact hRS q h h1 h2
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noDonation q (mem_removePending.mp h).1 h1
    · exact hND q h h1
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hJ.noVwithdraw q (mem_removePending.mp h).1 h1
    · exact hNW q h h1

theorem bearing_redirect (rid new : Nat) (q : GR α) : bearing T V (redirect rid new q) ↔ bearing T V q := by
  simp [bearing, resAmt_redirect, awAmt_redirect]

theorem J_okProm {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {dep : Nat} {s : St α}
    {es : List (Emit α (Call α))} {idx : Nat} (hwf : emitsWellFormed es = true) (hidx : idx < es.length)
    (hI : Inv T V (okProm w r dep s es idx))
    (hlower : s.ft.get V ≤ s.ledger.total + pot T V (okProm w r dep s es idx))
    (hkeys : (s.ledger.map (·.1)).Nodup)
    (hredir : ∀ q ∈ w.pending, q.waitsOn = some r.id →
      (∀ a, resAmt T V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = w.nextId + idx ∧ depSrc T V x = some a) ∧
      (∀ a, awAmt V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = w.nextId + idx ∧ wdSrc T V x = some a))
    (hE : ∀ q ∈ mkReceipts r w.nextId es, ∀ d, q.waitsOn = some d →
      (∀ a, resAmt T V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = d ∧ depSrc T V x = some a) ∧
      (∀ a, awAmt V q = some a → ∃ x ∈ mkReceipts r w.nextId es, x.id = d ∧ wdSrc T V x = some a))
    (hU : ∀ q1 ∈ mkReceipts r w.nextId es, ∀ q2 ∈ mkReceipts r w.nextId es, bearing T V q1 → bearing T V q2 →
      ∀ d, q1.waitsOn = some d → q2.waitsOn = some d → q1.id = q2.id)
    (hU2 : ∀ q ∈ mkReceipts r w.nextId es, bearing T V q → q.waitsOn ≠ some (w.nextId + idx))
    (hRS : ∀ q ∈ mkReceipts r w.nextId es, q.pred = T → q.recv = T →
      ∀ s rcv a d, q.action = .call (.ft_resolve_transfer s rcv a) d → s ≠ V)
    (hND : ∀ q ∈ mkReceipts r w.nextId es, q.recv = T → ∀ a d, q.action ≠ .call (.ft_transfer V a) d)
    (hNW : ∀ q ∈ mkReceipts r w.nextId es, q.pred = V → ∀ a d, q.action ≠ .call (.withdraw a) d) :
    J T V (okProm w r dep s es idx) := by
  have hunr := hJ.inv.unres r hr
  refine ⟨hI, hlower, hkeys, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq d hw hl
    change lookupResult w.results d = none at hl
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      obtain ⟨hm, _⟩ := mem_removePending.mp hq0
      by_cases hwr : q0.waitsOn = some r.id
      · -- redirected
        have hd : d = w.nextId + idx := by
          unfold redirect at hw; rw [if_pos hwr] at hw; exact (Option.some.inj hw).symm
        subst hd
        obtain ⟨h1, h2⟩ := hredir q0 hm hwr
        rw [resAmt_redirect, awAmt_redirect]
        exact ⟨fun a ha => let ⟨x, hx, y⟩ := h1 a ha; ⟨x, List.mem_append_right _ hx, y⟩,
               fun a ha => let ⟨x, hx, y⟩ := h2 a ha; ⟨x, List.mem_append_right _ hx, y⟩⟩
      · rw [redirect_same _ _ _ hwr] at hw ⊢
        obtain ⟨h1, h2⟩ := hJ.pairE q0 hm d hw hl
        have hdr : d ≠ r.id := fun e => hwr (e ▸ hw)
        have lift : ∀ x ∈ w.pending, x.id = d →
            redirect r.id (w.nextId + idx) x ∈ (okProm w r dep s es idx).pending ∧
            (redirect r.id (w.nextId + idx) x).id = d := fun x hx hxid =>
          ⟨List.mem_append_left _ (List.mem_map.mpr ⟨x, mem_removePending.mpr ⟨hx, hxid ▸ hdr⟩, rfl⟩),
           by rw [redirect_id]; exact hxid⟩
        constructor
        · intro a ha; obtain ⟨x, hx, hxid, hxd⟩ := h1 a ha
          exact ⟨_, (lift x hx hxid).1, (lift x hx hxid).2, by rw [depSrc_redirect]; exact hxd⟩
        · intro a ha; obtain ⟨x, hx, hxid, hxd⟩ := h2 a ha
          exact ⟨_, (lift x hx hxid).1, (lift x hx hxid).2, by rw [wdSrc_redirect]; exact hxd⟩
    · obtain ⟨h1, h2⟩ := hE q h d hw
      exact ⟨fun a ha => let ⟨x, hx, y⟩ := h1 a ha; ⟨x, List.mem_append_right _ hx, y⟩,
             fun a ha => let ⟨x, hx, y⟩ := h2 a ha; ⟨x, List.mem_append_right _ hx, y⟩⟩
  · -- uniqueness
    have old_wait : ∀ q0 ∈ removePending w.pending r.id, ∀ d,
        (redirect r.id (w.nextId + idx) q0).waitsOn = some d →
        (q0.waitsOn = some r.id ∧ d = w.nextId + idx) ∨ (q0.waitsOn = some d ∧ d < w.nextId) := by
      intro q0 hq0 d hw
      unfold redirect at hw
      split at hw
      · exact Or.inl ⟨by assumption, (Option.some.inj hw).symm⟩
      · exact Or.inr ⟨hw, hJ.inv.waitLt q0 (mem_removePending.mp hq0).1 d hw⟩
    intro q1 h1 q2 h2 b1 b2 d w1 w2
    rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
    · obtain ⟨p1, hp1, rfl⟩ := List.mem_map.mp h1
      obtain ⟨p2, hp2, rfl⟩ := List.mem_map.mp h2
      rw [bearing_redirect] at b1 b2
      rw [redirect_id, redirect_id]
      rcases old_wait p1 hp1 d w1 with ⟨e1, d1⟩ | ⟨e1, d1⟩ <;>
        rcases old_wait p2 hp2 d w2 with ⟨e2, d2⟩ | ⟨e2, d2⟩
      · exact hJ.uniq p1 (mem_removePending.mp hp1).1 p2 (mem_removePending.mp hp2).1 b1 b2 r.id e1 e2
      · omega
      · omega
      · exact hJ.uniq p1 (mem_removePending.mp hp1).1 p2 (mem_removePending.mp hp2).1 b1 b2 d e1 e2
    · obtain ⟨p1, hp1, rfl⟩ := List.mem_map.mp h1
      have hb := (mk_wait hwf h2 d w2).1
      rcases old_wait p1 hp1 d w1 with ⟨_, d1⟩ | ⟨_, d1⟩
      · subst d1; exact absurd w2 (hU2 q2 h2 b2)
      · omega
    · obtain ⟨p2, hp2, rfl⟩ := List.mem_map.mp h2
      have hb := (mk_wait hwf h1 d w1).1
      rcases old_wait p2 hp2 d w2 with ⟨_, d2⟩ | ⟨_, d2⟩
      · subst d2; exact absurd w1 (hU2 q1 h1 b1)
      · omega
    · exact hU q1 h1 q2 h2 b1 b2 d w1 w2
  · intro q hq h1 h2
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_pred] at h1; rw [redirect_recv] at h2
      intro s' rcv a d e; rw [redirect_action] at e
      exact hJ.resSender q0 (mem_removePending.mp hq0).1 h1 h2 s' rcv a d e
    · exact hRS q h h1 h2
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_recv] at h1; intro a d; rw [redirect_action]
      exact hJ.noDonation q0 (mem_removePending.mp hq0).1 h1 a d
    · exact hND q h h1
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp h
      rw [redirect_pred] at h1; intro a d; rw [redirect_action]
      exact hJ.noVwithdraw q0 (mem_removePending.mp hq0).1 h1 a d
    · exact hNW q h h1

/-- A bearing waiter of `r` exists only if `r` is a source; and then its amount equals `r`'s. -/
theorem waiter_amount {w : GW α} (hJ : J T V w) {r : GR α} (hr : r ∈ w.pending)
    {q : GR α} (hq : q ∈ w.pending) (hw : q.waitsOn = some r.id) :
    (∀ a, resAmt T V q = some a → depSrc T V r = some a) ∧ (∀ a, awAmt V q = some a → wdSrc T V r = some a) := by
  have hunr := hJ.inv.unres r hr
  obtain ⟨h1, h2⟩ := hJ.pairE q hq r.id hw hunr
  constructor
  · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h1 a ha
    have := eq_of_id hJ.inv.nodup hs hr hsid; subst this; exact hsd
  · intro a ha; obtain ⟨s, hs, hsid, hsd⟩ := h2 a ha
    have := eq_of_id hJ.inv.nodup hs hr hsid; subst this; exact hsd

end NearAsync.Vault.Proof
