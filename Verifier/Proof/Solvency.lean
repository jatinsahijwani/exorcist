import Verifier.Proof.Ok

/-!
# The fixed vault is solvent in every reachable state — for all traces

`fixed_vault_solvent_forever`: for any account type, any token/vault accounts `T ≠ V`, any code
on all other accounts (which cannot write token/vault storage), any set of receipts the adversary
may fail, any transactions from non-contract accounts with any arguments and amounts, and any
initial state with nothing in flight and a backed ledger: every state reached by any finite trace
satisfies `Σ ledger ≤ token balance of the vault`.

Proof: `Inv` (see `Defs.lean`) holds initially and is preserved by every step.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

/-! ## Small facts -/

theorem contrib_of_res {res : List (Nat × PResult)} {q : GR α} {a : Nat} (h : resAmt T V q = some a) :
    contrib T V res q = resPot res q.waitsOn a := by
  simp [contrib, h]

theorem resAmt_none_of_aw {q : GR α} {a : Nat} (h : awAmt V q = some a) : resAmt T V q = none := by
  unfold awAmt at h; unfold resAmt
  split at h <;> simp_all

theorem contrib_of_aw {res : List (Nat × PResult)} {q : GR α} {a : Nat} (h : awAmt V q = some a) :
    contrib T V res q = awPot res q.waitsOn a := by
  simp [contrib, resAmt_none_of_aw (T := T) h, h]

theorem sum_zero {β : Type} (l : List β) (f : β → Nat) (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `contrib` of a literal call receipt. -/
theorem contrib_call (res : List (Nat × PResult)) (i : Nat) (p sg rv : α) (c : Call α) (d : Nat)
    (ws : Option Nat) :
    contrib T V res { id := i, pred := p, signer := sg, recv := rv, action := .call c d, waitsOn := ws } =
      match c with
      | .ft_resolve_transfer _ rcv a => if rv = T ∧ p = T ∧ rcv = V then resPot res ws a else 0
      | .after_withdraw _ a => if rv = V ∧ p = V then awPot res ws a else 0
      | _ => 0 := by
  cases c <;> simp only [contrib, resAmt, awAmt] <;> (repeat' split) <;> simp_all

theorem readiness_input {w : GW α} {r : GR α} {x : PResult} (h : readiness w r = some (some x)) :
    ∃ d, r.waitsOn = some d ∧ lookupResult w.results d = some x := by
  unfold readiness at h
  cases hw : r.waitsOn with
  | none => rw [hw] at h; simp at h
  | some d =>
    rw [hw] at h; simp at h
    exact ⟨d, rfl, h⟩

theorem readiness_none_input {w : GW α} {r : GR α} (h : readiness w r = some none) : r.waitsOn = none := by
  unfold readiness at h
  cases hw : r.waitsOn with
  | none => rfl
  | some d => rw [hw] at h; simp at h

/-- Contribution of a receipt with no `resolve`/`after_withdraw` shape is zero. -/
theorem contrib_zero {res : List (Nat × PResult)} {q : GR α}
    (h1 : resAmt T V q = none) (h2 : awAmt V q = none) : contrib T V res q = 0 := by
  simp [contrib, h1, h2]

theorem pot_okVal (w : GW α) (r : GR α) (dep : Nat) (s : St α) (es : List (Emit α (Call α))) (v : Val) :
    pot T V (okVal w r dep s es v) =
      ((removePending w.pending r.id).map (contrib T V ((r.id, .ok v) :: w.results))).sum +
      ((mkReceipts r w.nextId es).map (contrib T V ((r.id, .ok v) :: w.results))).sum := by
  simp [pot, okVal, List.map_append, List.sum_append]

theorem pot_okProm (w : GW α) (r : GR α) (dep : Nat) (s : St α) (es : List (Emit α (Call α))) (idx : Nat) :
    pot T V (okProm w r dep s es idx) =
      (((removePending w.pending r.id).map (redirect r.id (w.nextId + idx))).map (contrib T V w.results)).sum +
      ((mkReceipts r w.nextId es).map (contrib T V w.results)).sum := by
  simp [pot, okProm, List.map_append, List.sum_append]

/-- Remaining potential, with a decrease of `a'` at a paired waiter `R` of `r`. -/
theorem pot_rest_dec {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) (x : PResult)
    {R : GR α} (hR : R ∈ w.pending) (hw : R.waitsOn = some r.id) (a' : Nat)
    (hdec : contrib T V ((r.id, x) :: w.results) R + a' ≤ contrib T V w.results R) :
    ((removePending w.pending r.id).map (contrib T V ((r.id, x) :: w.results))).sum + a' +
      contrib T V w.results r ≤ pot T V w := by
  have hagree := agree_cons w.results r.id x (hI.unres r hr)
  have h1 := sum_removePending w.pending (contrib T V w.results) hI.nodup r hr
  have h2 := sum_map_le_dec (removePending w.pending r.id) (contrib T V ((r.id, x) :: w.results))
    (contrib T V w.results) (fun q _ => contrib_mono _ _ hagree q) R (mem_rest hI hr hrd hr hR hw) a' hdec
  unfold pot; omega

theorem sum_redirect (res : List (Nat × PResult)) (ps : List (GR α)) (rid new : Nat)
    (h1 : lookupResult res rid = none) (h2 : lookupResult res new = none) :
    ((ps.map (redirect rid new)).map (contrib T V res)).sum = (ps.map (contrib T V res)).sum := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact contrib_redirect res rid new h1 h2 q

theorem lookup_ok_self (res : List (Nat × PResult)) (k : Nat) (x : PResult) :
    lookupResult ((k, x) :: res) k = some x := by simp [lookupResult]

/-! ## The ok cases -/

section cases

variable (cfg : Config) (other : α → Handler α) (cf : GR α → Bool)

/-- Context of a receipt execution. -/
abbrev ctxOf (r : GR α) (dep : Nat) (inp : Option PResult) : Ctx α :=
  { self := r.recv, pred := r.pred, signer := r.signer, deposit := dep, input := inp }

theorem other_news {r : GR α} (hT : r.recv ≠ T) (hV : r.recv ≠ V) (base : Nat) (es : List (Emit α (Call α)))
    (res : List (Nat × PResult)) :
    ((mkReceipts r base es).map (contrib T V res)).sum = 0 ∧
    ∀ q ∈ mkReceipts r base es, depSrc T V q = none ∧ wdSrc T V q = none ∧ q.pred ≠ V := by
  have hp : ∀ q ∈ mkReceipts r base es, q.pred = r.recv := fun q hq => mk_pred hq
  constructor
  · have : ∀ q ∈ mkReceipts r base es, contrib T V res q = 0 := by
      intro q hq
      apply contrib_zero
      · unfold resAmt; split <;> simp_all [hp q hq]
      · unfold awAmt; split <;> simp_all [hp q hq]
    exact sum_zero _ _ this
  · intro q hq
    have := hp q hq
    refine ⟨?_, ?_, by rw [this]; exact hV⟩
    · unfold depSrc; split <;> simp_all
    · unfold wdSrc; split <;> simp_all

/-- Value-returning executions preserve the invariant. -/
theorem val_case (hfix : cfg.depositFixed = true) (hframe : Frame other) (hTV : T ≠ V)
    {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) {s : St α} {es : List (Emit α (Call α))} {v : Val}
    (hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app = .ok s es (.val v))
    (hwf : emitsWellFormed es = true) :
    Inv T V (okVal w r dep s es v) := by
  have hb := hI.bal
  have hagree := agree_cons w.results r.id (.ok v) (hI.unres r hr)
  have hrest := pot_rest_le hI hr _ hagree
  have hunr := hI.unres r hr
  have hfreshres := res_cons_lt hI hr (.ok v)
  simp only [gsys] at hd
  by_cases hT : r.recv = T
  · ----------------------------------------------------------------- token
    rw [if_pos hT] at hd
    cases c with
    | ft_transfer to a =>
      simp only [tokenHandle, ftHandle] at hd
      split at hd; · simp at hd
      split at hd; · simp at hd
      split at hd; · simp at hd
      split at hd; · simp at hd
      rename_i hlt; simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      apply okVal_inv hI hr hrd hwf
      · rw [pot_okVal]
        simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
        simp only [Bal.get_add, Bal.get_sub]
        by_cases hp : r.pred = V
        · have hsrc : wdSrc T V r = some a := by simp [wdSrc, hact, hT, hp]
          obtain ⟨q, hq, hw, a', haw, hle⟩ := hI.pairWd r hr a hsrc
          have hdec : contrib T V ((r.id, .ok .unit) :: w.results) q + a' ≤ contrib T V w.results q := by
            rw [contrib_of_aw haw, contrib_of_aw haw, hw]
            simp [awPot, lookup_ok_self, hunr]
          have := pot_rest_dec hI hr hrd (.ok .unit) hq hw a' hdec
          have hto : to ≠ V := fun e => by simp_all
          simp only [hp, hto, if_true, if_false]
          simp only [ctxOf, hp] at hlt
          omega
        · simp only [hp, if_false]
          split <;> omega
      · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
    | ft_resolve_transfer sd rcv a =>
      simp only [tokenHandle, ftHandle] at hd
      split at hd; · simp at hd
      rename_i hpriv
      obtain ⟨x, rfl⟩ : ∃ x, inp = some x := by
        cases inp with
        | none => simp [ctxOf] at hd
        | some x => exact ⟨x, rfl⟩
      simp only [ctxOf] at hd hpriv
      have ⟨d, hwd, hlk⟩ := readiness_input hrd
      have hpT : r.pred = T := by simp at hpriv; rw [hpriv, hT]
      split at hd
      · rename_i hcond
        simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        apply okVal_inv hI hr hrd hwf
        · rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          simp only [Bal.get_add, Bal.get_sub]
          by_cases hrcv : rcv = V
          · have hres : resAmt T V r = some a := by simp [resAmt, hact, hT, hpT, hrcv]
            have hc : contrib T V w.results r = unusedAmount x a := by
              rw [contrib_of_res hres, hwd]; simp [resPot, hlk]
            rw [hrcv] at hcond hrest ⊢
            have hmin : min (w.app.ft.get V) (unusedAmount x a) ≤ unusedAmount x a := Nat.min_le_right _ _
            have hmin2 : min (w.app.ft.get V) (unusedAmount x a) ≤ w.app.ft.get V := Nat.min_le_left _ _
            simp only [if_true]
            split <;> omega
          · simp only [hrcv, if_false]
            split <;> omega
        · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
      · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        apply okVal_inv hI hr hrd hwf
        · rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          omega
        · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
    | ft_transfer_call to a m =>
      revert hd; simp only [tokenHandle, ftHandle]; repeat' split
      all_goals (intro h; simp at h)
    | _ => simp [tokenHandle, ftHandle] at hd
  · rw [if_neg hT] at hd
    by_cases hV : r.recv = V
    · --------------------------------------------------------------- vault
      rw [if_pos hV] at hd
      cases c with
      | ft_on_transfer sd a msg =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpT; simp only [ctxOf, ne_eq, Decidable.not_not] at hpT
        cases msg with
        | plain =>
          simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hsrc : depSrc T V r = some a := by simp [depSrc, hact, hV, hpT]
          obtain ⟨R, hR, hw, a', hra, hle⟩ := hI.pairDep r hr a hsrc
          have hdec : contrib T V ((r.id, .ok (.nat 0)) :: w.results) R + a' ≤ contrib T V w.results R := by
            rw [contrib_of_res hra, contrib_of_res hra, hw]
            simp [resPot, lookup_ok_self, hunr, unusedOf, unusedAmount]
          have := pot_rest_dec hI hr hrd (.ok (.nat 0)) hR hw a' hdec
          apply okVal_inv hI hr hrd hwf
          · rw [pot_okVal]
            simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
            have := Bal.total_add_le w.app.ledger sd a
            omega
          · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
        | notify h =>
          simp only [hfix, if_true] at hd
          simp at hd
      | after_notify who a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpV; simp only [ctxOf, ne_eq, Decidable.not_not] at hpV
        split at hd
        · rename_i y hinp
          simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hsrc : depSrc T V r = some a := by simp [depSrc, hact, hV, hpV]
          obtain ⟨R, hR, hw, a', hra, hle⟩ := hI.pairDep r hr a hsrc
          have hdec : contrib T V ((r.id, .ok (.nat 0)) :: w.results) R + a' ≤ contrib T V w.results R := by
            rw [contrib_of_res hra, contrib_of_res hra, hw]
            simp [resPot, lookup_ok_self, hunr, unusedOf, unusedAmount]
          have := pot_rest_dec hI hr hrd (.ok (.nat 0)) hR hw a' hdec
          apply okVal_inv hI hr hrd hwf
          · rw [pot_okVal]
            simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
            have := Bal.total_add_le w.app.ledger who a
            omega
          · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
        · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          apply okVal_inv hI hr hrd hwf
          · rw [pot_okVal]
            simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
            omega
          · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
        · simp at hd
      | withdraw a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        split at hd; · simp at hd
        rename_i hge
        simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        try simp only [ctxOf] at hge
        have hge' : a ≤ w.app.ledger.get r.pred := by omega
        have hsub := Bal.total_sub_le w.app.ledger r.pred a hge'
        have hlt1 : r.id < w.nextId := hI.idLt r hr
        apply okVal_inv hI hr hrd hwf
        · rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil]
          have hf : lookupResult ((r.id, PResult.ok Val.unit) :: w.results) w.nextId = none :=
            fresh_none hI _ hfreshres (Nat.le_refl _)
          simp only [contrib_call, hV, and_self, if_true, awPot, Option.map, Nat.add_zero, hf]
          simp only [hTV.symm, false_and, if_false, Nat.zero_add]
          omega
        · refine ⟨?_, ?_, ?_⟩
          · intro o ho a0 ha0
            simp [mkReceipts] at ho
            rcases ho with rfl | rfl <;> simp [depSrc] at ha0
          · intro t ht a0 ha0
            simp [mkReceipts] at ht
            rcases ht with rfl | rfl
            · simp [wdSrc, hV] at ha0
              subst ha0
              refine ⟨_, List.mem_append_right _ (by simp [mkReceipts]; exact Or.inr rfl), rfl, a, ?_, Nat.le_refl _⟩
              simp [awAmt, hV]
            · simp [wdSrc] at ha0
          · intro q hq h1 h2 to a0 m d0
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl
            · simp
            · simp at h2; exact absurd (hV ▸ h2) hTV.symm
      | after_withdraw who a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpV; simp only [ctxOf, ne_eq, Decidable.not_not] at hpV
        rcases inp with _ | ⟨y | _⟩
        · simp at hd
        · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          apply okVal_inv hI hr hrd hwf
          · rw [pot_okVal]
            simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
            omega
          · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
        · have ⟨d, hwd, hlk⟩ := readiness_input hrd
          have haw : awAmt V r = some a := by simp [awAmt, hact, hV, hpV]
          have hc : contrib T V w.results r = a := by
            rw [contrib_of_aw haw, hwd]; simp [awPot, hlk]
          simp only at hd
          split at hd
          · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
            obtain ⟨rfl, rfl, rfl⟩ := hd
            apply okVal_inv hI hr hrd hwf
            · rw [pot_okVal]
              simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
              have := Bal.total_add_le w.app.ledger who a
              omega
            · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
          · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
            obtain ⟨rfl, rfl, rfl⟩ := hd
            apply okVal_inv hI hr hrd hwf
            · rw [pot_okVal]
              simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
              omega
            · exact ⟨by simp [mkReceipts], by simp [mkReceipts], by simp [mkReceipts]⟩
      | _ => simp [vaultHandle] at hd
    · --------------------------------------------------------------- other code
      rw [if_neg hV] at hd
      have hs := hframe _ _ _ _ _ _ _ hd
      subst hs
      obtain ⟨hz, hq⟩ := other_news hT hV w.nextId es ((r.id, .ok v) :: w.results)
      apply okVal_inv hI hr hrd hwf
      · rw [pot_okVal, hz]; omega
      · refine ⟨?_, ?_, ?_⟩
        · intro o ho a ha; rw [(hq o ho).1] at ha; cases ha
        · intro t ht a ha; rw [(hq t ht).2.1] at ha; cases ha
        · intro q' hq' h1; exact absurd h1 (hq q' hq').2.2

/-- Promise-returning executions preserve the invariant. -/
theorem prom_case (hfix : cfg.depositFixed = true) (hframe : Frame other) (hTV : T ≠ V)
    {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) {s : St α} {es : List (Emit α (Call α))} {idx : Nat}
    (hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app = .ok s es (.promise idx))
    (hwf : emitsWellFormed es = true) (hidx : idx < es.length) :
    Inv T V (okProm w r dep s es idx) := by
  have hb := hI.bal
  have hunr := hI.unres r hr
  have hrid := hI.idLt r hr
  have hfresh : lookupResult w.results (w.nextId + idx) = none :=
    fresh_none hI _ hI.resLt (by omega)
  have hsr := sum_redirect (T := T) (V := V) w.results (removePending w.pending r.id) r.id (w.nextId + idx) hunr hfresh
  have h1 := sum_removePending w.pending (contrib T V w.results) hI.nodup r hr
  simp only [gsys] at hd
  by_cases hT : r.recv = T
  · rw [if_pos hT] at hd
    cases c with
    | ft_transfer_call to a m =>
      simp only [tokenHandle, ftHandle] at hd
      split at hd; · simp at hd
      split at hd; · simp at hd
      rename_i hne
      split at hd; · simp at hd
      split at hd; · simp at hd
      simp only [Outcome.ok.injEq, Ret.promise.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      have hpV : r.pred ≠ V := fun e => hI.noVcall r hr e hT to a m dep hact
      try simp only [ctxOf] at hne
      have hb1 : w.nextId + 1 ≥ w.nextId := by omega
      have hf0 : lookupResult w.results (w.nextId + 0) = none := fresh_none hI _ hI.resLt (by omega)
      apply okProm_inv hI hr hrd hwf hidx
      · rw [pot_okProm, hsr]
        simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, ctxOf]
        simp only [Bal.get_add, Bal.get_sub, hpV, if_false]
        have hf0' : lookupResult w.results w.nextId = none := fresh_none hI _ hI.resLt (Nat.le_refl _)
        simp only [contrib_call, hT, and_self, true_and, resPot, Option.map, Nat.add_zero, hf0']
        unfold pot at hb
        by_cases hto : to = V
        · simp only [hto, if_true]; omega
        · simp only [hto, if_false]; omega
      · refine ⟨?_, ?_, ?_⟩
        · intro o ho a0 ha0
          simp [mkReceipts] at ho
          rcases ho with rfl | rfl
          · simp only [depSrc] at ha0
            split at ha0
            · rename_i hc
              obtain ⟨hto, _⟩ := hc
              simp at ha0; subst ha0
              refine ⟨_, List.mem_append_right _ (by simp [mkReceipts]; exact Or.inr rfl), rfl, a, ?_, Nat.le_refl _⟩
              simp [resAmt, hT, hto]
            · cases ha0
          · simp [depSrc] at ha0
        · intro t ht a0 ha0
          simp [mkReceipts] at ht
          rcases ht with rfl | rfl <;> simp [wdSrc] at ha0
        · intro q hq h1 h2 to' a0 m0 d0
          simp [mkReceipts] at hq
          rcases hq with rfl | rfl <;> (try simp only at h1) <;> exact absurd (hT ▸ h1) hTV
    | ft_transfer to a =>
      revert hd; simp only [tokenHandle, ftHandle]; repeat' split
      all_goals (intro h; simp at h)
    | ft_resolve_transfer sd rcv a =>
      revert hd; simp only [tokenHandle, ftHandle]; repeat' split
      all_goals (intro h; simp at h)
    | _ => simp [tokenHandle, ftHandle] at hd
  · rw [if_neg hT] at hd
    by_cases hV : r.recv = V
    · rw [if_pos hV] at hd
      cases c with
      | ft_on_transfer sd a msg =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpT; simp only [ctxOf, ne_eq, Decidable.not_not] at hpT
        cases msg with
        | plain => simp at hd
        | notify h =>
          simp only [hfix, if_true, Outcome.ok.injEq, Ret.promise.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hsrc : depSrc T V r = some a := by simp [depSrc, hact, hV, hpT]
          obtain ⟨R, hR, hw, a', hra, hle⟩ := hI.pairDep r hr a hsrc
          have hRr := mem_rest hI hr hrd hr hR hw
          apply okProm_inv hI hr hrd hwf hidx
          · rw [pot_okProm, hsr]
            simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, ctxOf]
            simp only [contrib_call]
            unfold pot at hb; omega
          · refine ⟨?_, ?_, ?_⟩
            · intro o ho a0 ha0
              simp [mkReceipts] at ho
              rcases ho with rfl | rfl
              · simp [depSrc] at ha0
              · simp [depSrc, hV] at ha0
                subst ha0
                refine ⟨redirect r.id (w.nextId + 1) R,
                  List.mem_append_left _ (List.mem_map.mpr ⟨R, hRr, rfl⟩), ?_, a', ?_, hle⟩
                · simp [redirect, hw]
                · rw [resAmt_redirect]; exact hra
            · intro t ht a0 ha0
              simp [mkReceipts] at ht
              rcases ht with rfl | rfl <;> simp [wdSrc] at ha0
            · intro q hq h1 h2 to' a0 m0 d0
              simp [mkReceipts] at hq
              rcases hq with rfl | rfl
              · simp
              · simp at h2; exact absurd (hV ▸ h2) hTV.symm
      | after_notify who a =>
        revert hd; simp only [vaultHandle]; repeat' split
        all_goals (intro h; simp at h)
      | withdraw a =>
        revert hd; simp only [vaultHandle]; repeat' split
        all_goals (intro h; simp at h)
      | after_withdraw who a =>
        revert hd; simp only [vaultHandle]; repeat' split
        all_goals (intro h; simp at h)
      | _ => simp [vaultHandle] at hd
    · rw [if_neg hV] at hd
      have hs := hframe _ _ _ _ _ _ _ hd
      subst hs
      obtain ⟨hz, hq⟩ := other_news hT hV w.nextId es w.results
      apply okProm_inv hI hr hrd hwf hidx
      · rw [pot_okProm, hsr, hz]; unfold pot at hb; omega
      · refine ⟨?_, ?_, ?_⟩
        · intro o ho a ha; rw [(hq o ho).1] at ha; cases ha
        · intro t ht a ha; rw [(hq t ht).2.1] at ha; cases ha
        · intro q' hq' h1; exact absurd h1 (hq q' hq').2.2

end cases

end NearAsync.Vault.Proof
