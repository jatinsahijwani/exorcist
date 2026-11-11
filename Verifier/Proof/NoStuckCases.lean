import Verifier.Proof.NoStuck

/-!
# No stuck funds — per-method cases and the headline theorem

`fixed_vault_no_stuck_funds`: with the fixed vault (both fixes), only non-callback receipts failing,
no plain `ft_transfer` to the vault, and an exact initial ledger, every reachable state satisfies
`tokens held by V ≤ Σ ledger + pot`; in particular, whenever nothing is in flight, every token the
vault holds is owed to someone (`tokens held = Σ ledger`, together with solvency).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 4000000

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

theorem mem_of_mem_zipIdx' {β : Type} {l : List β} {n : Nat} {x : β} {i : Nat} (h : (x, i) ∈ l.zipIdx n) : x ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons y t ih =>
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.mp h with e | e
    · simp at e; rw [e.1]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih e)

section cases
variable (cfg : Config) (other : α → Handler α) (cf : GR α → Bool)

theorem bearing_amt {q : GR α} (h : bearing T V q) : (∃ a, resAmt T V q = some a) ∨ (∃ a, awAmt V q = some a) := by
  unfold bearing at h
  rcases h with h | h
  · left; cases e : resAmt T V q <;> simp_all
  · right; cases e : awAmt V q <;> simp_all

theorem rest_eq_of_not_src {w : GW α} (hJ : J T V w) {r : GR α} (hr : r ∈ w.pending)
    (hd : depSrc T V r = none) (hwd : wdSrc T V r = none) (x : PResult) :
    ((removePending w.pending r.id).map (contrib T V ((r.id, x) :: w.results))).sum =
      ((removePending w.pending r.id).map (contrib T V w.results)).sum := by
  congr 1
  apply List.map_congr_left
  intro q hq
  exact contrib_rest_eq hJ hr hd hwd x (mem_removePending.mp hq).1

theorem nil_obligations (r : GR α) (base : Nat) :
    (∀ q ∈ mkReceipts r base ([] : List (Emit α (Call α))), ∀ d, q.waitsOn = some d →
      (∀ a, resAmt T V q = some a → ∃ x ∈ mkReceipts r base ([] : List (Emit α (Call α))), x.id = d ∧ depSrc T V x = some a) ∧
      (∀ a, awAmt V q = some a → ∃ x ∈ mkReceipts r base ([] : List (Emit α (Call α))), x.id = d ∧ wdSrc T V x = some a)) ∧
    (∀ q1 ∈ mkReceipts r base ([] : List (Emit α (Call α))), ∀ q2 ∈ mkReceipts r base ([] : List (Emit α (Call α))),
      bearing T V q1 → bearing T V q2 → ∀ d, q1.waitsOn = some d → q2.waitsOn = some d → q1.id = q2.id) ∧
    (∀ q ∈ mkReceipts r base ([] : List (Emit α (Call α))), q.pred = T → q.recv = T →
      ∀ s rcv a d, q.action = .call (.ft_resolve_transfer s rcv a) d → s ≠ V) ∧
    (∀ q ∈ mkReceipts r base ([] : List (Emit α (Call α))), q.recv = T → ∀ a d, q.action ≠ .call (.ft_transfer V a) d) ∧
    (∀ q ∈ mkReceipts r base ([] : List (Emit α (Call α))), q.pred = V → ∀ a d, q.action ≠ .call (.withdraw a) d) := by
  simp [mkReceipts]

theorem J_val_case (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (hframe : Frame other) (hdon : NoDonate T V other) (hTV : T ≠ V)
    {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) {s : St α} {es : List (Emit α (Call α))} {v : Val}
    (hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app = .ok s es (.val v))
    (hwf : emitsWellFormed es = true) :
    J T V (okVal w r dep s es v) := by
  have hI := val_case cfg other cf hfix hframe hTV hJ.inv hr hrd hact hd hwf
  have hunr := hJ.inv.unres r hr
  have hl := hJ.lower
  have hbal := hJ.inv.bal
  have h1 := sum_removePending w.pending (contrib T V w.results) hJ.inv.nodup r hr
  unfold pot at hl hbal
  have hcr : resAmt T V r = none → awAmt V r = none → contrib T V w.results r = 0 := contrib_zero
  simp only [gsys] at hd
  by_cases hT : r.recv = T
  · rw [if_pos hT] at hd
    cases c with
    | ft_transfer to a =>
      simp only [tokenHandle, ftHandle] at hd
      split at hd; · simp at hd
      split at hd; · simp at hd
      rename_i hne
      split at hd; · simp at hd
      split at hd; · simp at hd
      rename_i hlt; simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
      obtain ⟨o1, o2, o3, o4, o5⟩ := nil_obligations (T := T) (V := V) r w.nextId
      apply J_okVal hJ hr hrd hwf hI _ hJ.keys o1 o2 o3 o4 o5
      rw [pot_okVal]
      simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
      simp only [Bal.get_add, Bal.get_sub]
      try simp only [ctxOf] at hne hlt
      by_cases hp : r.pred = V
      · have hge := pot_rest_ge hJ hr (.ok .unit) a (by
          intro q hq hb hw
          obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
          rcases bearing_amt hb with ⟨a', ha'⟩ | ⟨a', ha'⟩
          · have := hres a' ha'; simp [depSrc, hact] at this
          · have := haw a' ha'
            simp [wdSrc, hact, hT, hp] at this; subst this
            rw [contrib_of_aw ha', hw]; simp [awPot, hunr])
        have hto : to ≠ V := fun e => hne (hp.trans e.symm)
        simp only [hp, hto, if_true, if_false]
        omega
      · have hto : to ≠ V := fun e => hJ.noDonation r hr hT a dep (by rw [hact, e])
        have heq := rest_eq_of_not_src hJ hr (by simp [depSrc, hact]) (by simp [wdSrc, hact, hT, hp]) (.ok .unit)
        simp only [hp, hto, if_false]
        omega
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
      have hsd : sd ≠ V := hJ.resSender r hr hpT hT sd rcv a dep hact
      have heq := rest_eq_of_not_src hJ hr (by simp [depSrc, hact]) (by simp [wdSrc, hact])
      obtain ⟨o1, o2, o3, o4, o5⟩ := nil_obligations (T := T) (V := V) r w.nextId
      split at hd
      · rename_i hcond
        simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        apply J_okVal hJ hr hrd hwf hI _ hJ.keys o1 o2 o3 o4 o5
        rw [pot_okVal, heq]
        simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
        rw [Bal.get_add, Bal.get_sub, if_neg hsd]
        by_cases hrcv : rcv = V
        · have hres : resAmt T V r = some a := by simp [resAmt, hact, hT, hpT, hrcv]
          have hc : contrib T V w.results r = unusedAmount x a := by
            rw [contrib_of_res hres, hwd]; simp [resPot, hlk]
          rw [hrcv] at hcond ⊢
          rw [if_pos rfl]
          have hle : unusedAmount x a ≤ w.app.ft.get V := by omega
          rw [Nat.min_eq_right hle]
          omega
        · have hc0 := hcr (by simp [resAmt, hact, hrcv]) (by simp [awAmt, hact])
          rw [if_neg hrcv]
          omega
      · rename_i hcond
        simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        apply J_okVal hJ hr hrd hwf hI _ hJ.keys o1 o2 o3 o4 o5
        rw [pot_okVal, heq]
        simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
        by_cases hrcv : rcv = V
        · have hres : resAmt T V r = some a := by simp [resAmt, hact, hT, hpT, hrcv]
          have hc : contrib T V w.results r = unusedAmount x a := by
            rw [contrib_of_res hres, hwd]; simp [resPot, hlk]
          rw [hrcv] at hcond
          have hle : unusedAmount x a ≤ w.app.ft.get V := by omega
          have : unusedAmount x a = 0 := by
            by_cases h0 : 0 < unusedAmount x a
            · exact absurd ⟨h0, by omega⟩ hcond
            · omega
          omega
        · have hc0 := hcr (by simp [resAmt, hact, hrcv]) (by simp [awAmt, hact])
          omega
    | ft_transfer_call to a m =>
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
        | plain =>
          simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
          obtain ⟨o1, o2, o3, o4, o5⟩ := nil_obligations (T := T) (V := V) r w.nextId
          have hge := pot_rest_ge hJ hr (.ok (.nat 0)) a (by
            intro q hq hb hw
            obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
            rcases bearing_amt hb with ⟨a', ha'⟩ | ⟨a', ha'⟩
            · have := hres a' ha'
              simp [depSrc, hact, hV, hpT] at this; subst this
              rw [contrib_of_res ha', hw]; simp [resPot, hunr]
            · have := haw a' ha'; simp [wdSrc, hact] at this)
          apply J_okVal hJ hr hrd hwf hI _ (keys_add _ _ _ hJ.keys) o1 o2 o3 o4 o5
          rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          rw [total_add_eq _ _ _ hJ.keys]
          omega
        | notify h =>
          simp only [hfix, if_true] at hd
          simp at hd
      | after_notify who a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpV; simp only [ctxOf, ne_eq, Decidable.not_not] at hpV
        have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
        obtain ⟨o1, o2, o3, o4, o5⟩ := nil_obligations (T := T) (V := V) r w.nextId
        rcases inp with _ | ⟨y | _⟩
        · simp at hd
        · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hge := pot_rest_ge hJ hr (.ok (.nat 0)) a (by
            intro q hq hb hw
            obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
            rcases bearing_amt hb with ⟨a', ha'⟩ | ⟨a', ha'⟩
            · have := hres a' ha'
              simp [depSrc, hact, hV, hpV] at this; subst this
              rw [contrib_of_res ha', hw]; simp [resPot, hunr]
            · have := haw a' ha'; simp [wdSrc, hact] at this)
          apply J_okVal hJ hr hrd hwf hI _ (keys_add _ _ _ hJ.keys) o1 o2 o3 o4 o5
          rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          rw [total_add_eq _ _ _ hJ.keys]
          omega
        · simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          have hge := pot_rest_ge hJ hr (.ok (.nat a)) 0 (by
            intro q hq hb hw
            obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
            rcases bearing_amt hb with ⟨a', ha'⟩ | ⟨a', ha'⟩
            · have := hres a' ha'
              simp [depSrc, hact, hV, hpV] at this; subst this
              rw [contrib_of_res ha', contrib_of_res ha', hw]
              simp [resPot, hunr, lookup_ok_self, unusedOf, unusedAmount]
            · have := haw a' ha'; simp [wdSrc, hact] at this)
          apply J_okVal hJ hr hrd hwf hI _ hJ.keys o1 o2 o3 o4 o5
          rw [pot_okVal]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          omega
      | withdraw a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        split at hd; · simp at hd
        rename_i hge
        simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
        obtain ⟨rfl, rfl, rfl⟩ := hd
        have hge' : a ≤ w.app.ledger.get r.pred := by (try simp only [ctxOf] at hge); omega
        have hsub := total_sub_eq w.app.ledger r.pred a hJ.keys hge'
        have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
        have heq := rest_eq_of_not_src hJ hr (by simp [depSrc, hact]) (by simp [wdSrc, hact]) (.ok .unit)
        have hlt1 : r.id < w.nextId := hJ.inv.idLt r hr
        have hpV : r.pred ≠ V := fun e => hJ.noVwithdraw r hr e a dep hact
        have hf : lookupResult ((r.id, PResult.ok Val.unit) :: w.results) w.nextId = none :=
          fresh_none hJ.inv _ (res_cons_lt hJ.inv hr _) (Nat.le_refl _)
        apply J_okVal hJ hr hrd hwf hI _ (keys_sub _ _ _ hJ.keys)
        · intro q hq d hw
          simp [mkReceipts] at hq
          rcases hq with rfl | rfl
          · simp at hw
          · simp at hw; subst hw
            refine ⟨fun a0 ha0 => by simp [resAmt] at ha0, fun a0 ha0 => ?_⟩
            simp [awAmt, hV] at ha0; subst ha0
            exact ⟨_, by simp [mkReceipts]; exact Or.inl rfl, by simp, by simp [wdSrc, hV]⟩
        · intro q1 h1 q2 h2 b1 b2 d w1 w2
          simp [mkReceipts] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
            first | rfl | (simp [bearing, resAmt, awAmt] at b1; done) | (simp [bearing, resAmt, awAmt] at b2; done)
        · intro q hq h1; simp [mkReceipts] at hq
          rcases hq with rfl | rfl <;> (simp at h1; exact absurd (hV ▸ h1) (Ne.symm hTV))
        · intro q hq h1 a0 d0; simp [mkReceipts] at hq
          rcases hq with rfl | rfl
          · intro e; simp at e; exact hpV e.1.1
          · simp at h1; exact absurd (hV ▸ h1) (Ne.symm hTV)
        · intro q hq h1 a0 d0; simp [mkReceipts] at hq
          rcases hq with rfl | rfl <;> simp
        · rw [pot_okVal, heq]
          simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil]
          simp only [contrib_call, hV, and_self, if_true, awPot, Option.map, Nat.add_zero, hf]
          simp only [hTV.symm, false_and, if_false, Nat.zero_add]
          omega
      | after_withdraw who a =>
        simp only [vaultHandle] at hd
        split at hd; · simp at hd
        rename_i hpV; simp only [ctxOf, ne_eq, Decidable.not_not] at hpV
        have heq := rest_eq_of_not_src hJ hr (by simp [depSrc, hact]) (by simp [wdSrc, hact])
        have haw : awAmt V r = some a := by simp [awAmt, hact, hV, hpV]
        obtain ⟨o1, o2, o3, o4, o5⟩ := nil_obligations (T := T) (V := V) r w.nextId
        rcases inp with _ | ⟨y | _⟩
        · simp at hd
        · have ⟨d, hwd, hlk⟩ := readiness_input hrd
          have hc : contrib T V w.results r = 0 := by rw [contrib_of_aw haw, hwd]; simp [awPot, hlk]
          simp only [Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          apply J_okVal hJ hr hrd hwf hI _ hJ.keys o1 o2 o3 o4 o5
          rw [pot_okVal, heq]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          omega
        · have ⟨d, hwd, hlk⟩ := readiness_input hrd
          have hc : contrib T V w.results r = a := by rw [contrib_of_aw haw, hwd]; simp [awPot, hlk]
          simp only [hwfix, if_true, Outcome.ok.injEq, Ret.val.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          apply J_okVal hJ hr hrd hwf hI _ (keys_add _ _ _ hJ.keys) o1 o2 o3 o4 o5
          rw [pot_okVal, heq]
          simp only [mkReceipts, List.zipIdx_nil, List.map_nil, List.sum_nil, Nat.add_zero]
          rw [total_add_eq _ _ _ hJ.keys]
          omega
      | _ => simp [vaultHandle] at hd
    · rw [if_neg hV] at hd
      have hs := hframe _ _ _ _ _ _ _ hd
      subst hs
      have hc0 := hcr (by unfold resAmt; split <;> simp_all) (by unfold awAmt; split <;> simp_all)
      have heq := rest_eq_of_not_src hJ hr (by unfold depSrc; split <;> simp_all)
        (by unfold wdSrc; split <;> simp_all) (.ok v)
      obtain ⟨hz, hq⟩ := other_news hT hV w.nextId es ((r.id, .ok v) :: w.results)
      have hpred : ∀ q ∈ mkReceipts r w.nextId es, q.pred = r.recv := fun q h => mk_pred h
      have hnb : ∀ q ∈ mkReceipts r w.nextId es, resAmt T V q = none ∧ awAmt V q = none := by
        intro q h
        constructor
        · unfold resAmt; split <;> simp_all [hpred q h]
        · unfold awAmt; split <;> simp_all [hpred q h]
      apply J_okVal hJ hr hrd hwf hI _ hJ.keys
      · intro q h d _
        refine ⟨fun a ha => ?_, fun a ha => ?_⟩
        · rw [(hnb q h).1] at ha; cases ha
        · rw [(hnb q h).2] at ha; cases ha
      · intro q1 h1 q2 h2 b1; simp [bearing, (hnb q1 h1).1, (hnb q1 h1).2] at b1
      · intro q h h1; rw [hpred q h] at h1; exact absurd h1 hT
      · intro q h h1 a d e
        obtain ⟨e', i, hm, rfl⟩ := mem_mkReceipts.mp h
        simp at e h1
        exact hdon _ _ _ _ _ _ _ hd e' (mem_of_mem_zipIdx' hm) h1 a e.1
      · intro q h h1; rw [hpred q h] at h1; exact absurd h1 hV
      · rw [pot_okVal, hz, heq]; omega


theorem J_prom_case (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (hframe : Frame other) (hdon : NoDonate T V other) (hTV : T ≠ V)
    {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) {s : St α} {es : List (Emit α (Call α))} {idx : Nat}
    (hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app = .ok s es (.promise idx))
    (hwf : emitsWellFormed es = true) (hidx : idx < es.length) :
    J T V (okProm w r dep s es idx) := by
  have hI := prom_case cfg other cf hfix hframe hTV hJ.inv hr hrd hact hd hwf hidx
  have hunr := hJ.inv.unres r hr
  have hrid := hJ.inv.idLt r hr
  have hl := hJ.lower
  have h1 := sum_removePending w.pending (contrib T V w.results) hJ.inv.nodup r hr
  have hfresh : lookupResult w.results (w.nextId + idx) = none := fresh_none hJ.inv _ hJ.inv.resLt (by omega)
  have hsr := sum_redirect (T := T) (V := V) w.results (removePending w.pending r.id) r.id (w.nextId + idx) hunr hfresh
  have hf0 : lookupResult w.results w.nextId = none := fresh_none hJ.inv _ hJ.inv.resLt (Nat.le_refl _)
  unfold pot at hl
  have hcr : resAmt T V r = none → awAmt V r = none → contrib T V w.results r = 0 := contrib_zero
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
      have hpV : r.pred ≠ V := fun e => hJ.inv.noVcall r hr e hT to a m dep hact
      have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
      try simp only [ctxOf] at hne
      apply J_okProm hJ hr hrd hwf hidx hI _ hJ.keys
      · intro q hq hw
        obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
        exact ⟨fun a0 ha0 => by have := hres a0 ha0; simp [depSrc, hact] at this,
               fun a0 ha0 => by have := haw a0 ha0; simp [wdSrc, hact] at this⟩
      · intro q hq d hw
        simp [mkReceipts] at hq
        rcases hq with rfl | rfl
        · simp at hw
        · simp at hw; subst hw
          refine ⟨fun a0 ha0 => ?_, fun a0 ha0 => by simp [awAmt] at ha0⟩
          simp [resAmt, hT] at ha0
          obtain ⟨hto, rfl⟩ := ha0
          exact ⟨_, by simp [mkReceipts]; exact Or.inl rfl, by simp, by simp [depSrc, hto, hT]⟩
      · intro q1 h1 q2 h2 b1 b2 d w1 w2
        simp [mkReceipts] at h1 h2
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
          first | rfl | (simp [bearing, resAmt, awAmt] at b1; done) | (simp [bearing, resAmt, awAmt] at b2; done)
      · intro q hq hb hw
        simp [mkReceipts] at hq
        rcases hq with rfl | rfl <;> simp at hw <;> omega
      · intro q hq h1 h2 s' rcv a0 d0 e
        simp [mkReceipts] at hq
        rcases hq with rfl | rfl <;> simp at e
        intro hs; apply hpV
        have hps : r.pred = s' := by simp_all
        rw [hps, hs]
      · intro q hq h1 a0 d0
        simp [mkReceipts] at hq
        rcases hq with rfl | rfl <;> simp
      · intro q hq h1
        simp [mkReceipts] at hq
        rcases hq with rfl | rfl <;> (simp at h1; exact absurd (hT ▸ h1) hTV)
      · rw [pot_okProm, hsr]
        simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, ctxOf]
        simp only [Bal.get_add, Bal.get_sub, hpV, if_false]
        simp only [contrib_call, hT, and_self, true_and, resPot, Option.map, Nat.add_zero, hf0]
        by_cases hto : to = V
        · simp only [hto, if_true]; omega
        · simp only [hto, if_false]; omega
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
          have hc0 := hcr (by simp [resAmt, hact]) (by simp [awAmt, hact])
          apply J_okProm hJ hr hrd hwf hidx hI _ hJ.keys
          · intro q hq hw
            obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
            refine ⟨fun a0 ha0 => ?_, fun a0 ha0 => by have := haw a0 ha0; simp [wdSrc, hact] at this⟩
            have := hres a0 ha0
            simp [depSrc, hact, hV, hpT] at this; subst this
            exact ⟨_, by simp [mkReceipts]; exact Or.inr rfl, by simp, by simp [depSrc, hV]⟩
          · intro q hq d hw
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl <;>
              exact ⟨fun a0 ha0 => by simp [resAmt] at ha0, fun a0 ha0 => by simp [awAmt] at ha0⟩
          · intro q1 h1 q2 h2 b1
            simp [mkReceipts] at h1
            rcases h1 with rfl | rfl <;> simp [bearing, resAmt, awAmt] at b1
          · intro q hq hb
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl <;> simp [bearing, resAmt, awAmt] at hb
          · intro q hq h1
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl <;> (simp at h1; exact absurd (hV ▸ h1) (Ne.symm hTV))
          · intro q hq h1 a0 d0
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl
            · simp
            · simp at h1; exact absurd (hV ▸ h1) (Ne.symm hTV)
          · intro q hq h1 a0 d0
            simp [mkReceipts] at hq
            rcases hq with rfl | rfl <;> simp
          · rw [pot_okProm, hsr]
            simp only [mkReceipts, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, ctxOf]
            simp only [contrib_call]
            omega
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
      have hc0 := hcr (by unfold resAmt; split <;> simp_all) (by unfold awAmt; split <;> simp_all)
      obtain ⟨hz, hq⟩ := other_news hT hV w.nextId es w.results
      have hpred : ∀ q ∈ mkReceipts r w.nextId es, q.pred = r.recv := fun q h => mk_pred h
      have hnb : ∀ q ∈ mkReceipts r w.nextId es, resAmt T V q = none ∧ awAmt V q = none := by
        intro q h
        constructor
        · unfold resAmt; split <;> simp_all [hpred q h]
        · unfold awAmt; split <;> simp_all [hpred q h]
      apply J_okProm hJ hr hrd hwf hidx hI _ hJ.keys
      · intro q hq hw
        obtain ⟨hres, haw⟩ := waiter_amount hJ hr hq hw
        refine ⟨fun a0 ha0 => ?_, fun a0 ha0 => ?_⟩
        · have := hres a0 ha0; unfold depSrc at this; split at this <;> simp_all
        · have := haw a0 ha0; unfold wdSrc at this; split at this <;> simp_all
      · intro q h d _
        refine ⟨fun a ha => ?_, fun a ha => ?_⟩
        · rw [(hnb q h).1] at ha; cases ha
        · rw [(hnb q h).2] at ha; cases ha
      · intro q1 h1 q2 h2 b1; simp [bearing, (hnb q1 h1).1, (hnb q1 h1).2] at b1
      · intro q h b1; simp [bearing, (hnb q h).1, (hnb q h).2] at b1
      · intro q h h1; rw [hpred q h] at h1; exact absurd h1 hT
      · intro q h h1 a d e
        obtain ⟨e', i, hm, rfl⟩ := mem_mkReceipts.mp h
        simp at e h1
        exact hdon _ _ _ _ _ _ _ hd e' (mem_of_mem_zipIdx' hm) h1 a e.1
      · intro q h h1; rw [hpred q h] at h1; exact absurd h1 hV
      · rw [pot_okProm, hsr, hz]; omega

/-- A receipt with potential never fails on its own: it runs and returns a value. -/
theorem bearing_dispatch (hwfix : cfg.withdrawFixed = true) (hTV : T ≠ V)
    {w : GW α} {r : GR α} {inp : Option PResult} {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) (hrd : readiness w r = some inp) (hc : contrib T V w.results r ≠ 0) :
    ∃ s v, (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app = .ok s [] (.val v) := by
  have hwait : ∃ d, r.waitsOn = some d := by
    cases hw : r.waitsOn with
    | some d => exact ⟨d, rfl⟩
    | none =>
      exfalso; apply hc
      unfold contrib
      cases resAmt T V r <;> cases awAmt V r <;> simp [resPot, awPot, hw]
  obtain ⟨d, hwd⟩ := hwait
  have hinp : ∃ x, inp = some x := by
    unfold readiness at hrd; rw [hwd] at hrd
    cases e : lookupResult w.results d with
    | none => simp [e] at hrd
    | some x => simp [e] at hrd; exact ⟨x, hrd.symm⟩
  obtain ⟨x, rfl⟩ := hinp
  simp only [gsys]
  rcases bearing_amt (bearing_of_contrib hc) with ⟨a, ha⟩ | ⟨a, ha⟩
  · unfold resAmt at ha
    rw [hact] at ha
    cases c with
    | ft_resolve_transfer sd rcv a' =>
      simp at ha
      obtain ⟨⟨hrT, hpT, _⟩, _⟩ := ha
      rw [if_pos hrT]
      simp only [tokenHandle, ftHandle, ctxOf, hpT, hrT, ne_eq, not_true_eq_false, if_false]
      split
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
    | _ => simp at ha
  · unfold awAmt at ha
    rw [hact] at ha
    cases c with
    | after_withdraw who a' =>
      simp at ha
      obtain ⟨⟨hrV, hpV⟩, _⟩ := ha
      have hrT : r.recv ≠ T := fun e => hTV (e.symm.trans hrV)
      rw [if_neg hrT, if_pos hrV]
      simp only [vaultHandle, ctxOf, hpV, hrV, ne_eq, not_true_eq_false, if_false]
      cases x with
      | ok v => exact ⟨_, _, rfl⟩
      | failed => simp only [hwfix, if_true]; exact ⟨_, _, rfl⟩
    | _ => simp at ha

end cases

section run
variable (cfg : Config) (other : α → Handler α) (cf : GR α → Bool)

theorem run_call_J (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (hframe : Frame other) (hdon : NoDonate T V other) (hTV : T ≠ V)
    {w : GW α} (hJ : J T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) : J T V (runReceipt (gsys cfg T V other cf) w r inp) := by
  have zero_or : ∀ (P : Prop), (∀ s v, (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app ≠ .ok s [] (.val v) ∨ P) →
      P ∨ contrib T V w.results r = 0 := by
    intro P h
    by_cases hc : contrib T V w.results r = 0
    · exact Or.inr hc
    · obtain ⟨s, v, hd⟩ := bearing_dispatch cfg other cf hwfix hTV hact hrd hc
      rcases h s v with h | h
      · exact absurd hd h
      · exact Or.inl h
  rw [runReceipt_call _ w r inp c dep hact]
  cases hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app with
  | panic _ =>
    have : contrib T V w.results r = 0 := by
      rcases zero_or False (fun s v => Or.inl (by rw [hd]; simp)) with h | h
      · exact h.elim
      · exact h
    exact J_fail hJ hr hrd dep this
  | ok s es ret =>
    simp only
    split
    · rename_i hcond
      have : contrib T V w.results r = 0 := by
        rcases zero_or False (fun s' v => by
          by_cases e : (Outcome.ok s es ret : Outcome (St α) α (Call α)) = .ok s' [] (.val v)
          · simp at e; obtain ⟨rfl, rfl, rfl⟩ := e
            simp [emitsDeposit, emitsWellFormed] at hcond
          · exact Or.inl (by rw [hd]; exact e)) with h | h
        · exact h.elim
        · exact h
      exact J_fail hJ hr hrd dep this
    · rename_i hcond
      have hwf : emitsWellFormed es = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at hcond
        cases h : emitsWellFormed es <;> simp_all
      cases ret with
      | val v => exact J_val_case cfg other cf hfix hwfix hframe hdon hTV hJ hr hrd hact hd hwf
      | promise idx =>
        simp only
        split
        · rename_i hidx; exact J_prom_case cfg other cf hfix hwfix hframe hdon hTV hJ hr hrd hact hd hwf hidx
        · have : contrib T V w.results r = 0 := by
            rcases zero_or False (fun s' v => Or.inl (by rw [hd]; simp)) with h | h
            · exact h.elim
            · exact h
          exact J_fail hJ hr hrd dep this

theorem step_J (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (hframe : Frame other) (hdon : NoDonate T V other) (hTV : T ≠ V)
    (hcf : ∀ r, cf r = true → r.waitsOn = none)
    {w w' : GW α} (hJ : J T V w) (st : Step α (Call α))
    (hsg : ∀ sg rv c d, st = .submit sg rv c d → sg ≠ T ∧ sg ≠ V ∧ (rv = T → ∀ x, c ≠ .ft_transfer V x))
    (hst : step (gsys cfg T V other cf) w st = some w') : J T V w' := by
  cases st with
  | submit sg rv c dep =>
    obtain ⟨hsT, hsV, hdn⟩ := hsg sg rv c dep rfl
    simp only [step] at hst
    split at hst
    · cases hst
    · cases hst; exact J_submit hJ sg rv c dep hsT hsV hdn
  | run rid =>
    simp only [step, bind, Option.bind] at hst
    cases hf : findPending w.pending rid with
    | none => simp [hf] at hst
    | some r =>
      simp only [hf] at hst
      cases hrd : readiness w r with
      | none => simp [hrd] at hst
      | some inp =>
        simp only [hrd, pure, Option.some.injEq] at hst
        subst hst
        have hr := (findPending_spec hf).1
        cases hact : r.action with
        | refund amt => exact J_refund hJ hr hrd hact
        | call c dep => exact run_call_J cfg other cf hfix hwfix hframe hdon hTV hJ hr hrd hact
  | fail rid =>
    simp only [step, bind, Option.bind] at hst
    cases hf : findPending w.pending rid with
    | none => simp [hf] at hst
    | some r =>
      simp only [hf] at hst
      cases hrd : readiness w r with
      | none => simp [hrd] at hst
      | some inp =>
        simp only [hrd] at hst
        have hr := (findPending_spec hf).1
        cases hact : r.action with
        | refund amt => simp [hact] at hst
        | call c dep =>
          simp only [hact] at hst
          split at hst
          · rename_i hcan
            cases hst
            have hw := hcf r hcan
            have hc : contrib T V w.results r = 0 := by
              unfold contrib; cases resAmt T V r <;> cases awAmt V r <;> simp [resPot, awPot, hw]
            exact J_fail hJ hr hrd dep hc
          · cases hst

theorem run_J (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (hframe : Frame other) (hdon : NoDonate T V other) (hTV : T ≠ V)
    (hcf : ∀ r, cf r = true → r.waitsOn = none) :
    ∀ (tr : List (Step α (Call α))) (w w' : GW α), J T V w → honestTxs T V tr →
      run (gsys cfg T V other cf) w tr = some w' → J T V w' := by
  intro tr
  induction tr with
  | nil => intro w w' hJ _ h; simp [run] at h; subst h; exact hJ
  | cons st rest ih =>
    intro w w' hJ hsg h
    simp only [run] at h
    cases hs : step (gsys cfg T V other cf) w st with
    | none => simp [hs] at h
    | some w1 =>
      rw [hs] at h
      have hJ1 := step_J cfg other cf hfix hwfix hframe hdon hTV hcf hJ st
        (fun sg rv c d e => hsg sg rv c d (e ▸ List.mem_cons_self ..)) hs
      exact ih w1 w' hJ1 (fun sg rv c d hm => hsg sg rv c d (List.mem_cons_of_mem _ hm)) h

end run

theorem initial_J {w : GW α} (h : InitialExact V w) : J T V w := by
  obtain ⟨hp, hres, hb, hk⟩ := h
  refine ⟨initial_inv ⟨hp, hres, by omega⟩, ?_, hk, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pot, hp]; omega
  all_goals (intro q hq; simp [hp] at hq)

/-- **No stuck funds.** Fixed vault (both fixes), only non-callback receipts may fail, nobody makes a
plain `ft_transfer` to the vault: in every reachable state the vault holds at most what the ledger
owes plus what is still in flight; when nothing is in flight it holds exactly what the ledger owes. -/
theorem fixed_vault_no_stuck_funds (cfg : Config) (hfix : cfg.depositFixed = true)
    (hwfix : cfg.withdrawFixed = true) (T V : α) (hTV : T ≠ V) (other : α → Handler α)
    (hframe : Frame other) (hdon : NoDonate T V other)
    (canFail : GR α → Bool) (hcf : ∀ r, canFail r = true → r.waitsOn = none)
    (w0 : GW α) (h0 : InitialExact V w0) (tr : List (Step α (Call α))) (htx : honestTxs T V tr)
    (w : GW α) (hrun : run (gsys cfg T V other canFail) w0 tr = some w) :
    w.app.ft.get V ≤ w.app.ledger.total + pot T V w ∧
      (w.pending = [] → w.app.ft.get V = w.app.ledger.total) := by
  have hJ := run_J cfg other canFail hfix hwfix hframe hdon hTV hcf tr w0 w (initial_J h0) htx hrun
  refine ⟨hJ.lower, fun hp => ?_⟩
  have h1 := hJ.lower
  have h2 := hJ.inv.bal
  simp [pot, hp] at h1 h2
  omega

theorem concreteOther_noDonate (cfg : Config) : NoDonate Acct.token Acct.vault (concreteOther cfg) := by
  intro a ctx c s s' es ret h
  cases a <;> simp [concreteOther, hookHandle] at h
  split at h <;> simp_all

/-- The explorer's fixed models under adversaries that fail only non-callback receipts
(`withdraw-fixed`, `noreturn-fixed`) have no stuck funds, for every trace (not just to depth N). -/
theorem concrete_no_stuck (cfg : Config) (hfix : cfg.depositFixed = true) (hwfix : cfg.withdrawFixed = true)
    (adv : Adversary) (hadv : ∀ r, canFail adv r = true → r.waitsOn = none)
    (tr : List (Step Acct (Call Acct))) (htx : honestTxs Acct.token Acct.vault tr)
    (w : W) (hrun : run (system cfg adv) init tr = some w) : noStuck w = true := by
  rw [system_eq] at hrun
  have := fixed_vault_no_stuck_funds cfg hfix hwfix .token .vault (by decide) _ (concreteOther_frame _)
    (concreteOther_noDonate _) _ hadv init
    ⟨rfl, rfl, by decide, by decide⟩ tr htx w hrun
  unfold noStuck
  cases hp : w.pending with
  | nil => have := this.2 hp; simp [hp, this]
  | cons _ _ => simp

end NearAsync.Vault.Proof
