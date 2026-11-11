import Verifier.Proof.Solvency

/-!
# Headline theorem: the fixed vault is solvent forever

Unbounded: every trace of any length, any interleaving, any receipt failures, any amounts,
any number of accounts, arbitrary attacker contracts. See `Defs.lean` for the exact setting.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace NearAsync.Vault.Proof

open NearAsync NearAsync.Vault

variable {α : Type} [DecidableEq α] {T V : α}

theorem refund_inv {sys : System (St α) α (Call α)} {w : GW α} (hI : Inv T V w) {r : GR α}
    {inp : Option PResult} (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {amt : Nat}
    (hact : r.action = .refund amt) : Inv T V (runReceipt sys w r inp) := by
  have h : runReceipt sys w r inp =
      { w with near := w.near.add r.recv amt, pending := removePending w.pending r.id } := by
    unfold runReceipt; rw [hact]
  rw [h]
  have h1 := sum_removePending w.pending (contrib T V w.results) hI.nodup r hr
  constructor
  · show w.app.ledger.total + ((removePending w.pending r.id).map (contrib T V w.results)).sum ≤ w.app.ft.get V
    have := hI.bal; unfold pot at this; omega
  · intro q hq; exact hI.idLt q (mem_removePending.mp hq).1
  · intro q hq; exact hI.waitLt q (mem_removePending.mp hq).1
  · exact hI.resLt
  · exact nodup_removePending _ _ hI.nodup
  · intro q hq; exact hI.unres q (mem_removePending.mp hq).1
  · intro o ho a ha
    obtain ⟨hm, _⟩ := mem_removePending.mp ho
    obtain ⟨R, hR, hw, rest⟩ := hI.pairDep o hm a ha
    exact ⟨R, mem_rest hI hr hrd hm hR hw, hw, rest⟩
  · intro t ht a ha
    obtain ⟨hm, _⟩ := mem_removePending.mp ht
    obtain ⟨q, hq, hw, rest⟩ := hI.pairWd t hm a ha
    exact ⟨q, mem_rest hI hr hrd hm hq hw, hw, rest⟩
  · intro q hq; exact hI.noVcall q (mem_removePending.mp hq).1

theorem submit_inv {w : GW α} (hI : Inv T V w) (sg rv : α) (c : Call α) (dep : Nat)
    (hsT : sg ≠ T) (hsV : sg ≠ V) :
    Inv T V { w with near := w.near.sub sg dep,
                     pending := w.pending ++ [{ id := w.nextId, pred := sg, signer := sg, recv := rv,
                                                action := .call c dep, waitsOn := none }],
                     nextId := w.nextId + 1 } := by
  have hz : contrib T V w.results
      { id := w.nextId, pred := sg, signer := sg, recv := rv, action := .call c dep, waitsOn := none } = 0 := by
    rw [contrib_call]; cases c <;> simp [hsT, hsV]
  constructor
  · show w.app.ledger.total + ((w.pending ++ _).map (contrib T V w.results)).sum ≤ w.app.ft.get V
    rw [List.map_append, List.sum_append]; simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, hz]
    have := hI.bal; unfold pot at this; omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact Nat.lt_succ_of_lt (hI.idLt q h)
    · simp at h; subst h; exact Nat.lt_succ_self _
  · intro q hq d hd
    rcases List.mem_append.mp hq with h | h
    · exact Nat.lt_succ_of_lt (hI.waitLt q h d hd)
    · simp at h; subst h; cases hd
  · intro p hp; exact Nat.lt_succ_of_lt (hI.resLt p hp)
  · show ((w.pending ++ _).map (·.id)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨hI.nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    simp at hb; subst hb
    have := hI.idLt q hq; omega
  · intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hI.unres q h
    · simp at h; subst h; exact lookupResult_none_of_lt _ _ _ hI.resLt (Nat.le_refl _)
  · intro o ho a ha
    rcases List.mem_append.mp ho with h | h
    · obtain ⟨R, hR, rest⟩ := hI.pairDep o h a ha
      exact ⟨R, List.mem_append_left _ hR, rest⟩
    · simp at h; subst h
      unfold depSrc at ha; split at ha <;> simp_all
  · intro t ht a ha
    rcases List.mem_append.mp ht with h | h
    · obtain ⟨q, hq, rest⟩ := hI.pairWd t h a ha
      exact ⟨q, List.mem_append_left _ hq, rest⟩
    · simp at h; subst h
      unfold wdSrc at ha; split at ha <;> simp_all
  · intro q hq h1
    rcases List.mem_append.mp hq with h | h
    · exact hI.noVcall q h h1
    · simp at h; subst h; exact absurd h1 hsV

section
variable (cfg : Config) (other : α → Handler α) (cf : GR α → Bool)

theorem run_call_inv (hfix : cfg.depositFixed = true) (hframe : Frame other) (hTV : T ≠ V)
    {w : GW α} (hI : Inv T V w) {r : GR α} {inp : Option PResult}
    (hr : r ∈ w.pending) (hrd : readiness w r = some inp) {c : Call α} {dep : Nat}
    (hact : r.action = .call c dep) : Inv T V (runReceipt (gsys cfg T V other cf) w r inp) := by
  rw [runReceipt_call _ w r inp c dep hact]
  cases hd : (gsys cfg T V other cf).dispatch r.recv (ctxOf r dep inp) c w.app with
  | panic _ => exact fail_inv hI hr hrd dep
  | ok s es ret =>
    simp only
    split
    · exact fail_inv hI hr hrd dep
    · rename_i hcond
      have hwf : emitsWellFormed es = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at hcond
        cases h : emitsWellFormed es <;> simp_all
      cases ret with
      | val v => exact val_case cfg other cf hfix hframe hTV hI hr hrd hact hd hwf
      | promise idx =>
        simp only
        split
        · rename_i hidx; exact prom_case cfg other cf hfix hframe hTV hI hr hrd hact hd hwf hidx
        · exact fail_inv hI hr hrd dep

theorem step_inv (hfix : cfg.depositFixed = true) (hframe : Frame other) (hTV : T ≠ V)
    {w w' : GW α} (hI : Inv T V w) (st : Step α (Call α))
    (hsg : ∀ sg rv c d, st = .submit sg rv c d → sg ≠ T ∧ sg ≠ V)
    (hst : step (gsys cfg T V other cf) w st = some w') : Inv T V w' := by
  cases st with
  | submit sg rv c dep =>
    obtain ⟨hsT, hsV⟩ := hsg sg rv c dep rfl
    simp only [step] at hst
    split at hst
    · cases hst
    · cases hst; exact submit_inv hI sg rv c dep hsT hsV
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
        | refund amt => exact refund_inv hI hr hrd hact
        | call c dep => exact run_call_inv cfg other cf hfix hframe hTV hI hr hrd hact
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
          · cases hst; exact fail_inv hI hr hrd dep
          · cases hst

theorem run_inv (hfix : cfg.depositFixed = true) (hframe : Frame other) (hTV : T ≠ V) :
    ∀ (tr : List (Step α (Call α))) (w w' : GW α), Inv T V w → honestSigners T V tr →
      run (gsys cfg T V other cf) w tr = some w' → Inv T V w' := by
  intro tr
  induction tr with
  | nil => intro w w' hI _ h; simp [run] at h; subst h; exact hI
  | cons st rest ih =>
    intro w w' hI hsg h
    simp only [run] at h
    cases hs : step (gsys cfg T V other cf) w st with
    | none => simp [hs] at h
    | some w1 =>
      rw [hs] at h
      have hI1 := step_inv cfg other cf hfix hframe hTV hI st
        (fun sg rv c d e => hsg sg rv c d (e ▸ List.mem_cons_self ..)) hs
      exact ih w1 w' hI1 (fun sg rv c d hm => hsg sg rv c d (List.mem_cons_of_mem _ hm)) h

end

theorem initial_inv {w : GW α} (h : Initial V w) : Inv T V w := by
  obtain ⟨hp, hres, hb⟩ := h
  constructor
  · simp [pot, hp]; exact hb
  all_goals first
    | (intro q hq; simp [hp] at hq)
    | (intro p hp'; simp [hres] at hp')
    | simp [hp]

/-- **Headline theorem.** The fixed vault (any withdraw variant, any hook) never becomes insolvent:
for every finite trace from an initial state, `Σ ledger ≤ tokens held by the vault`. -/
theorem fixed_vault_solvent_forever (cfg : Config) (hfix : cfg.depositFixed = true)
    (T V : α) (hTV : T ≠ V) (other : α → Handler α) (hframe : Frame other)
    (canFail : GR α → Bool) (w0 : GW α) (h0 : Initial V w0)
    (tr : List (Step α (Call α))) (hsg : honestSigners T V tr)
    (w : GW α) (hrun : run (gsys cfg T V other canFail) w0 tr = some w) :
    w.app.ledger.total ≤ w.app.ft.get V := by
  have hI := run_inv cfg other canFail hfix hframe hTV tr w0 w (initial_inv h0) hsg hrun
  have := hI.bal
  omega

/-! ## The concrete explorer models are instances -/

/-- The hook and plain accounts of the concrete model, as "other code". -/
def concreteOther (cfg : Config) : Acct → Handler Acct
  | .hook => hookHandle cfg.hookReturns
  | _ => fun _ _ _ => .panic "account has no contract"

theorem concreteOther_frame (cfg : Config) : Frame (concreteOther cfg) := by
  intro a ctx c s s' es ret h
  cases a <;> simp [concreteOther, hookHandle] at h
  split at h <;> simp_all

theorem system_eq (cfg : Config) (adv : Adversary) :
    system cfg adv = gsys cfg .token .vault (concreteOther cfg) (canFail adv) := by
  simp only [system, gsys]
  congr 1
  funext a
  cases a <;> rfl

/-- The explorer's fixed models (`deposit-fixed`, `noreturn-fixed`, `withdraw-fixed`) are solvent
for every trace from `init`, under every adversary — not just up to the explorer's depth. -/
theorem concrete_fixed_solvent (cfg : Config) (hfix : cfg.depositFixed = true) (adv : Adversary)
    (tr : List (Step Acct (Call Acct))) (hsg : honestSigners Acct.token Acct.vault tr)
    (w : W) (hrun : run (system cfg adv) init tr = some w) : solvent w = true := by
  rw [system_eq] at hrun
  have := fixed_vault_solvent_forever cfg hfix .token .vault (by decide) _ (concreteOther_frame cfg)
    _ init ⟨rfl, rfl, by decide⟩ tr hsg w hrun
  simp [solvent, this]

end NearAsync.Vault.Proof
