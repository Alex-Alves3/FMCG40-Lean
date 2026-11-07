-- ============================================================
-- FMCG 4.0 Formal Mathematical Framework
-- Signal-to-Shelf Chain (Thesis Appendix A, Sections A.5 to A.6)
-- Theorems T15 to T23, extending FMCG40/Basic.lean
-- ============================================================
-- Author: Alexandre Alves da Silva
-- UCL Computer Science PhD
-- Supervisor: Prof. Philip Treleaven
-- ============================================================
--
-- Conventions:
--   * FMCG40/Basic.lean is imported and left untouched.
--   * Encoders, cosine similarity, the neural policy, the gradient
--     boosting models and the ASP verifier are abstract functions with
--     explicit hypotheses. Every theorem holds for any implementation
--     that satisfies those hypotheses.
--   * Time quantities named dt_* correspond to the thesis symbols
--     Δt_* (Equations A.29 and A.32).

import FMCG40.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace FMCG40

open Real

-- ============================================================
-- Definitions: Equations A.32 and A.34
-- ============================================================

/-- Equation A.32: CBR computed by the implementation, with
    R = R(a*_B; S) and p the portfolio coverage. The times are
    Δt_int and Δt_seq, in the same unit as 1/lam. -/
noncomputable def CBR_impl (R p lam dt_int dt_seq : ℝ) : ℝ :=
  R / p * Real.exp (-lam * (dt_int - dt_seq))

/-- Equation A.34: the full Signal-to-Shelf form, with the factor
    (Δt_seq + t₀) / (Δt_int + t₀). -/
noncomputable def CBR_StS (R p lam t₀ dt_int dt_seq : ℝ) : ℝ :=
  CBR_impl R p lam dt_int dt_seq * ((dt_seq + t₀) / (dt_int + t₀))

/-- Equation A.10 with arbitrary intrinsic qualities for the two arms.
    `CBR R_base R_prod R_mark R_coup ...` of Basic.lean is the instance
    with R₀_int = R_base + R_prod + R_mark + R_coup and
    R₀_seq = R_base + R_prod + R_mark. -/
noncomputable def CBR_arms (R₀_int R₀_seq lam t₀ t_int t_seq : ℝ) : ℝ :=
  StS R₀_int lam t₀ t_int / StS R₀_seq lam t₀ t_seq

theorem CBR_eq_CBR_arms
    (R_base R_prod R_mark R_coup lam t₀ t_int t_seq : ℝ) :
    CBR R_base R_prod R_mark R_coup lam t₀ t_int t_seq =
    CBR_arms (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
      lam t₀ t_int t_seq := rfl

-- ============================================================
-- T15. Decomposition of ln CBR (Equation A.33)
-- ============================================================

theorem CBR_log_decomposition
    (R p lam dt_int dt_seq : ℝ) (hR : R > 0) (hp : p > 0) :
    Real.log (CBR_impl R p lam dt_int dt_seq) =
    Real.log (R / p) + lam * (dt_seq - dt_int) := by
  unfold CBR_impl
  rw [Real.log_mul (div_pos hR hp).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

-- ============================================================
-- T16. Exact condition for coupling benefit (Section A.6)
-- ============================================================

theorem CBR_gt_one_iff
    (R p lam dt_int dt_seq : ℝ) (_hR : R > 0) (_hp : p > 0) :
    CBR_impl R p lam dt_int dt_seq > 1 ↔
    R / p > Real.exp (-lam * (dt_seq - dt_int)) := by
  have hE : 0 < Real.exp (-lam * (dt_seq - dt_int)) := Real.exp_pos _
  have h : Real.exp (-lam * (dt_int - dt_seq)) =
      (Real.exp (-lam * (dt_seq - dt_int)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold CBR_impl
  rw [h, ← div_eq_mul_inv]
  exact one_lt_div hE

/-- Relation between Equations A.32, A.34 and A.10. -/
theorem CBR_arms_eq_CBR_StS
    (R p lam t₀ t_int t_seq : ℝ)
    (hR : R > 0) (hp : p > 0)
    (ht₀ : t₀ > 0) (ht_int : t_int ≥ 0) (ht_seq : t_seq ≥ 0) :
    CBR_arms R p lam t₀ t_int t_seq = CBR_StS R p lam t₀ t_int t_seq := by
  have hi : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hs : t_seq + t₀ > 0 := StS_denominator_pos t₀ t_seq ht₀ ht_seq
  have e : Real.exp (-lam * t_int) =
      Real.exp (-lam * (t_int - t_seq)) * Real.exp (-lam * t_seq) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold CBR_arms CBR_StS CBR_impl StS
  rw [e]
  have h1 : Real.exp (-lam * t_seq) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- Condition 10 of Section A.1 as a special case of the exact
    condition: under its hypotheses the criterion of
    `CBR_gt_one_iff` holds, and the conclusion is strict. -/
theorem CBR_condition10_strict
    (R_base R_prod R_mark R_coup lam t₀ t_int t_seq : ℝ)
    (hlam : lam > 0) (ht₀ : t₀ > 0)
    (ht_int : t_int ≥ 0) (ht_seq : t_seq ≥ 0) (ht : t_int ≤ t_seq)
    (hcoup : R_coup > 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0) :
    CBR_impl (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
      lam t_int t_seq > 1 ∧
    CBR R_base R_prod R_mark R_coup lam t₀ t_int t_seq > 1 := by
  have hp : R_base + R_prod + R_mark > 0 := hR_base_pos
  have hR : R_base + R_prod + R_mark + R_coup > 0 := by linarith
  have hratio : (R_base + R_prod + R_mark + R_coup) / (R_base + R_prod + R_mark) > 1 := by
    rw [gt_iff_lt, one_lt_div hp]
    linarith
  have hexp : Real.exp (-lam * (t_seq - t_int)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h1 : CBR_impl (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
      lam t_int t_seq > 1 :=
    (CBR_gt_one_iff _ _ lam t_int t_seq hR hp).mpr (lt_of_le_of_lt hexp hratio)
  refine ⟨h1, ?_⟩
  rw [CBR_eq_CBR_arms,
    CBR_arms_eq_CBR_StS _ _ lam t₀ t_int t_seq hR hp ht₀ ht_int ht_seq]
  unfold CBR_StS
  have hi : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hfac : (t_seq + t₀) / (t_int + t₀) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ hi]
    linarith
  calc (1 : ℝ) < CBR_impl (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
        lam t_int t_seq := h1
    _ = CBR_impl (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
        lam t_int t_seq * 1 := by ring
    _ ≤ CBR_impl (R_base + R_prod + R_mark + R_coup) (R_base + R_prod + R_mark)
        lam t_int t_seq * ((t_seq + t₀) / (t_int + t₀)) :=
      mul_le_mul_of_nonneg_left hfac (by linarith)

-- ============================================================
-- T17. Boundedness (Section A.6)
-- ============================================================

/-- Equation A.22. `enc` ranges over the finite encoder set E, `cos` is
    an abstract similarity, `d` stands for desc(a) and `e k` for the
    descriptor text of signal member k. -/
noncomputable def coverageReward {T V ι : Type*}
    (cos : V → V → ℝ) (E : Finset (T → V)) (S : Finset ι) (hS : S.Nonempty)
    (d : T) (e : ι → T) : ℝ :=
  (1 / (E.card : ℝ)) *
    ∑ φ ∈ E, S.inf' hS (fun k => cos (φ d) (φ (e k)))

/-- T17(a). Equation A.22 lies in [-1, 1] when cos takes values in [-1, 1]. -/
theorem coverageReward_bounds {T V ι : Type*}
    (cos : V → V → ℝ) (hcos : ∀ u v, -1 ≤ cos u v ∧ cos u v ≤ 1)
    (E : Finset (T → V)) (S : Finset ι) (hE : E.Nonempty) (hS : S.Nonempty)
    (d : T) (e : ι → T) :
    -1 ≤ coverageReward cos E S hS d e ∧ coverageReward cos E S hS d e ≤ 1 := by
  have hcard : (0 : ℝ) < (E.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hE
  have hmin : ∀ φ ∈ E, -1 ≤ S.inf' hS (fun k => cos (φ d) (φ (e k))) ∧
      S.inf' hS (fun k => cos (φ d) (φ (e k))) ≤ 1 := by
    intro φ _
    constructor
    · exact (Finset.le_inf' hS _ (fun k _ => (hcos _ _).1))
    · obtain ⟨k, hk⟩ := hS
      exact (Finset.inf'_le _ hk).trans (hcos _ _).2
  have hsum_le : ∑ φ ∈ E, S.inf' hS (fun k => cos (φ d) (φ (e k))) ≤ (E.card : ℝ) := by
    calc ∑ φ ∈ E, S.inf' hS (fun k => cos (φ d) (φ (e k))) ≤ ∑ _φ ∈ E, (1 : ℝ) :=
          Finset.sum_le_sum (fun φ hφ => (hmin φ hφ).2)
      _ = (E.card : ℝ) := by simp
  have hsum_ge : -(E.card : ℝ) ≤ ∑ φ ∈ E, S.inf' hS (fun k => cos (φ d) (φ (e k))) := by
    calc -(E.card : ℝ) = ∑ _φ ∈ E, (-1 : ℝ) := by simp
      _ ≤ ∑ φ ∈ E, S.inf' hS (fun k => cos (φ d) (φ (e k))) :=
          Finset.sum_le_sum (fun φ hφ => (hmin φ hφ).1)
  unfold coverageReward
  constructor
  · rw [one_div, inv_mul_eq_div, le_div_iff₀ hcard]
    linarith
  · rw [one_div, inv_mul_eq_div, div_le_one hcard]
    exact hsum_le

/-- The logistic function of Equation A.35. -/
noncomputable def expit (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem expit_mem_Ioo (x : ℝ) : 0 < expit x ∧ expit x < 1 := by
  have h : 0 < 1 + Real.exp (-x) := by positivity
  constructor
  · unfold expit; positivity
  · unfold expit
    rw [div_lt_one h]
    linarith [Real.exp_pos (-x)]

/-- Equation A.35. `pk` and `f` are the two parts of the gradient boosting
    model for signal member k, evaluated at the recipe. -/
noncomputable def consumerReward {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (pk f : ι → ℝ) : ℝ :=
  S.inf' hS (fun k => pk k * expit (f k))

/-- T17(b). Equation A.35 lies in [0, 1] when each pk k is in [0, 1]. -/
theorem consumerReward_bounds {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (pk f : ι → ℝ)
    (hpk : ∀ k, 0 ≤ pk k ∧ pk k ≤ 1) :
    0 ≤ consumerReward S hS pk f ∧ consumerReward S hS pk f ≤ 1 := by
  have hy : ∀ k, 0 ≤ pk k * expit (f k) ∧ pk k * expit (f k) ≤ 1 := by
    intro k
    obtain ⟨h0, h1⟩ := expit_mem_Ioo (f k)
    obtain ⟨hp0, hp1⟩ := hpk k
    constructor
    · positivity
    · calc pk k * expit (f k) ≤ 1 * 1 :=
          mul_le_mul hp1 h1.le h0.le zero_le_one
        _ = 1 := by ring
  unfold consumerReward
  constructor
  · exact Finset.le_inf' hS _ (fun k _ => (hy k).1)
  · obtain ⟨k, hk⟩ := hS
    exact (Finset.inf'_le _ hk).trans (hy k).2

-- ============================================================
-- T18. Budget monotonicity (Section A.6, Equation A.23)
-- ============================================================

/-- M(B) = max over n ≤ B of R(a_n), for a sequence of proposals
    a_1, a_2, ... and B ≥ 1. -/
noncomputable def bestWithin {α : Type*} (R : α → ℝ) (a : ℕ → α)
    (B : ℕ) (hB : 1 ≤ B) : ℝ :=
  (Finset.Icc 1 B).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hB⟩⟩ (fun n => R (a n))

theorem bestWithin_mono {α : Type*} (R : α → ℝ) (a : ℕ → α)
    {B₁ B₂ : ℕ} (h₁ : 1 ≤ B₁) (h : B₁ ≤ B₂) :
    bestWithin R a B₁ h₁ ≤ bestWithin R a B₂ (h₁.trans h) := by
  unfold bestWithin
  apply Finset.sup'_mono
  intro n hn
  rw [Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans h⟩

-- ============================================================
-- T19. Safety (Section A.6, Equations A.27 and A.28)
-- ============================================================

/-- Verdict of the ASP verifier. -/
inductive Verdict where
  | SAT
  | UNSAT
  deriving DecidableEq

/-- Equation A.27: the set accepted by the verifier. -/
def compliantSet {X Ω : Type*} [Fintype Ω] (V : X → Ω → Verdict) (x : X) : Finset Ω :=
  Finset.univ.filter (fun ω => V x ω = Verdict.SAT)

theorem mem_compliantSet {X Ω : Type*} [Fintype Ω] (V : X → Ω → Verdict) (x : X)
    (ω : Ω) : ω ∈ compliantSet V x ↔ V x ω = Verdict.SAT := by
  simp [compliantSet]

/-- ω is an argmax of f over the finite set s. -/
def IsArgmaxOn {Ω : Type*} (f : Ω → ℝ) (s : Finset Ω) (ω : Ω) : Prop :=
  ω ∈ s ∧ ∀ ω' ∈ s, f ω' ≤ f ω

/-- T19. Safety: an argmax of f over Ω₂₀ ∩ 𝒞 belongs to 𝒞. In this
    encoding the statement follows from the definition of argmax over a
    set contained in 𝒞, given Equation A.27. -/
theorem selection_mem_compliant {X Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (V : X → Ω → Verdict) (x : X) (Ω₂₀ : Finset Ω) (f : Ω → ℝ) (ωstar : Ω)
    (_hne : (Ω₂₀ ∩ compliantSet V x).Nonempty)
    (harg : IsArgmaxOn f (Ω₂₀ ∩ compliantSet V x) ωstar) :
    ωstar ∈ compliantSet V x ∧ V x ωstar = Verdict.SAT := by
  have hmem := (Finset.mem_inter.mp harg.1).2
  exact ⟨hmem, (mem_compliantSet V x ωstar).mp hmem⟩

open Classical in
/-- Equation A.28 as a partial function: the selected strategy, or
    `none` when Ω₂₀ ∩ 𝒞 is empty. -/
noncomputable def selectStrategy {X Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (V : X → Ω → Verdict) (x : X) (Ω₂₀ : Finset Ω) (f : Ω → ℝ) : Option Ω :=
  if h : (Ω₂₀ ∩ compliantSet V x).Nonempty then
    some (Finset.exists_max_image _ f h).choose
  else none

theorem selectStrategy_eq_none_iff {X Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (V : X → Ω → Verdict) (x : X) (Ω₂₀ : Finset Ω) (f : Ω → ℝ) :
    selectStrategy V x Ω₂₀ f = none ↔ Ω₂₀ ∩ compliantSet V x = ∅ := by
  unfold selectStrategy
  by_cases h : (Ω₂₀ ∩ compliantSet V x).Nonempty
  · rw [dif_pos h]
    simp only [reduceCtorEq, false_iff]
    exact Finset.nonempty_iff_ne_empty.mp h
  · rw [dif_neg h]
    simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.mp h

/-- T19 for the partial function: whatever Γ returns is an argmax of f
    over Ω₂₀ ∩ 𝒞, hence verified by V. -/
theorem selectStrategy_safe {X Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (V : X → Ω → Verdict) (x : X) (Ω₂₀ : Finset Ω) (f : Ω → ℝ) (ω : Ω)
    (h : selectStrategy V x Ω₂₀ f = some ω) :
    IsArgmaxOn f (Ω₂₀ ∩ compliantSet V x) ω ∧ V x ω = Verdict.SAT := by
  unfold selectStrategy at h
  by_cases hne : (Ω₂₀ ∩ compliantSet V x).Nonempty
  · rw [dif_pos hne] at h
    have hc := (Finset.exists_max_image _ f hne).choose_spec
    have h' := Option.some.inj h
    rw [h'] at hc
    exact ⟨⟨hc.1, hc.2⟩, (mem_compliantSet V x _).mp (Finset.mem_inter.mp hc.1).2⟩
  · rw [dif_neg hne] at h
    exact absurd h (by simp)

/-- Link with Theorem C.1. If V is sound with respect to the semantic
    compliant set C, the selected strategy lies in C (safety). If V is
    also complete and Ω₂₀ meets C, a strategy is returned (relative
    completeness). -/
theorem selection_theorem_C1 {X Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (V : X → Ω → Verdict) (x : X) (C : Set Ω) (Ω₂₀ : Finset Ω) (f : Ω → ℝ)
    (hsound : ∀ ω, V x ω = Verdict.SAT → ω ∈ C)
    (hcomplete : ∀ ω, ω ∈ C → V x ω = Verdict.SAT) :
    (∀ ω, selectStrategy V x Ω₂₀ f = some ω → ω ∈ C) ∧
    ((∃ ω ∈ Ω₂₀, ω ∈ C) → selectStrategy V x Ω₂₀ f ≠ none) := by
  constructor
  · intro ω h
    exact hsound ω (selectStrategy_safe V x Ω₂₀ f ω h).2
  · rintro ⟨ω, hω, hC⟩ hnone
    rw [selectStrategy_eq_none_iff] at hnone
    have hmem : ω ∈ Ω₂₀ ∩ compliantSet V x :=
      Finset.mem_inter.mpr ⟨hω, (mem_compliantSet V x ω).mpr (hcomplete ω hC)⟩
    rw [hnone] at hmem
    exact absurd hmem (Finset.notMem_empty ω)

-- ============================================================
-- T20. Status propagation (Section A.6, Equation A.18)
-- ============================================================

/-- Confirmation status of a signal, ordered candidate < confirmed. -/
inductive Status where
  | candidate
  | confirmed
  deriving DecidableEq

/-- Equation A.18: s = (S, ℓ, κ). -/
structure Signal (ι Level : Type*) where
  members : Finset ι
  level : Level
  status : Status

/-- Output of the chain Φ_B(D) = (s, a*_B, ω*). -/
structure ChainOutput (ι Level Recipe Strategy : Type*) where
  signal : Signal ι Level
  recipe : Recipe
  strategy : Strategy

/-- κ of a chain output is the status of the signal that it carries. -/
def ChainOutput.status {ι Level Recipe Strategy : Type*}
    (o : ChainOutput ι Level Recipe Strategy) : Status :=
  o.signal.status

/-- T20. By the encoding chosen, the chain output carries the signal
    produced by Σ, so status propagation holds by definition (`rfl`). -/
theorem status_propagation {Corpus ι Level Recipe Strategy : Type*}
    (σ : Corpus → Signal ι Level) (prodOp : Signal ι Level → Recipe)
    (γ : Signal ι Level → Recipe → Strategy) (D : Corpus) :
    (ChainOutput.mk (σ D) (prodOp (σ D)) (γ (σ D) (prodOp (σ D)))).status = (σ D).status :=
  rfl

-- ============================================================
-- T21. Well-typedness of the composition (Section A.6, Equation A.30)
-- ============================================================

/-- Output of Σ: a non-empty member set contained in the family F. -/
structure SignalOver {ι : Type*} (F : Finset ι) where
  members : Finset ι
  subset : members ⊆ F
  nonempty : members.Nonempty

/-- Output of Π_B: a recipe whose eight ratios sum to one. -/
structure Recipe where
  ratios : Fin 8 → ℝ
  sum_one : ∑ n, ratios n = 1

/-- Context map ψ : (recipe, observation) → ℝ¹⁰ and its image, the
    domain required by Γ. -/
def ContextDomain {Obs : Type*} (ψ : Recipe → Obs → (Fin 10 → ℝ)) : Type _ :=
  {x : Fin 10 → ℝ // ∃ a o, x = ψ a o}

/-- Σ requires a corpus and returns a SignalOver F and an observation;
    Π_B requires a SignalOver F (non-empty by type) and returns a Recipe;
    Γ requires a ContextDomain ψ. The composition is well defined by
    construction. -/
noncomputable def chain {Corpus Obs Strategy ι : Type*} {F : Finset ι}
    (σ : Corpus → SignalOver F × Obs)
    (prodOp : SignalOver F → Obs → Recipe)
    (ψ : Recipe → Obs → (Fin 10 → ℝ))
    (γ : ContextDomain ψ → Strategy) (D : Corpus) :
    SignalOver F × Recipe × Strategy :=
  let so := σ D
  let a := prodOp so.1 so.2
  (so.1, a, γ ⟨ψ a so.2, a, so.2, rfl⟩)

/-- The three preconditions hold for the data flowing through the chain. -/
theorem chain_wellTyped {Corpus Obs Strategy ι : Type*} {F : Finset ι}
    (σ : Corpus → SignalOver F × Obs)
    (prodOp : SignalOver F → Obs → Recipe)
    (ψ : Recipe → Obs → (Fin 10 → ℝ))
    (γ : ContextDomain ψ → Strategy) (D : Corpus) :
    ((chain σ prodOp ψ γ D).1.members.Nonempty ∧ (chain σ prodOp ψ γ D).1.members ⊆ F) ∧
    (∑ n, (chain σ prodOp ψ γ D).2.1.ratios n = 1) ∧
    (∃ a o, ψ a o = ψ (chain σ prodOp ψ γ D).2.1 (σ D).2) := by
  exact ⟨⟨(σ D).1.nonempty, (σ D).1.subset⟩, (prodOp (σ D).1 (σ D).2).sum_one,
    ⟨_, _, rfl⟩⟩

-- ============================================================
-- T22. Sensitivity of CBR to lam with different times
-- ============================================================

theorem CBR_arms_closed_form
    (R₀_int R₀_seq lam t₀ t_int t_seq : ℝ)
    (hint : R₀_int > 0) (hseq : R₀_seq > 0)
    (ht₀ : t₀ > 0) (ht_int : t_int ≥ 0) (ht_seq : t_seq ≥ 0) :
    CBR_arms R₀_int R₀_seq lam t₀ t_int t_seq =
    (R₀_int / R₀_seq * ((t_seq + t₀) / (t_int + t₀))) *
      Real.exp (lam * (t_seq - t_int)) := by
  have hi : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hs : t_seq + t₀ > 0 := StS_denominator_pos t₀ t_seq ht₀ ht_seq
  have e : Real.exp (-lam * t_int) =
      Real.exp (lam * (t_seq - t_int)) * Real.exp (-lam * t_seq) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold CBR_arms StS
  rw [e]
  have h1 : Real.exp (-lam * t_seq) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- T22. ln CBR(lam) = ln(R₀_int / R₀_seq) + ln((t_seq + t₀)/(t_int + t₀))
    + lam (t_seq - t_int). -/
theorem CBR_log_sensitivity
    (R₀_int R₀_seq lam t₀ t_int t_seq : ℝ)
    (hint : R₀_int > 0) (hseq : R₀_seq > 0)
    (ht₀ : t₀ > 0) (ht_int : t_int ≥ 0) (ht_seq : t_seq ≥ 0) :
    Real.log (CBR_arms R₀_int R₀_seq lam t₀ t_int t_seq) =
    Real.log (R₀_int / R₀_seq) + Real.log ((t_seq + t₀) / (t_int + t₀)) +
      lam * (t_seq - t_int) := by
  have hi : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hs : t_seq + t₀ > 0 := StS_denominator_pos t₀ t_seq ht₀ ht_seq
  rw [CBR_arms_closed_form R₀_int R₀_seq lam t₀ t_int t_seq hint hseq ht₀ ht_int ht_seq,
    Real.log_mul (mul_pos (div_pos hint hseq) (div_pos hs hi)).ne' (Real.exp_pos _).ne',
    Real.log_mul (div_pos hint hseq).ne' (div_pos hs hi).ne', Real.log_exp]

/-- T22, consequences: strictly increasing in lam if t_int < t_seq,
    strictly decreasing if t_int > t_seq, constant if t_int = t_seq. -/
theorem CBR_lambda_monotonicity
    (R₀_int R₀_seq t₀ t_int t_seq : ℝ)
    (hint : R₀_int > 0) (hseq : R₀_seq > 0)
    (ht₀ : t₀ > 0) (ht_int : t_int ≥ 0) (ht_seq : t_seq ≥ 0) :
    (t_int < t_seq → StrictMono (fun lam => CBR_arms R₀_int R₀_seq lam t₀ t_int t_seq)) ∧
    (t_seq < t_int → StrictAnti (fun lam => CBR_arms R₀_int R₀_seq lam t₀ t_int t_seq)) ∧
    (t_int = t_seq → ∀ lam₁ lam₂,
      CBR_arms R₀_int R₀_seq lam₁ t₀ t_int t_seq =
      CBR_arms R₀_int R₀_seq lam₂ t₀ t_int t_seq) := by
  have hi : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hs : t_seq + t₀ > 0 := StS_denominator_pos t₀ t_seq ht₀ ht_seq
  have hK : 0 < R₀_int / R₀_seq * ((t_seq + t₀) / (t_int + t₀)) :=
    mul_pos (div_pos hint hseq) (div_pos hs hi)
  have hform := fun lam => CBR_arms_closed_form R₀_int R₀_seq lam t₀ t_int t_seq
    hint hseq ht₀ ht_int ht_seq
  refine ⟨?_, ?_, ?_⟩
  · intro hlt lam₁ lam₂ h12
    simp only [hform]
    apply mul_lt_mul_of_pos_left _ hK
    apply Real.exp_lt_exp.mpr
    nlinarith
  · intro hlt lam₁ lam₂ h12
    simp only [hform]
    apply mul_lt_mul_of_pos_left _ hK
    apply Real.exp_lt_exp.mpr
    nlinarith
  · intro heq lam₁ lam₂
    rw [hform, hform, heq]
    simp

/-- Consistency with the existing theorem `CBR_lambda_invariant_equal_time`:
    the equal-time case of T22 gives the same conclusion. -/
theorem CBR_lambda_invariant_from_sensitivity
    (R_base R_prod R_mark R_coup t₀ t lam₁ lam₂ : ℝ)
    (ht₀ : t₀ > 0) (ht : t ≥ 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0)
    (hcoup : R_coup > 0) :
    CBR R_base R_prod R_mark R_coup lam₁ t₀ t t =
    CBR R_base R_prod R_mark R_coup lam₂ t₀ t t := by
  have hint : R_base + R_prod + R_mark + R_coup > 0 := by linarith
  rw [CBR_eq_CBR_arms, CBR_eq_CBR_arms]
  exact (CBR_lambda_monotonicity _ _ t₀ t t hint hR_base_pos ht₀ ht ht).2.2
    rfl lam₁ lam₂

-- ============================================================
-- T23. Sign of the speed term (Section A.4, Equation A.29)
-- ============================================================

/-- Δt_int of Equation A.29, in months. -/
noncomputable def timeToShelfInt (b : ℝ) (ρ : Prop) [Decidable ρ] : ℝ :=
  4.0 - min 1.5 (b + 0.2 * (if ρ then 1 else 0))

/-- Δt_seq of Equation A.29, in months. -/
def timeToShelfSeq : ℝ := 9.0

/-- T23. With b ≥ 0: 2.5 ≤ Δt_int ≤ 4.0 < Δt_seq. -/
theorem timeToShelf_bounds (b : ℝ) (ρ : Prop) [Decidable ρ] (hb : 0 ≤ b) :
    2.5 ≤ timeToShelfInt b ρ ∧ timeToShelfInt b ρ ≤ 4.0 ∧ 4.0 < timeToShelfSeq := by
  unfold timeToShelfInt timeToShelfSeq
  have h0 : (0 : ℝ) ≤ 0.2 * (if ρ then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · have := min_le_left (1.5 : ℝ) (b + 0.2 * (if ρ then 1 else 0))
    linarith
  · have := le_min (by norm_num : (0 : ℝ) ≤ 1.5) (by linarith : (0 : ℝ) ≤ b + 0.2 * (if ρ then 1 else 0))
    linarith

/-- The lower bound 2.5 ≤ Δt_int holds without any hypothesis on b. -/
theorem timeToShelfInt_lower (b : ℝ) (ρ : Prop) [Decidable ρ] :
    2.5 ≤ timeToShelfInt b ρ := by
  unfold timeToShelfInt
  have := min_le_left (1.5 : ℝ) (b + 0.2 * (if ρ then 1 else 0))
  linarith

/-- T23, consequences: for lam > 0, lam (Δt_seq - Δt_int) > 0 and
    CBR > R/p. The factor c > 0 converts months to the unit of 1/lam
    (Section A.4 uses c = 365.25/(12 × 7) weeks per month). -/
theorem speed_term_positive (b : ℝ) (ρ : Prop) [Decidable ρ] (hb : 0 ≤ b)
    (lam c R p : ℝ) (hlam : lam > 0) (hc : c > 0) (hR : R > 0) (hp : p > 0) :
    lam * (timeToShelfSeq - timeToShelfInt b ρ) > 0 ∧
    lam * (c * timeToShelfSeq - c * timeToShelfInt b ρ) > 0 ∧
    CBR_impl R p lam (c * timeToShelfInt b ρ) (c * timeToShelfSeq) > R / p := by
  obtain ⟨_, h2, h3⟩ := timeToShelf_bounds b ρ hb
  have hgap : timeToShelfSeq - timeToShelfInt b ρ > 0 := by linarith
  have hgapc : c * timeToShelfSeq - c * timeToShelfInt b ρ > 0 := by
    rw [← mul_sub]; exact mul_pos hc hgap
  refine ⟨mul_pos hlam hgap, mul_pos hlam hgapc, ?_⟩
  unfold CBR_impl
  have hexp : 1 < Real.exp (-lam * (c * timeToShelfInt b ρ - c * timeToShelfSeq)) := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hq : 0 < R / p := div_pos hR hp
  calc R / p = R / p * 1 := by ring
    _ < R / p * Real.exp (-lam * (c * timeToShelfInt b ρ - c * timeToShelfSeq)) :=
      mul_lt_mul_of_pos_left hexp hq

end FMCG40
