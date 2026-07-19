-- ============================================================
-- FMCG 4.0 Formal Mathematical Framework
-- Signal-to-Shelf and Coupling Benefit Ratio: Lean 4 Proofs
-- ============================================================
-- Author: Alexandre Alves da Silva
-- UCL Computer Science PhD
-- Supervisor: Prof. Philip Treleaven
-- Date: July 2026
-- ============================================================

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace FMCG40

open Real Set

noncomputable def StS (R₀ lam t₀ t : ℝ) : ℝ :=
  R₀ * Real.exp (-lam * t) / (t + t₀)

noncomputable def MarketResponse (R₀ lam t : ℝ) : ℝ :=
  R₀ * Real.exp (-lam * t)

noncomputable def TemporalDecay (lam t : ℝ) : ℝ :=
  Real.exp (-lam * t)

noncomputable def R₀_integrated (R_base R_prod R_mark R_coup : ℝ) : ℝ :=
  R_base + R_prod + R_mark + R_coup

noncomputable def R₀_sequential (R_base R_prod R_mark : ℝ) : ℝ :=
  R_base + R_prod + R_mark

noncomputable def CBR
    (R_base R_prod R_mark R_coup lam t₀ t_int t_seq : ℝ) : ℝ :=
  StS (R_base + R_prod + R_mark + R_coup) lam t₀ t_int /
  StS (R_base + R_prod + R_mark) lam t₀ t_seq

noncomputable def η_coup (R_base R_prod R_mark R_coup : ℝ) : ℝ :=
  R_coup / R₀_integrated R_base R_prod R_mark R_coup

theorem StS_denominator_pos (t₀ t : ℝ) (ht₀ : t₀ > 0) (ht : t ≥ 0) :
    t + t₀ > 0 := by
  linarith

theorem StS_well_defined (t₀ t : ℝ) (ht₀ : t₀ > 0) (ht : t ≥ 0) :
    t + t₀ ≠ 0 := by
  have h := StS_denominator_pos t₀ t ht₀ ht
  linarith

theorem StS_max_value (R₀ lam t₀ : ℝ) (ht₀ : t₀ > 0) :
    StS R₀ lam t₀ 0 = R₀ / t₀ := by
  simp [StS, Real.exp_zero]

theorem MarketResponse_pos (R₀ lam t : ℝ) (hR₀_pos : R₀ > 0) :
    MarketResponse R₀ lam t > 0 := by
  unfold MarketResponse
  apply mul_pos hR₀_pos
  exact Real.exp_pos _

theorem TemporalDecay_bounds (lam t : ℝ) (ht : t ≥ 0) (hlam : lam > 0) :
    0 < TemporalDecay lam t ∧ TemporalDecay lam t ≤ 1 := by
  constructor
  · unfold TemporalDecay; exact Real.exp_pos _
  · unfold TemporalDecay
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith

theorem trend_half_life (lam : ℝ) (hlam : lam > 0) :
    TemporalDecay lam (Real.log 2 / lam) = 1 / 2 := by
  unfold TemporalDecay
  have hne : lam ≠ 0 := ne_of_gt hlam
  rw [show -lam * (Real.log 2 / lam) = -Real.log 2 by field_simp]
  rw [Real.exp_neg, Real.exp_log (by norm_num : (2:ℝ) > 0)]
  norm_num

theorem CBR_eq_one_iff_no_coupling
    (R_base R_prod R_mark lam t₀ t : ℝ)
    (ht₀ : t₀ > 0) (ht : t ≥ 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0) :
    CBR R_base R_prod R_mark 0 lam t₀ t t = 1 := by
  have hden : t + t₀ > 0 := StS_denominator_pos t₀ t ht₀ ht
  have hStS_pos : StS (R_base + R_prod + R_mark) lam t₀ t > 0 := by
    unfold StS
    apply div_pos
    · exact mul_pos hR_base_pos (Real.exp_pos _)
    · exact hden
  unfold CBR
  rw [add_zero]
  exact div_self (ne_of_gt hStS_pos)

theorem η_coup_bounds
    (R_base R_prod R_mark R_coup : ℝ)
    (hR_coup : R_coup ≥ 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0) :
    0 ≤ η_coup R_base R_prod R_mark R_coup ∧
    η_coup R_base R_prod R_mark R_coup < 1 := by
  have hden_pos : R₀_integrated R_base R_prod R_mark R_coup > 0 := by
    unfold R₀_integrated
    linarith
  unfold η_coup
  constructor
  · exact div_nonneg hR_coup (le_of_lt hden_pos)
  · rw [div_lt_one hden_pos]
    unfold R₀_integrated
    linarith

theorem decay_rate_estimator_well_defined
    (TS₁ TS₂ t₁ t₂ : ℝ)
    (hTS₁ : TS₁ > 0) (hTS₂ : TS₂ > 0)
    (hTS_decay : TS₁ > TS₂)
    (ht_order : t₁ < t₂) :
    Real.log (TS₁ / TS₂) / (t₂ - t₁) > 0 := by
  apply div_pos
  · apply Real.log_pos
    rw [lt_div_iff₀ hTS₂]
    linarith
  · linarith

theorem StS_strictly_decreasing
    (R₀ lam t₀ : ℝ) (hR₀_pos : R₀ > 0) (hlam : lam > 0) (ht₀ : t₀ > 0) :
    StrictAntiOn (StS R₀ lam t₀) (Ici 0) := by
  have hderiv : ∀ t ∈ Ici (0:ℝ),
      HasDerivAt (StS R₀ lam t₀)
        (R₀ * (Real.exp (-lam * t) * (-lam * (t + t₀) - 1)) / (t + t₀)^2) t := by
    intro t ht
    have ht' : t ≥ 0 := ht
    have hnum : HasDerivAt (fun s : ℝ => R₀ * Real.exp (-lam * s))
        (R₀ * (Real.exp (-lam * t) * (-lam))) t := by
      have h1 : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
        simpa using (hasDerivAt_id t).const_mul (-lam)
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-lam * s))
          (Real.exp (-lam * t) * (-lam)) t := h1.exp
      simpa [mul_assoc] using h2.const_mul R₀
    have hden : HasDerivAt (fun s : ℝ => s + t₀) 1 t := by
      simpa using (hasDerivAt_id t).add_const t₀
    have hdenne : (t + t₀) ≠ 0 := ne_of_gt (StS_denominator_pos t₀ t ht₀ ht')
    have hcomb := hnum.div hden hdenne
    have hfun : StS R₀ lam t₀ = (fun s : ℝ => R₀ * Real.exp (-lam * s)) / (fun s : ℝ => s + t₀) := by
      funext s
      simp [StS, Pi.div_apply]
    rw [hfun]
    have heq : R₀ * (Real.exp (-lam * t) * (-lam * (t + t₀) - 1)) / (t + t₀) ^ 2
        = (R₀ * (Real.exp (-lam * t) * (-lam)) * (t + t₀) - R₀ * Real.exp (-lam * t) * 1)
          / (t + t₀) ^ 2 := by ring
    rw [heq]
    exact hcomb
  apply strictAntiOn_of_deriv_neg (convex_Ici (0:ℝ))
  · apply ContinuousOn.div
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).continuousOn
    · exact (continuous_id.add continuous_const).continuousOn
    · intro t ht
      exact ne_of_gt (StS_denominator_pos t₀ t ht₀ ht)
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : t ≥ 0 := le_of_lt ht
    have hd := (hderiv t ht').deriv
    rw [hd]
    have hexp_pos : Real.exp (-lam * t) > 0 := Real.exp_pos _
    have hden_pos : (t + t₀)^2 > 0 := by positivity
    have hfactor_neg : (-lam * (t + t₀) - 1) < 0 := by
      have hpos : lam * (t + t₀) > 0 := mul_pos hlam (by linarith)
      linarith
    have hnum_neg : R₀ * (Real.exp (-lam * t) * (-lam * (t + t₀) - 1)) < 0 := by
      apply mul_neg_of_pos_of_neg hR₀_pos
      exact mul_neg_of_pos_of_neg hexp_pos hfactor_neg
    exact div_neg_of_neg_of_pos hnum_neg hden_pos

theorem StS_max_at_zero
    (R₀ lam t₀ t : ℝ)
    (hR₀_pos : R₀ > 0) (hlam : lam > 0) (ht₀ : t₀ > 0) (ht : t ≥ 0) :
    StS R₀ lam t₀ t ≤ StS R₀ lam t₀ 0 := by
  have hanti : AntitoneOn (StS R₀ lam t₀) (Ici 0) :=
    (StS_strictly_decreasing R₀ lam t₀ hR₀_pos hlam ht₀).antitoneOn
  exact hanti (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr ht) ht

theorem CBR_geq_one
    (R_base R_prod R_mark R_coup lam t₀ t_int t_seq : ℝ)
    (hlam : lam > 0) (ht₀ : t₀ > 0)
    (ht_int : t_int ≥ 0)
    (ht_seq : t_seq ≥ 0)
    (ht : t_int ≤ t_seq)
    (hcoup : R_coup > 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0) :
    CBR R_base R_prod R_mark R_coup lam t₀ t_int t_seq ≥ 1 := by
  set R₀int := R_base + R_prod + R_mark + R_coup with hR₀int_def
  set R₀seq := R_base + R_prod + R_mark with hR₀seq_def
  have hR₀int_pos : R₀int > 0 := by rw [hR₀int_def]; linarith
  have hR₀seq_pos : R₀seq > 0 := by rw [hR₀seq_def]; linarith
  have hR₀_lt : R₀seq < R₀int := by rw [hR₀int_def, hR₀seq_def]; linarith
  have hden_int_pos : t_int + t₀ > 0 := StS_denominator_pos t₀ t_int ht₀ ht_int
  have hden_seq_pos : t_seq + t₀ > 0 := StS_denominator_pos t₀ t_seq ht₀ ht_seq
  have hStS_seq_pos : StS R₀seq lam t₀ t_seq > 0 := by
    unfold StS
    exact div_pos (mul_pos hR₀seq_pos (Real.exp_pos _)) hden_seq_pos
  have step_a : StS R₀seq lam t₀ t_seq ≤ StS R₀int lam t₀ t_seq := by
    unfold StS
    apply div_le_div_of_nonneg_right _ (le_of_lt hden_seq_pos)
    exact mul_le_mul_of_nonneg_right (le_of_lt hR₀_lt) (le_of_lt (Real.exp_pos _))
  have step_b : StS R₀int lam t₀ t_seq ≤ StS R₀int lam t₀ t_int := by
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [heq]
    · have hanti : AntitoneOn (StS R₀int lam t₀) (Ici 0) :=
        (StS_strictly_decreasing R₀int lam t₀ hR₀int_pos hlam ht₀).antitoneOn
      exact hanti (mem_Ici.mpr ht_int) (mem_Ici.mpr ht_seq) ht
  unfold CBR
  rw [ge_iff_le, le_div_iff₀ hStS_seq_pos]
  calc 1 * StS R₀seq lam t₀ t_seq = StS R₀seq lam t₀ t_seq := by ring
    _ ≤ StS R₀int lam t₀ t_seq := step_a
    _ ≤ StS R₀int lam t₀ t_int := step_b

theorem CBR_lambda_invariant_equal_time
    (R_base R_prod R_mark R_coup t₀ t lam₁ lam₂ : ℝ)
    (ht₀ : t₀ > 0) (ht : t ≥ 0)
    (hlam₁ : lam₁ > 0) (hlam₂ : lam₂ > 0)
    (hR_base_pos : R_base + R_prod + R_mark > 0)
    (hcoup : R_coup > 0) :
    CBR R_base R_prod R_mark R_coup lam₁ t₀ t t =
    CBR R_base R_prod R_mark R_coup lam₂ t₀ t t := by
  have hden_pos : t + t₀ > 0 := StS_denominator_pos t₀ t ht₀ ht
  have hden_ne : t + t₀ ≠ 0 := ne_of_gt hden_pos
  have hR₀seq_pos : R_base + R_prod + R_mark > 0 := hR_base_pos
  have hseq_ne : R_base + R_prod + R_mark ≠ 0 := ne_of_gt hR₀seq_pos
  unfold CBR StS
  have key : ∀ lam' : ℝ,
      (R_base + R_prod + R_mark + R_coup) * Real.exp (-lam' * t) / (t + t₀) /
        ((R_base + R_prod + R_mark) * Real.exp (-lam' * t) / (t + t₀))
      = (R_base + R_prod + R_mark + R_coup) / (R_base + R_prod + R_mark) := by
    intro lam'
    have hexp_ne : Real.exp (-lam' * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp
  rw [key lam₁, key lam₂]

end FMCG40
