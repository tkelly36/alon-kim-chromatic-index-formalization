import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingOneVertexAnalyticEstimate]
theorem SamplingOneVertexAnalyticEstimate :
    ∀ (Delta : ℕ) (gamma : ℝ),
      0 < (Delta : ℝ) →
      0 ≤ gamma →
      gamma ≤ (Delta : ℝ) →
      abs (((1 / (Delta : ℝ)) *
            (∫ x in (0 : ℝ)..gamma, (1 - x / (Delta : ℝ)) ^ Delta)) -
          (1 - Real.exp (-gamma)) / (Delta : ℝ)) ≤
        2 / (Delta : ℝ)^2 := by
-- BODY
  intro Delta gamma hD hgamma_nonneg hgamma_le
  let d : ℝ := (Delta : ℝ)
  have hd_pos : 0 < d := hD
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have h0gamma : (0 : ℝ) ≤ gamma := hgamma_nonneg
  have hpoly_int : IntervalIntegrable (fun x : ℝ => (1 - x / d) ^ Delta)
      MeasureTheory.volume 0 gamma := by
    exact ((continuous_const.sub (continuous_id.div_const d)).pow Delta).intervalIntegrable 0 gamma
  have hexp_int : IntervalIntegrable (fun x : ℝ => Real.exp (-x))
      MeasureTheory.volume 0 gamma := by
    exact (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 gamma
  have hpoly_le_exp :
      (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) ≤
        ∫ x in (0 : ℝ)..gamma, Real.exp (-x) := by
    refine intervalIntegral.integral_mono_on h0gamma hpoly_int hexp_int ?_
    intro x hx
    have hx_le_d : x ≤ (Delta : ℝ) := hx.2.trans hgamma_le
    simpa [d] using Real.one_sub_div_pow_le_exp_neg (n := Delta) (t := x) hx_le_d
  have hdiff_nonneg :
      0 ≤ (∫ x in (0 : ℝ)..gamma, Real.exp (-x)) -
        (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) :=
    sub_nonneg.mpr hpoly_le_exp
  have hdiff_int : IntervalIntegrable
      (fun x : ℝ => Real.exp (-x) - (1 - x / d) ^ Delta)
      MeasureTheory.volume 0 (Delta : ℝ) := by
    refine IntervalIntegrable.sub ?_ ?_
    · exact (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 (Delta : ℝ)
    · exact ((continuous_const.sub (continuous_id.div_const d)).pow Delta).intervalIntegrable 0
        (Delta : ℝ)
  have hdiff_ae_nonneg :
      ((fun _ : ℝ => (0 : ℝ)) ≤ᵐ[MeasureTheory.volume.restrict
        (Set.Ioc (0 : ℝ) (Delta : ℝ))]
        (fun x : ℝ => Real.exp (-x) - (1 - x / d) ^ Delta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    apply sub_nonneg.mpr
    have hx_le_d : x ≤ (Delta : ℝ) := hx.2
    simpa [d] using Real.one_sub_div_pow_le_exp_neg (n := Delta) (t := x) hx_le_d
  have hdiff_le_full_int :
      (∫ x in (0 : ℝ)..gamma, Real.exp (-x) - (1 - x / d) ^ Delta) ≤
        ∫ x in (0 : ℝ)..(Delta : ℝ), Real.exp (-x) - (1 - x / d) ^ Delta := by
    refine intervalIntegral.integral_mono_interval
      (f := fun x : ℝ => Real.exp (-x) - (1 - x / d) ^ Delta)
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := gamma) (c := (0 : ℝ))
      (d := (Delta : ℝ)) le_rfl h0gamma hgamma_le hdiff_ae_nonneg hdiff_int
  have hgamma_diff_eq :
      (∫ x in (0 : ℝ)..gamma, Real.exp (-x) - (1 - x / d) ^ Delta) =
        (∫ x in (0 : ℝ)..gamma, Real.exp (-x)) -
          (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) := by
    rw [intervalIntegral.integral_sub hexp_int hpoly_int]
  have hpoly_full :
      (∫ x in (0 : ℝ)..(Delta : ℝ), (1 - x / d) ^ Delta) =
        (Delta : ℝ) / (Delta + 1 : ℝ) := by
    rw [show (fun x : ℝ => (1 - x / d) ^ Delta) =
        fun x : ℝ => (fun y : ℝ => y ^ Delta) (1 - x / d) by rfl]
    rw [intervalIntegral.integral_comp_sub_div
      (f := fun y : ℝ => y ^ Delta) (a := (0 : ℝ)) (b := (Delta : ℝ))
      hd_ne (1 : ℝ)]
    simp [d, hd_ne, integral_pow, div_eq_mul_inv]
  have hexp_full :
      (∫ x in (0 : ℝ)..(Delta : ℝ), Real.exp (-x)) =
        1 - Real.exp (-(Delta : ℝ)) := by
    rw [intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => Real.exp x) (a := (0 : ℝ)) (b := (Delta : ℝ))]
    simp [integral_exp]
  have hfull_sub :
      (∫ x in (0 : ℝ)..(Delta : ℝ), Real.exp (-x) - (1 - x / d) ^ Delta) =
        (1 - Real.exp (-(Delta : ℝ))) - (Delta : ℝ) / (Delta + 1 : ℝ) := by
    rw [intervalIntegral.integral_sub]
    · rw [hexp_full, hpoly_full]
    · exact (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 (Delta : ℝ)
    · exact ((continuous_const.sub (continuous_id.div_const d)).pow Delta).intervalIntegrable 0
        (Delta : ℝ)
  have hfull_le :
      (∫ x in (0 : ℝ)..(Delta : ℝ), Real.exp (-x) - (1 - x / d) ^ Delta) ≤
        1 / d := by
    rw [hfull_sub]
    have hden_pos : 0 < (Delta + 1 : ℝ) := by positivity
    have hstep :
        (1 - Real.exp (-(Delta : ℝ))) - (Delta : ℝ) / (Delta + 1 : ℝ) ≤
          1 - (Delta : ℝ) / (Delta + 1 : ℝ) := by
      linarith [Real.exp_pos (-(Delta : ℝ))]
    have hone : 1 - (Delta : ℝ) / (Delta + 1 : ℝ) = 1 / (Delta + 1 : ℝ) := by
      field_simp [hden_pos.ne']
      norm_num
    have hle_den : 1 / (Delta + 1 : ℝ) ≤ 1 / d := by
      have hd_le : d ≤ (Delta + 1 : ℝ) := by simp [d]
      exact one_div_le_one_div_of_le hd_pos hd_le
    exact hstep.trans (by simpa [hone, d] using hle_den)
  have hdiff_le :
      (∫ x in (0 : ℝ)..gamma, Real.exp (-x)) -
        (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) ≤ 1 / d := by
    rw [← hgamma_diff_eq]
    exact hdiff_le_full_int.trans hfull_le
  have hexp_gamma :
      (∫ x in (0 : ℝ)..gamma, Real.exp (-x)) = 1 - Real.exp (-gamma) := by
    rw [intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => Real.exp x) (a := (0 : ℝ)) (b := gamma)]
    simp [integral_exp]
  have habs_inner :
      abs ((∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) -
          (1 - Real.exp (-gamma))) ≤ 1 / d := by
    rw [← hexp_gamma]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hscale :
      abs (((1 / d) * (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta)) -
          (1 - Real.exp (-gamma)) / d) =
        (1 / d) *
          abs ((∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) -
            (1 - Real.exp (-gamma))) := by
    have heq :
        ((1 / d) * (∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta)) -
          (1 - Real.exp (-gamma)) / d =
          (1 / d) *
            ((∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) -
              (1 - Real.exp (-gamma))) := by
      field_simp [hd_ne]
    rw [heq, abs_mul]
    have : abs (1 / d) = 1 / d := abs_of_nonneg (by positivity)
    rw [this]
  rw [show (Delta : ℝ) = d by rfl]
  rw [hscale]
  have hmain :
      (1 / d) *
          abs ((∫ x in (0 : ℝ)..gamma, (1 - x / d) ^ Delta) -
            (1 - Real.exp (-gamma))) ≤
        (1 / d) * (1 / d) := by
    exact mul_le_mul_of_nonneg_left habs_inner (by positivity)
  have hsq : (1 / d) * (1 / d) ≤ 2 / d ^ 2 := by
    field_simp [hd_ne, pow_two]
    nlinarith [sq_nonneg d]
  exact hmain.trans hsq
