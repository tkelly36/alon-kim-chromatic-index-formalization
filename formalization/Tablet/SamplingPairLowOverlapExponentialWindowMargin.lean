import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingPairLowOverlapExponentialWindowMargin]
theorem SamplingPairLowOverlapExponentialWindowMargin
    (alpha gamma0 lambda : ℝ)
    (halpha_pos : 0 < alpha)
    (halpha_le_one : alpha ≤ 1)
    (hgamma0_nonneg : 0 ≤ gamma0)
    (hlambda_ge : alpha ≤ lambda)
    (hlambda_le_one : lambda ≤ 1)
    (htail : Real.exp (-gamma0) * (1 + 1 / alpha) ≤ alpha) :
      2 *
          (∫ x in (0 : ℝ)..gamma0,
            ∫ y in x..gamma0,
              ((1 - alpha) * Real.exp (-(lambda * x))) *
                ((1 - alpha) * Real.exp (-y))) ≥
        2 / (1 + lambda) - 6 * alpha := by
-- BODY
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le halpha_pos hlambda_ge
  have hden_pos : 0 < 1 + lambda := by linarith
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hA_nonneg : 0 ≤ (1 - alpha) ^ 2 := sq_nonneg _
  have exp_int (c a b : ℝ) (hc : 0 < c) :
      (∫ y in a..b, Real.exp (-(c * y))) =
        (Real.exp (-(c * a)) - Real.exp (-(c * b))) / c := by
    have hne : c ≠ 0 := ne_of_gt hc
    have hderiv : ∀ y : ℝ,
        HasDerivAt (fun t : ℝ => -(Real.exp (-(c * t)) / c))
          (Real.exp (-(c * y))) y := by
      intro y
      have hinner : HasDerivAt (fun t : ℝ => -(c * t)) (-c) y := by
        simpa [neg_mul] using ((hasDerivAt_id y).const_mul (-c))
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(c * t)))
          (Real.exp (-(c * y)) * (-c)) y := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Real.hasDerivAt_exp (-(c * y))).comp y hinner
      have h2 := h1.div_const c
      have h3 := h2.neg
      simpa [hne, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _hy => hderiv y)
      ((Real.continuous_exp.comp
        (by fun_prop : Continuous fun y : ℝ => -(c * y))).intervalIntegrable a b)]
    field_simp [hne]
    simp
    ring
  let J : ℝ := ∫ x in (0 : ℝ)..gamma0, Real.exp (-(lambda * x)) *
      (Real.exp (-x) - Real.exp (-gamma0))
  have hinner (x : ℝ) :
      (∫ y in x..gamma0,
          ((1 - alpha) * Real.exp (-(lambda * x))) *
            ((1 - alpha) * Real.exp (-y))) =
        (1 - alpha)^2 * Real.exp (-(lambda * x)) *
          (Real.exp (-x) - Real.exp (-gamma0)) := by
    rw [show (fun y : ℝ =>
          ((1 - alpha) * Real.exp (-(lambda * x))) *
            ((1 - alpha) * Real.exp (-y))) =
        fun y : ℝ => ((1 - alpha) * Real.exp (-(lambda * x))) *
          ((1 - alpha) * Real.exp (-y)) by rfl]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
    have hyint :
        (∫ y in x..gamma0, Real.exp (-y)) =
          Real.exp (-x) - Real.exp (-gamma0) := by
      simpa using exp_int 1 x gamma0 zero_lt_one
    rw [hyint]
    ring
  have houter_eq :
      (∫ x in (0 : ℝ)..gamma0,
            ∫ y in x..gamma0,
              ((1 - alpha) * Real.exp (-(lambda * x))) *
                ((1 - alpha) * Real.exp (-y))) =
        (1 - alpha)^2 * J := by
    simp_rw [hinner]
    have hfun :
        (fun x : ℝ => (1 - alpha) ^ 2 * Real.exp (-(lambda * x)) *
            (Real.exp (-x) - Real.exp (-gamma0))) =
          fun x : ℝ => (1 - alpha) ^ 2 *
            (Real.exp (-(lambda * x)) * (Real.exp (-x) - Real.exp (-gamma0))) := by
      ext x
      ring
    rw [hfun, intervalIntegral.integral_const_mul]
  have hJ_eq :
      J =
        (1 - Real.exp (-((lambda + 1) * gamma0))) / (lambda + 1) -
          Real.exp (-gamma0) *
            ((1 - Real.exp (-(lambda * gamma0))) / lambda) := by
    dsimp [J]
    have hsplit :
        (fun x : ℝ => Real.exp (-(lambda * x)) *
            (Real.exp (-x) - Real.exp (-gamma0))) =
          fun x : ℝ =>
            Real.exp (-((lambda + 1) * x)) -
              Real.exp (-gamma0) * Real.exp (-(lambda * x)) := by
      ext x
      rw [mul_sub, ← Real.exp_add]
      congr 1
      · congr 1
        ring
      ring
    rw [hsplit]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul]
      rw [exp_int (lambda + 1) 0 gamma0 (by linarith)]
      rw [exp_int lambda 0 gamma0 hlambda_pos]
      simp
    · exact (Real.continuous_exp.comp
        (by fun_prop : Continuous fun x : ℝ =>
          -((lambda + 1) * x))).intervalIntegrable 0 gamma0
    · exact ((continuous_const.mul
        (Real.continuous_exp.comp
          (by fun_prop : Continuous fun x : ℝ =>
            -(lambda * x)))).intervalIntegrable 0 gamma0)
  have hJ_lower :
      J ≥ 1 / (1 + lambda) - alpha := by
    rw [hJ_eq]
    have hexp_nonneg1 : 0 ≤ Real.exp (-((lambda + 1) * gamma0)) :=
      (Real.exp_pos _).le
    have htail1 :
        Real.exp (-((lambda + 1) * gamma0)) / (lambda + 1) ≤
          Real.exp (-gamma0) := by
      have hle_exp :
          Real.exp (-((lambda + 1) * gamma0)) ≤ Real.exp (-gamma0) := by
        rw [Real.exp_le_exp]
        have : gamma0 ≤ (lambda + 1) * gamma0 := by
          nlinarith [hgamma0_nonneg, hlambda_pos]
        linarith
      calc
        Real.exp (-((lambda + 1) * gamma0)) / (lambda + 1)
            ≤ Real.exp (-((lambda + 1) * gamma0)) / 1 := by
              have hone_le : (1 : ℝ) ≤ lambda + 1 := by linarith
              exact div_le_div_of_nonneg_left hexp_nonneg1 zero_lt_one hone_le
        _ = Real.exp (-((lambda + 1) * gamma0)) := by ring
        _ ≤ Real.exp (-gamma0) := hle_exp
    have htail2 :
        Real.exp (-gamma0) *
            ((1 - Real.exp (-(lambda * gamma0))) / lambda) ≤
          Real.exp (-gamma0) * (1 / alpha) := by
      have hnum_le : 1 - Real.exp (-(lambda * gamma0)) ≤ 1 := by
        linarith [Real.exp_pos (-(lambda * gamma0))]
      have hfrac_le :
          (1 - Real.exp (-(lambda * gamma0))) / lambda ≤ 1 / alpha := by
        have hfrac_le_one_lam :
            (1 - Real.exp (-(lambda * gamma0))) / lambda ≤ 1 / lambda := by
          exact div_le_div_of_nonneg_right hnum_le hlambda_pos.le
        have hone_lam_le : 1 / lambda ≤ 1 / alpha :=
          one_div_le_one_div_of_le halpha_pos hlambda_ge
        exact hfrac_le_one_lam.trans hone_lam_le
      exact mul_le_mul_of_nonneg_left hfrac_le (Real.exp_pos _).le
    have htail_total :
        Real.exp (-((lambda + 1) * gamma0)) / (lambda + 1) +
          Real.exp (-gamma0) *
            ((1 - Real.exp (-(lambda * gamma0))) / lambda) ≤ alpha := by
      calc
        Real.exp (-((lambda + 1) * gamma0)) / (lambda + 1) +
            Real.exp (-gamma0) *
              ((1 - Real.exp (-(lambda * gamma0))) / lambda)
            ≤ Real.exp (-gamma0) + Real.exp (-gamma0) * (1 / alpha) :=
              add_le_add htail1 htail2
        _ = Real.exp (-gamma0) * (1 + 1 / alpha) := by ring
        _ ≤ alpha := htail
    have hmain :
        (1 - Real.exp (-((lambda + 1) * gamma0))) / (lambda + 1) -
            Real.exp (-gamma0) *
              ((1 - Real.exp (-(lambda * gamma0))) / lambda) ≥
          1 / (1 + lambda) - alpha := by
      have hden_eq : lambda + 1 = 1 + lambda := by ring
      rw [hden_eq] at htail_total ⊢
      have :
          (1 - Real.exp (-((1 + lambda) * gamma0))) / (1 + lambda) =
            1 / (1 + lambda) -
              Real.exp (-((1 + lambda) * gamma0)) / (1 + lambda) := by
        ring
      rw [this]
      linarith
    exact hmain
  have htarget_alg :
      2 * ((1 - alpha)^2 * (1 / (1 + lambda) - alpha)) ≥
        2 / (1 + lambda) - 6 * alpha := by
    let s : ℝ := 1 / (1 + lambda)
    have htarget_s :
        2 * ((1 - alpha)^2 * (s - alpha)) ≥ 2 * s - 6 * alpha := by
      have hs_le_one : s ≤ 1 := by
        dsimp [s]
        exact (div_le_one hden_pos).2 (by linarith)
      have hs_nonneg : 0 ≤ s := by
        dsimp [s]
        positivity
      nlinarith [sq_nonneg alpha, sq_nonneg (1 - alpha), hs_le_one,
        hs_nonneg, halpha_nonneg, halpha_le_one, hlambda_le_one]
    simpa [s] using htarget_s
  have hprod_lower :
      (1 - alpha)^2 * J ≥
        (1 - alpha)^2 * (1 / (1 + lambda) - alpha) := by
    exact mul_le_mul_of_nonneg_left hJ_lower hA_nonneg
  rw [houter_eq]
  linarith
