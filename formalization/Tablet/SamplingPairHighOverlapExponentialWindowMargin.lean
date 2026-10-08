import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingPairHighOverlapExponentialWindowMargin]
theorem SamplingPairHighOverlapExponentialWindowMargin
    (L alpha : ℝ)
    (hnumeric :
      (5 / 3 + 2 * alpha) ≤
        2 * ((1 - alpha)^2 * Real.exp (-(alpha * L)) *
          (∫ x in (0 : ℝ)..L, Real.exp (-x) - Real.exp (-L)))) :
      (5 / 3 + 2 * alpha) ≤
        2 *
          (∫ x in (0 : ℝ)..L,
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y))) := by
-- BODY
  have exp_int_one (a b : ℝ) :
      (∫ y in a..b, Real.exp (-y)) = Real.exp (-a) - Real.exp (-b) := by
    have hderiv : ∀ y : ℝ,
        HasDerivAt (fun t : ℝ => - Real.exp (-t)) (Real.exp (-y)) y := by
      intro y
      have hinner : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) y := by
        simpa using (hasDerivAt_id y).neg
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t))
          (Real.exp (-y) * (-1 : ℝ)) y := by
        simpa using (Real.hasDerivAt_exp (-y)).comp y hinner
      have h2 := h1.neg
      simpa using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _hy => hderiv y)
      ((Real.continuous_exp.comp
        (by fun_prop : Continuous fun y : ℝ => -y)).intervalIntegrable a b)]
    ring
  have hinner (x : ℝ) :
      (∫ y in x..L,
          ((1 - alpha) * Real.exp (-(alpha * L))) *
            ((1 - alpha) * Real.exp (-y))) =
        (1 - alpha)^2 * Real.exp (-(alpha * L)) *
          (Real.exp (-x) - Real.exp (-L)) := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
    rw [exp_int_one x L]
    ring
  have houter :
      (∫ x in (0 : ℝ)..L,
          ∫ y in x..L,
            ((1 - alpha) * Real.exp (-(alpha * L))) *
              ((1 - alpha) * Real.exp (-y))) =
        (1 - alpha)^2 * Real.exp (-(alpha * L)) *
          (∫ x in (0 : ℝ)..L, Real.exp (-x) - Real.exp (-L)) := by
    simp_rw [hinner]
    rw [← intervalIntegral.integral_const_mul]
  rwa [houter]
