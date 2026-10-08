import Tablet.RandomIndependentSetSampling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingIntervalLIntegralOfRealConversion]
theorem SamplingIntervalLIntegralOfRealConversion
    (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hf_int : IntervalIntegrable f MeasureTheory.volume a b)
    (hf_nonneg : ∀ x : ℝ, x ∈ Set.Ioc a b → 0 ≤ f x) :
    (∫⁻ x in Set.Ioc a b, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x in a..b, f x) := by
-- BODY
  rw [intervalIntegral.integral_of_le hab]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int.1
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc |>.2
      (Filter.Eventually.of_forall hf_nonneg))).symm
