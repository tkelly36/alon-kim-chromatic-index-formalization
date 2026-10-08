import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- [TABLET NODE: BernoulliChernoffRateLowerBound]
theorem BernoulliChernoffRateLowerBound (r : ℝ) (hr : 0 ≤ r) :
    r ^ 2 / (2 + r) ≤ (1 + r) * Real.log (1 + r) - r := by
-- BODY
  have hd : 0 < 2 + r := by linarith
  have hx : r / (2 + r) < 1 := (div_lt_one hd).2 (by linarith)
  have h := Real.sum_range_le_log_div (div_nonneg hr hd.le) hx 1
  have heq : (1 + r / (2 + r)) / (1 - r / (2 + r)) = 1 + r := by
    field_simp
    ring
  rw [heq] at h
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one,
    div_one] at h
  apply (div_le_iff₀ hd).2
  have hh := (div_le_iff₀ hd).1 h
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hh)]
