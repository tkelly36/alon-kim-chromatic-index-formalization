import Tablet.Preamble

-- [TABLET NODE: SamplingNonadjacentPairChamberIntegrandNonnegative]
theorem SamplingNonadjacentPairChamberIntegrandNonnegative :
    ∀ Delta : ℕ, ∀ gamma : ℝ, ∀ c : ℕ, ∀ x y : ℝ,
      0 < gamma →
        gamma ≤ (Delta : ℝ) →
          c ≤ Delta →
            0 ≤ x →
              x ≤ y →
                y ≤ gamma →
                  0 ≤
                    (1 - x / (Delta : ℝ)) ^ (Delta - c) *
                      (1 - y / (Delta : ℝ)) ^ Delta := by
-- BODY
  intro Delta gamma c x y hgamma_pos hgamma_le _hc_le hx_nonneg hxy hy_le_gamma
  have hDelta_pos : (0 : ℝ) < (Delta : ℝ) := by
    linarith
  have hx_le_Delta : x ≤ (Delta : ℝ) := by
    exact hxy.trans (hy_le_gamma.trans hgamma_le)
  have hy_le_Delta : y ≤ (Delta : ℝ) := by
    exact hy_le_gamma.trans hgamma_le
  have hx_factor_nonneg : 0 ≤ 1 - x / (Delta : ℝ) := by
    have hx_div_le_one : x / (Delta : ℝ) ≤ 1 := by
      exact (div_le_one hDelta_pos).2 hx_le_Delta
    linarith
  have hy_factor_nonneg : 0 ≤ 1 - y / (Delta : ℝ) := by
    have hy_div_le_one : y / (Delta : ℝ) ≤ 1 := by
      exact (div_le_one hDelta_pos).2 hy_le_Delta
    linarith
  exact
    mul_nonneg
      (pow_nonneg hx_factor_nonneg (Delta - c))
      (pow_nonneg hy_factor_nonneg Delta)
