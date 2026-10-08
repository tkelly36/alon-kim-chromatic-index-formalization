import Tablet.Preamble

set_option linter.unusedVariables false

open BigOperators

-- [TABLET NODE: SamplingPairKernelSplitLowerBound]
theorem SamplingPairKernelSplitLowerBound
    (Delta : ℕ) (alpha lambda K : ℝ)
    (hDelta : 0 < (Delta : ℝ))
    (halpha_le_one : alpha ≤ 1)
    (hlambda_pos : 0 < lambda) (hlambda_le_one : lambda ≤ 1)
    (hlow :
      alpha ≤ lambda →
        K ≥ (2 / (1 + lambda) - 6 * alpha) / (Delta : ℝ)^2)
    (hhigh :
      lambda < alpha →
        K ≥ (5 / 3 + 2 * alpha) / (Delta : ℝ)^2) :
    K ≥
      (1 + (1 / 3) * lambda *
            (2 / (lambda * (1 + lambda)) - 1)) / (Delta : ℝ)^2 -
        (6 * alpha) / (Delta : ℝ)^2 := by
-- BODY
  have hD2_pos : 0 < (Delta : ℝ)^2 := sq_pos_of_pos hDelta
  by_cases hcase : alpha ≤ lambda
  · have hK := hlow hcase
    have hden_pos : 0 < 1 + lambda := by linarith
    have htarget_le :
        1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1) ≤
          2 / (1 + lambda) := by
      have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda_pos
      have hden_ne : 1 + lambda ≠ 0 := ne_of_gt hden_pos
      field_simp [hlambda_ne, hden_ne]
      nlinarith [sq_nonneg (1 - lambda)]
    have hdiv_le :
        (1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1)) /
            (Delta : ℝ)^2 ≤
          (2 / (1 + lambda)) / (Delta : ℝ)^2 := by
      exact div_le_div_of_nonneg_right htarget_le (le_of_lt hD2_pos)
    have hmain :
        (1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1)) /
            (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2 ≤
          (2 / (1 + lambda) - 6 * alpha) / (Delta : ℝ)^2 := by
      rw [sub_div]
      exact sub_le_sub_right hdiv_le ((6 * alpha) / (Delta : ℝ)^2)
    linarith
  · have hlt : lambda < alpha := lt_of_not_ge hcase
    have hK := hhigh hlt
    have hden_pos : 0 < 1 + lambda := by linarith
    have htarget_le :
        1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1) ≤
          5 / 3 := by
      have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda_pos
      have hden_ne : 1 + lambda ≠ 0 := ne_of_gt hden_pos
      field_simp [hlambda_ne, hden_ne]
      nlinarith [sq_nonneg lambda, hlambda_le_one]
    have hdiv_le :
        (1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1)) /
            (Delta : ℝ)^2 ≤
          (5 / 3) / (Delta : ℝ)^2 := by
      exact div_le_div_of_nonneg_right htarget_le (le_of_lt hD2_pos)
    have hmain :
        (1 + (1 / 3) * lambda * (2 / (lambda * (1 + lambda)) - 1)) /
            (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2 ≤
          (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 := by
      have haux :
          (5 / 3) / (Delta : ℝ)^2 -
              (6 * alpha) / (Delta : ℝ)^2 ≤
            (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 := by
        rw [← sub_div]
        apply div_le_div_of_nonneg_right _ (le_of_lt hD2_pos)
        nlinarith [hlt, hlambda_pos]
      linarith
    linarith
