import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTripleRealChamberEstimate]
theorem SamplingTripleRealChamberEstimate
    (x y z tau : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (htau : 0 ≤ tau) :
    2 / ((1 + x) * (x + y + z + tau)) +
        2 / ((1 + y) * (x + y + z + tau)) +
          2 / ((1 + z) * (x + y + z + tau)) ≤
      1 + (1 / 3) *
        ((2 / ((1 + x) * x) - 1) +
          (2 / ((1 + y) * y) - 1) +
            (2 / ((1 + z) * z) - 1)) := by
-- BODY
  have hSpos : 0 < x + y + z := by positivity
  have hMpos : 0 < x + y + z + tau := by linarith
  have hx1pos : 0 < 1 + x := by linarith
  have hy1pos : 0 < 1 + y := by linarith
  have hz1pos : 0 < 1 + z := by linarith
  have hterm_x :
      2 / ((1 + x) * (x + y + z + tau)) ≤
        2 / ((1 + x) * (x + y + z)) := by
    have hden : (1 + x) * (x + y + z) ≤ (1 + x) * (x + y + z + tau) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hinv :
        1 / ((1 + x) * (x + y + z + tau)) ≤
          1 / ((1 + x) * (x + y + z)) := by
      exact one_div_le_one_div_of_le (mul_pos hx1pos hSpos) hden
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  have hterm_y :
      2 / ((1 + y) * (x + y + z + tau)) ≤
        2 / ((1 + y) * (x + y + z)) := by
    have hden : (1 + y) * (x + y + z) ≤ (1 + y) * (x + y + z + tau) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hinv :
        1 / ((1 + y) * (x + y + z + tau)) ≤
          1 / ((1 + y) * (x + y + z)) := by
      exact one_div_le_one_div_of_le (mul_pos hy1pos hSpos) hden
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  have hterm_z :
      2 / ((1 + z) * (x + y + z + tau)) ≤
        2 / ((1 + z) * (x + y + z)) := by
    have hden : (1 + z) * (x + y + z) ≤ (1 + z) * (x + y + z + tau) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hinv :
        1 / ((1 + z) * (x + y + z + tau)) ≤
          1 / ((1 + z) * (x + y + z)) := by
      exact one_div_le_one_div_of_le (mul_pos hz1pos hSpos) hden
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  have hreduce :
      2 / ((1 + x) * (x + y + z + tau)) +
          2 / ((1 + y) * (x + y + z + tau)) +
            2 / ((1 + z) * (x + y + z + tau)) ≤
        2 / ((1 + x) * (x + y + z)) +
          2 / ((1 + y) * (x + y + z)) +
            2 / ((1 + z) * (x + y + z)) := by
    linarith
  have hkey :
      0 ≤ (x + y + z) *
            (1 / (x * (1 + x)) + 1 / (y * (1 + y)) + 1 / (z * (1 + z))) -
          3 * (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) := by
    have hident :
        (x + y + z) *
            (1 / (x * (1 + x)) + 1 / (y * (1 + y)) + 1 / (z * (1 + z))) -
          3 * (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) =
        (x - y) ^ 2 * (x + y + 1) / (x * y * (1 + x) * (1 + y)) +
          (x - z) ^ 2 * (x + z + 1) / (x * z * (1 + x) * (1 + z)) +
            (y - z) ^ 2 * (y + z + 1) / (y * z * (1 + y) * (1 + z)) := by
      field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz, ne_of_gt hx1pos,
        ne_of_gt hy1pos, ne_of_gt hz1pos]
      ring
    rw [hident]
    positivity
  have halg :
      2 / ((1 + x) * (x + y + z)) +
          2 / ((1 + y) * (x + y + z)) +
            2 / ((1 + z) * (x + y + z)) ≤
        1 + (1 / 3) *
          ((2 / ((1 + x) * x) - 1) +
            (2 / ((1 + y) * y) - 1) +
              (2 / ((1 + z) * z) - 1)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz, ne_of_gt hSpos,
      ne_of_gt hx1pos, ne_of_gt hy1pos, ne_of_gt hz1pos] at hkey ⊢
    nlinarith
  exact hreduce.trans halg
