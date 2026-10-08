import Tablet.Preamble

-- [TABLET NODE: ThreeUniformTwoSimpleMatrixRescaling]
theorem ThreeUniformTwoSimpleMatrixRescaling
    (r Q P L : ℝ) (hr : 1 ≤ r) (hQ : 0 ≤ Q) (hL : L ≤ 3)
    (hbound : (1 / 9 : ℝ) * Q + (1 / 27 : ℝ) * P - (1 / 27 : ℝ) * L ≤
      2 / (3 : ℝ) ^ 5) :
    r ^ 2 / 9 * Q + r ^ 3 / 27 * P - r / 27 * L ≤
      r ^ 3 * (2 / (3 : ℝ) ^ 5) + (r ^ 2 - 1) * r / 9 := by
-- BODY
  have hr0 : 0 ≤ r := by linarith
  have hscale := mul_le_mul_of_nonneg_left hbound (pow_nonneg hr0 3)
  have hpair : 0 ≤ r ^ 2 * (r - 1) * Q :=
    mul_nonneg (mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr)) hQ
  have hcoeff : 0 ≤ (r ^ 2 - 1) * r := by
    apply mul_nonneg _ hr0
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left hL hcoeff
  nlinarith only [hscale, hpair, hlinear]
