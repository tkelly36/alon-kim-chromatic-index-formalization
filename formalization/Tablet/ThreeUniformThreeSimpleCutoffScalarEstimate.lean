import Tablet.Preamble

-- [TABLET NODE: ThreeUniformThreeSimpleCutoffScalarEstimate]
theorem ThreeUniformThreeSimpleCutoffScalarEstimate
    (d p t : ℝ) (hd : 900000 ≤ d)
    (hp : 1.031 - 9 / d < p) (hpupper : p ≤ 9 / 2)
    (ht : t ^ 2 ≤ p ^ 3 / 27) :
    -1 / d + 1 - p / 9 + t / 27 < 0.89291 := by
-- BODY
  have hdpos : 0 < d := by linarith
  have hsmall : 9 / d ≤ (1 : ℝ) / 100000 := by
    apply (div_le_iff₀ hdpos).2
    linarith
  have hpbase : (103099 : ℝ) / 100000 ≤ p := by linarith
  let u := p - (103099 : ℝ) / 100000
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have huupper : u ≤ 7 / 2 := by dsimp [u]; linarith
  have hcubic : u ^ 3 ≤ (7 / 2 : ℝ) * u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huupper) (sq_nonneg u)]
  have hpoly : p ^ 3 / 27 ≤ ((2015 : ℝ) / 10000 + u / 2) ^ 2 := by
    dsimp [u] at *
    nlinarith [sq_nonneg (p - (103099 : ℝ) / 100000)]
  have htupper : t ≤ (2015 : ℝ) / 10000 + u / 2 := by
    nlinarith
  have hinv : -1 / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hdpos.le
  dsimp [u] at htupper
  linarith
