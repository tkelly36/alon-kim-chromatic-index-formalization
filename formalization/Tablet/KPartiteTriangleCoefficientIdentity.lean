import Tablet.Preamble

-- [TABLET NODE: KPartiteTriangleCoefficientIdentity]
theorem KPartiteTriangleCoefficientIdentity :
    ∀ k : ℕ, 3 ≤ k →
      ((2 : ℝ) / 3) *
          Real.sqrt (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) *
          Real.sqrt (((k : ℝ) - 2) / k) =
        (Nat.choose k 3 : ℝ) /
          (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2) := by
-- BODY
  intro k hk
  have hk0 : (0 : ℝ) < k := by
    exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by
    exact_mod_cast (by omega : 2 ≤ k)
  have hkm2 : 0 ≤ (k : ℝ) - 2 := by
    linarith
  have hfrac1_nonneg :
      0 ≤ ((k : ℝ) - 2) / (2 * ((k : ℝ) - 1)) := by
    exact div_nonneg hkm2 (mul_nonneg (by norm_num) (by linarith))
  have hfrac2_nonneg : 0 ≤ ((k : ℝ) - 2) / k := by
    exact div_nonneg hkm2 (le_of_lt hk0)
  have hchoose_rec_nat :
      Nat.choose k 3 * 3 = Nat.choose k 2 * (k - 2) := by
    simpa using (Nat.choose_succ_right_eq k 2)
  have hchoose_rec :
      (Nat.choose k 3 : ℝ) =
        (Nat.choose k 2 : ℝ) * ((k : ℝ) - 2) / 3 := by
    have hcast :
        ((Nat.choose k 3 * 3 : ℕ) : ℝ) =
          ((Nat.choose k 2 * (k - 2) : ℕ) : ℝ) := by
      exact_mod_cast hchoose_rec_nat
    norm_num at hcast
    have hk2sub : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      norm_num [Nat.cast_sub (by omega : 2 ≤ k)]
    rw [hk2sub] at hcast
    linarith
  have hCpos : 0 < (Nat.choose k 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ k)
  have hCrpow :
      (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2) =
        (Nat.choose k 2 : ℝ) * Real.sqrt (Nat.choose k 2 : ℝ) := by
    calc
      (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2)
          = (Nat.choose k 2 : ℝ) ^ (1 + (1 / 2 : ℝ)) := by
              norm_num
      _ = (Nat.choose k 2 : ℝ) *
            ((Nat.choose k 2 : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hCpos]
              simp
      _ = (Nat.choose k 2 : ℝ) * Real.sqrt (Nat.choose k 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
  rw [hchoose_rec, hCrpow]
  field_simp [ne_of_gt hCpos]
  rw [Nat.cast_choose_two]
  field_simp [ne_of_gt hk0,
    ne_of_gt (by nlinarith : (0 : ℝ) < (k : ℝ) - 1),
    ne_of_gt (by norm_num : (0 : ℝ) < (2 : ℝ)),
    ne_of_gt (by norm_num : (0 : ℝ) < (3 : ℝ))]
  have hprod :
      (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1)) *
          ((k : ℝ) - 2) / (k : ℝ) *
          ((k : ℝ) * ((k : ℝ) - 1) / 2)) =
        (((k : ℝ) - 2) / 2) ^ 2 := by
    field_simp [ne_of_gt hk0,
      ne_of_gt (by nlinarith : (0 : ℝ) < (k : ℝ) - 1)]
  have hhalf_nonneg : 0 ≤ ((k : ℝ) - 2) / 2 := by
    positivity
  calc
    2 * Real.sqrt (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) *
          Real.sqrt (((k : ℝ) - 2) / k) *
          Real.sqrt ((k : ℝ) * ((k : ℝ) - 1) / 2)
        = 2 *
            (Real.sqrt (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) *
              Real.sqrt (((k : ℝ) - 2) / k)) *
            Real.sqrt ((k : ℝ) * ((k : ℝ) - 1) / 2) := by
            ring
    _ = 2 *
            Real.sqrt ((((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) *
              (((k : ℝ) - 2) / k)) *
            Real.sqrt ((k : ℝ) * ((k : ℝ) - 1) / 2) := by
            rw [Real.sqrt_mul hfrac1_nonneg (((k : ℝ) - 2) / k)]
    _ = 2 *
            (Real.sqrt ((((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) *
              (((k : ℝ) - 2) / k)) *
              Real.sqrt ((k : ℝ) * ((k : ℝ) - 1) / 2)) := by
            ring
    _ = 2 * Real.sqrt
            (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1)) *
              ((k : ℝ) - 2) / (k : ℝ) *
              ((k : ℝ) * ((k : ℝ) - 1) / 2)) := by
            rw [← Real.sqrt_mul (mul_nonneg hfrac1_nonneg hfrac2_nonneg)
              ((k : ℝ) * ((k : ℝ) - 1) / 2)]
            ring_nf
    _ = 2 * Real.sqrt ((((k : ℝ) - 2) / 2) ^ 2) := by
            rw [hprod]
    _ = 2 * (((k : ℝ) - 2) / 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hhalf_nonneg]
    _ = (k : ℝ) - 2 := by
            ring
