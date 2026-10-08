import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.Preamble

-- [TABLET NODE: SamplingFiniteProductPointwiseLower]
theorem SamplingFiniteProductPointwiseLower
    (Delta N : ℕ) (alpha L t : ℝ)
    (hD : 0 < (Delta : ℝ))
    (halpha_pos : 0 < 1 - alpha)
    (ht_nonneg : 0 ≤ t)
    (ht_le_L : t ≤ L)
    (hL_lt : L < (Delta : ℝ))
    (hN_le : (N : ℝ) ≤ (Delta : ℝ))
    (hlarge : L^2 / ((Delta : ℝ) - L) ≤ - Real.log (1 - alpha)) :
    (1 - t / (Delta : ℝ)) ^ N ≥
      (1 - alpha) * Real.exp (-(((N : ℝ) / (Delta : ℝ)) * t)) := by
-- BODY
  let d : ℝ := (Delta : ℝ)
  have hd_pos : 0 < d := hD
  have hL_nonneg : 0 ≤ L := le_trans ht_nonneg ht_le_L
  have ht_lt_d : t < d := lt_of_le_of_lt ht_le_L hL_lt
  have hden_pos : 0 < d - L := sub_pos.2 hL_lt
  have hdt_pos : 0 < d - t := sub_pos.2 ht_lt_d
  have ht_sq_le_L_sq : t ^ 2 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - t)]
  have hfrac_tL : t ^ 2 / (d - t) ≤ L ^ 2 / (d - L) := by
    have hinv : (d - t)⁻¹ ≤ (d - L)⁻¹ := by
      exact inv_anti₀ hden_pos (by linarith)
    calc
      t ^ 2 / (d - t) = t ^ 2 * (d - t)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ L ^ 2 * (d - t)⁻¹ := by
        exact mul_le_mul_of_nonneg_right ht_sq_le_L_sq (inv_nonneg.mpr hdt_pos.le)
      _ ≤ L ^ 2 * (d - L)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (sq_nonneg L)
      _ = L ^ 2 / (d - L) := by rw [div_eq_mul_inv]
  have hu_error :
      (N : ℝ) * (t / d)^2 / (1 - t / d) ≤ - Real.log (1 - alpha) := by
    have hbase :
        (N : ℝ) * (t / d)^2 / (1 - t / d) ≤ t ^ 2 / (d - t) := by
      have hone_sub_pos : 0 < 1 - t / d := sub_pos.2 ((div_lt_one hd_pos).2 ht_lt_d)
      have hN_div : (N : ℝ) / d ≤ 1 := (div_le_one hd_pos).2 hN_le
      have hnonneg_t2_div : 0 ≤ t ^ 2 / d := div_nonneg (sq_nonneg t) hd_pos.le
      calc
        (N : ℝ) * (t / d)^2 / (1 - t / d)
            = ((N : ℝ) / d) * (t ^ 2 / d) / (1 - t / d) := by
              field_simp [ne_of_gt hd_pos]
        _ ≤ 1 * (t ^ 2 / d) / (1 - t / d) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hN_div hnonneg_t2_div) hone_sub_pos.le
        _ = t ^ 2 / (d - t) := by
              field_simp [ne_of_gt hd_pos, ne_of_gt hdt_pos]
    exact hbase.trans (hfrac_tL.trans (by simpa [d] using hlarge))
  let u : ℝ := t / d
  have hu_nonneg : 0 ≤ u := div_nonneg ht_nonneg hd_pos.le
  have hu_lt_one : u < 1 := (div_lt_one hd_pos).2 ht_lt_d
  have hbase_pos : 0 < 1 - u := sub_pos.2 hu_lt_one
  have hbase_pos' : 0 < 1 - t / d := by
    simpa [u] using hbase_pos
  apply Real.le_pow_of_log_le hbase_pos'
  have hlog_lower : -(u / (1 - u)) ≤ Real.log (1 - u) := by
    have h := Real.one_sub_inv_le_log_of_pos hbase_pos
    have heq : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by
      field_simp [ne_of_gt hbase_pos]
      ring
    simpa [heq] using h
  have hmul_lower : -((N : ℝ) * (u / (1 - u))) ≤ (N : ℝ) * Real.log (1 - u) := by
    have h := mul_le_mul_of_nonneg_left hlog_lower (Nat.cast_nonneg N : 0 ≤ (N : ℝ))
    simpa [mul_neg, mul_div_assoc] using h
  have herr_u : (N : ℝ) * u^2 / (1 - u) ≤ - Real.log (1 - alpha) := by
    simpa [u, d] using hu_error
  have htarget_le :
      Real.log ((1 - alpha) * Real.exp (-(((N : ℝ) / d) * t))) ≤
        -((N : ℝ) * (u / (1 - u))) := by
    rw [Real.log_mul (ne_of_gt halpha_pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    have hrewrite : ((N : ℝ) / d) * t = (N : ℝ) * u := by
      simp [u, div_eq_mul_inv, mul_assoc, mul_comm]
    rw [hrewrite]
    have hident :
        -((N : ℝ) * (u / (1 - u))) =
          -((N : ℝ) * u) - ((N : ℝ) * u^2 / (1 - u)) := by
      field_simp [ne_of_gt hbase_pos]
      ring
    rw [hident]
    linarith
  have hfinal := htarget_le.trans hmul_lower
  simpa [u, d] using hfinal
