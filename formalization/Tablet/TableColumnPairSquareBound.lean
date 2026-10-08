import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Tablet.Preamble

open scoped BigOperators

set_option linter.unusedVariables false

-- [TABLET NODE: TableColumnPairSquareBound]
theorem TableColumnPairSquareBound :
    ∀ {k : ℕ} (hk : 2 ≤ k) (x : Fin k → ℝ),
      (∑ i : Fin k, ∑ i' : Fin k, (if i < i' then x i * x i' else 0))
        ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) *
          (∑ i : Fin k, x i) ^ (2 : ℕ) := by
-- BODY
  intro k hk x
  let B : ℝ := ∑ i : Fin k, x i
  let P : ℝ := ∑ i : Fin k, ∑ i' : Fin k, (if i < i' then x i * x i' else 0)
  let Q : ℝ := ∑ i : Fin k, (x i)^2
  have hkpos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hdiag :
      (∑ i : Fin k, ∑ i' : Fin k,
          (if i = i' then x i * x i' else 0)) = Q := by
    dsimp [Q]
    simp [pow_two]
  have hdiag' : (∑ i : Fin k, x i * x i) = Q := by
    simpa using hdiag
  have hswap :
      (∑ i : Fin k, ∑ i' : Fin k,
          (if i' < i then x i * x i' else 0)) = P := by
    dsimp [P]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro i' _
    by_cases h : i < i'
    · simp [h, mul_comm]
    · simp [h]
  have hpoint : ∀ i i' : Fin k,
      (if i < i' then x i * x i' else 0) +
        (if i' < i then x i * x i' else 0) +
        (if i = i' then x i * x i' else 0)
        = x i * x i' := by
    intro i i'
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_gt hlt]
    · subst i'
      simp
    · simp [hgt, ne_of_gt hgt, not_lt_of_gt hgt]
  have hid : 2 * P + Q = B^2 := by
    have hsum :
        (∑ i : Fin k, ∑ i' : Fin k,
          ((if i < i' then x i * x i' else 0) +
            (if i' < i then x i * x i' else 0) +
            (if i = i' then x i * x i' else 0)))
          =
        (∑ i : Fin k, ∑ i' : Fin k, x i * x i') := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro i' _
      exact hpoint i i'
    calc
      2 * P + Q
          = (∑ i : Fin k, ∑ i' : Fin k,
              ((if i < i' then x i * x i' else 0) +
                (if i' < i then x i * x i' else 0) +
                (if i = i' then x i * x i' else 0))) := by
            symm
            simp [P, Finset.sum_add_distrib, hswap, hdiag', two_mul, add_assoc]
      _ = (∑ i : Fin k, ∑ i' : Fin k, x i * x i') := hsum
      _ = B^2 := by
            dsimp [B]
            rw [pow_two, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
  have hcauchy : B^2 ≤ Q * (k : ℝ) := by
    dsimp [B, Q]
    simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
        (fun i => x i) (fun _ => (1 : ℝ)))
  have htarget : (2 * (k : ℝ)) * P ≤ ((k : ℝ) - 1) * B^2 := by
    nlinarith [hid, hcauchy, hkpos]
  have hden_pos : 0 < 2 * (k : ℝ) := mul_pos (by norm_num) hkpos
  calc
    P = ((2 * (k : ℝ)) * P) / (2 * (k : ℝ)) := by
      field_simp [ne_of_gt hden_pos]
    _ ≤ (((k : ℝ) - 1) * B^2) / (2 * (k : ℝ)) :=
      div_le_div_of_nonneg_right htarget hden_pos.le
    _ = ((↑k - 1) / (2 * ↑k)) * B ^ 2 := by ring
