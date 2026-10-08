import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: TablePairBound]
theorem TablePairBound :
    ∀ {k n : ℕ} (hk : 2 ≤ k) (C T : ℝ) (A : Fin k → Fin n → ℝ),
      0 < C →
      0 < T →
      (∀ i j, 0 ≤ A i j) →
      (∀ j, (∑ i : Fin k, A i j) ≤ C) →
      (∑ i : Fin k, ∑ j : Fin n, A i j) ≤ T →
      (∑ j : Fin n,
          ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0))
        ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * T * C := by
-- BODY
  intro k n hk C T A hC hT hnonneg hcol htot
  let B : Fin n → ℝ := fun j => ∑ i : Fin k, A i j
  let P : Fin n → ℝ := fun j =>
    ∑ i : Fin k, ∑ i' : Fin k, (if i < i' then A i j * A i' j else 0)
  have hkpos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hcoef_nonneg : 0 ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) := by
    have h1k : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hk)
    exact div_nonneg (sub_nonneg.mpr h1k) (mul_nonneg (by norm_num) hkpos.le)
  have hcolP : ∀ j : Fin n, P j ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * B j := by
    intro j
    have hB_nonneg : 0 ≤ B j := by
      dsimp [B]
      exact Finset.sum_nonneg (fun i _ => hnonneg i j)
    have hB_le_C : B j ≤ C := by
      dsimp [B]
      exact hcol j
    have hBsq_le_CB : B j ^ 2 ≤ C * B j := by
      calc
        B j ^ 2 = B j * B j := by ring
        _ ≤ C * B j := by exact mul_le_mul_of_nonneg_right hB_le_C hB_nonneg
    have hpair_le : P j ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * (B j)^2 := by
      let Q : ℝ := ∑ i : Fin k, (A i j)^2
      have hdiag :
          (∑ i : Fin k, ∑ i' : Fin k,
              (if i = i' then A i j * A i' j else 0)) = Q := by
        dsimp [Q]
        simp [pow_two]
      have hdiag' : (∑ i : Fin k, A i j * A i j) = Q := by
        simpa using hdiag
      have hswap :
          (∑ i : Fin k, ∑ i' : Fin k,
              (if i' < i then A i j * A i' j else 0)) = P j := by
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
          (if i < i' then A i j * A i' j else 0) +
            (if i' < i then A i j * A i' j else 0) +
            (if i = i' then A i j * A i' j else 0)
            = A i j * A i' j := by
        intro i i'
        rcases lt_trichotomy i i' with hlt | heq | hgt
        · simp [hlt, ne_of_lt hlt, not_lt_of_gt hlt]
        · subst i'
          simp
        · simp [hgt, ne_of_gt hgt, not_lt_of_gt hgt]
      have hid :
          2 * P j + Q = (B j)^2 := by
        have hsum :
            (∑ i : Fin k, ∑ i' : Fin k,
              ((if i < i' then A i j * A i' j else 0) +
                (if i' < i then A i j * A i' j else 0) +
                (if i = i' then A i j * A i' j else 0)))
              =
            (∑ i : Fin k, ∑ i' : Fin k, A i j * A i' j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro i' _
          exact hpoint i i'
        calc
          2 * P j + Q
              = (∑ i : Fin k, ∑ i' : Fin k,
                  ((if i < i' then A i j * A i' j else 0) +
                    (if i' < i then A i j * A i' j else 0) +
                    (if i = i' then A i j * A i' j else 0))) := by
                symm
                simp [P, Finset.sum_add_distrib, hswap, hdiag', two_mul, add_assoc]
          _ = (∑ i : Fin k, ∑ i' : Fin k, A i j * A i' j) := hsum
          _ = (B j)^2 := by
                dsimp [B]
                rw [pow_two, Finset.sum_mul]
                simp_rw [Finset.mul_sum]
      have hcauchy : (B j)^2 ≤ Q * (k : ℝ) := by
        dsimp [B, Q]
        simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_comm, mul_left_comm,
          mul_assoc] using
          (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
            (fun i => A i j) (fun _ => (1 : ℝ)))
      have htarget : (2 * (k : ℝ)) * P j ≤ ((k : ℝ) - 1) * (B j)^2 := by
        nlinarith [hid, hcauchy, hkpos]
      have hden_pos : 0 < 2 * (k : ℝ) := mul_pos (by norm_num) hkpos
      calc
        P j = ((2 * (k : ℝ)) * P j) / (2 * (k : ℝ)) := by
          field_simp [ne_of_gt hden_pos]
        _ ≤ (((k : ℝ) - 1) * (B j)^2) / (2 * (k : ℝ)) :=
          div_le_div_of_nonneg_right htarget hden_pos.le
        _ = ((↑k - 1) / (2 * ↑k)) * B j ^ 2 := by ring
    have hmul := mul_le_mul_of_nonneg_left hBsq_le_CB hcoef_nonneg
    nlinarith [hpair_le, hmul]
  have hsumP : (∑ j : Fin n, P j) ≤
      ∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * B j := by
    exact Finset.sum_le_sum (fun j _ => hcolP j)
  have hsumB_le : (∑ j : Fin n, B j) ≤ T := by
    dsimp [B]
    rw [Finset.sum_comm]
    exact htot
  have hmain : (∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * B j)
      ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * T * C := by
    calc
      (∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * B j)
          = (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * (∑ j : Fin n, B j) := by
            rw [← Finset.mul_sum]
      _ ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * C * T := by
            gcongr
      _ = (((k : ℝ) - 1) / (2 * (k : ℝ))) * T * C := by ring
  exact le_trans hsumP hmain
