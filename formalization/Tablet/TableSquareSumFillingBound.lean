import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: TableSquareSumFillingBound]
theorem TableSquareSumFillingBound :
    ∀ {n : ℕ} (C T : ℝ) (q : ℕ) (r : ℝ) (s : Fin n → ℝ),
      0 < C →
      T = (q : ℝ) * C + r →
      0 ≤ r →
      r ≤ C →
      (∀ j, 0 ≤ s j) →
      (∀ j, s j ≤ C) →
      (∑ j : Fin n, s j) ≤ T →
      (∑ j : Fin n, (s j) ^ (2 : ℕ)) ≤ (q : ℝ) * C ^ (2 : ℕ) + r ^ (2 : ℕ) := by
-- BODY
  intro n
  induction n with
  | zero =>
      intro C T q r s hC hTsplit hr_nonneg hr_le_C hs_nonneg hs_le_C hsum
      simp
      exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) (sq_nonneg r)
  | succ n ih =>
      intro C T q r s hC hTsplit hr_nonneg hr_le_C hs_nonneg hs_le_C hsum
      let x : ℝ := s (Fin.last n)
      let t : Fin n → ℝ := fun j => s (Fin.castSucc j)
      have hx_nonneg : 0 ≤ x := hs_nonneg (Fin.last n)
      have hx_le_C : x ≤ C := hs_le_C (Fin.last n)
      have ht_nonneg : ∀ j, 0 ≤ t j := fun j => hs_nonneg (Fin.castSucc j)
      have ht_le_C : ∀ j, t j ≤ C := fun j => hs_le_C (Fin.castSucc j)
      have hsum_split : (∑ j : Fin (n + 1), s j) = (∑ j : Fin n, t j) + x := by
        dsimp [t, x]
        exact Fin.sum_univ_castSucc s
      have hsq_split :
          (∑ j : Fin (n + 1), (s j) ^ (2 : ℕ)) =
            (∑ j : Fin n, (t j) ^ (2 : ℕ)) + x ^ (2 : ℕ) := by
        dsimp [t, x]
        exact Fin.sum_univ_castSucc (fun j => (s j) ^ (2 : ℕ))
      have hsum_t_le : (∑ j : Fin n, t j) ≤ T - x := by
        nlinarith [hsum, hsum_split]
      by_cases hxr : x ≤ r
      · have hrx_nonneg : 0 ≤ r - x := sub_nonneg.mpr hxr
        have hrx_le_C : r - x ≤ C := by nlinarith
        have hTsplit' : T - x = (q : ℝ) * C + (r - x) := by
          nlinarith [hTsplit]
        have hih := ih C (T - x) q (r - x) t hC hTsplit' hrx_nonneg hrx_le_C
          ht_nonneg ht_le_C hsum_t_le
        rw [hsq_split]
        nlinarith [hih, hx_nonneg, hxr]
      · have hr_lt_x : r < x := lt_of_not_ge hxr
        have hq_pos : 0 < q := by
          by_contra hq0
          have hq_eq_zero : q = 0 := Nat.eq_zero_of_not_pos hq0
          have hx_le_T : x ≤ T := by
            have ht_sum_nonneg : 0 ≤ ∑ j : Fin n, t j := by
              exact Finset.sum_nonneg (fun j _ => ht_nonneg j)
            nlinarith [hsum, hsum_split]
          have hT_eq_r : T = r := by
            rw [hq_eq_zero] at hTsplit
            norm_num at hTsplit
            exact hTsplit
          nlinarith [hT_eq_r, hx_le_T, hr_lt_x]
        let q' : ℕ := q - 1
        let r' : ℝ := C + r - x
        have hr'_nonneg : 0 ≤ r' := by
          dsimp [r']
          nlinarith [hx_le_C, hr_nonneg]
        have hr'_le_C : r' ≤ C := by
          dsimp [r']
          nlinarith [hr_lt_x]
        have hq_cast : (q : ℝ) = (q' : ℝ) + 1 := by
          dsimp [q']
          have hsucc : (q - 1) + 1 = q := Nat.succ_pred_eq_of_pos hq_pos
          have hcast := congrArg (fun m : ℕ => (m : ℝ)) hsucc
          norm_num at hcast ⊢
          linarith
        have hTsplit' : T - x = (q' : ℝ) * C + r' := by
          dsimp [r']
          nlinarith [hTsplit, hq_cast]
        have hih := ih C (T - x) q' r' t hC hTsplit' hr'_nonneg hr'_le_C
          ht_nonneg ht_le_C hsum_t_le
        rw [hsq_split]
        dsimp [r'] at hih ⊢
        nlinarith [hih, hx_le_C, hr_lt_x.le]
