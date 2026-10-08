import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingFiniteBonferroniUnionBound]
theorem SamplingFiniteBonferroniUnionBound {V : Type*} [Fintype V] [DecidableEq V]
    (μ : Finset V → ℝ) (hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S) (X : Finset V) :
    (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
      (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) -
        (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) +
          (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) := by
-- BODY
  classical
  have hbonf_nat :
      ∀ n : ℕ,
        (if n = 0 then (0 : ℝ) else 1) ≤
          (n : ℝ) - (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      have hid :
          (n : ℝ) - (Nat.choose n 2 : ℝ) + (Nat.choose n 3 : ℝ) =
            1 + (Nat.choose (n - 1) 3 : ℝ) := by
        cases n with
        | zero => contradiction
        | succ m =>
            have h2 : Nat.choose (m + 1) 2 = m + Nat.choose m 2 := by
              rw [show (2 : ℕ) = 1 + 1 by norm_num, Nat.choose_succ_succ]
              simp
            have h3 : Nat.choose (m + 1) 3 = Nat.choose m 2 + Nat.choose m 3 := by
              rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.choose_succ_succ]
            simp only [Nat.add_sub_cancel_right]
            rw [h2, h3]
            norm_num
            ring
      rw [hid]
      have hnonneg : (0 : ℝ) ≤ (Nat.choose (n - 1) 3 : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
  have hpoint :
      ∀ S : Finset V,
        (if (S ∩ X).Nonempty then μ S else 0) ≤
          μ S * ((S ∩ X).card : ℝ) -
            μ S * (Nat.choose (S ∩ X).card 2 : ℝ) +
              μ S * (Nat.choose (S ∩ X).card 3 : ℝ) := by
    intro S
    by_cases hnonempty : (S ∩ X).Nonempty
    · have hcard_ne : (S ∩ X).card ≠ 0 := Finset.card_ne_zero.mpr hnonempty
      have hineq := hbonf_nat (S ∩ X).card
      rw [if_neg hcard_ne] at hineq
      have hmul := mul_le_mul_of_nonneg_left hineq (hμ_nonneg S)
      simpa [hnonempty, mul_sub, mul_add] using hmul
    · have hcard_zero : (S ∩ X).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
      simp [hnonempty, hcard_zero, hμ_nonneg S]
  calc
    (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0)
        ≤ ∑ S : Finset V,
            (μ S * ((S ∩ X).card : ℝ) -
              μ S * (Nat.choose (S ∩ X).card 2 : ℝ) +
                μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) := by
          exact Finset.sum_le_sum (fun S _hS => hpoint S)
    _ = (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) -
        (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) +
          (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
