import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingFiniteConditionalReplacementIteration]
theorem SamplingFiniteConditionalReplacementIteration {Ω : Type*} [Fintype Ω]
    (n : ℕ) (w : Ω → ℝ) (P : ℕ → Ω → ℝ)
    (hw_nonneg : ∀ ω : Ω, 0 ≤ w ω)
    (hstep : ∀ k : ℕ, k < n → ∀ ω : Ω, P k ω ≤ P (k + 1) ω) :
    (∑ ω : Ω, w ω * P 0 ω) ≤ (∑ ω : Ω, w ω * P n ω) := by
-- BODY
  classical
  have hmono : ∀ m : ℕ, m ≤ n →
      (∑ ω : Ω, w ω * P 0 ω) ≤ (∑ ω : Ω, w ω * P m ω) := by
    intro m hm
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hm_le_n : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
        have hprev :
            (∑ ω : Ω, w ω * P 0 ω) ≤ (∑ ω : Ω, w ω * P m ω) :=
          ih hm_le_n
        have hm_lt_n : m < n := Nat.lt_of_succ_le hm
        have hnext :
            (∑ ω : Ω, w ω * P m ω) ≤ (∑ ω : Ω, w ω * P (m + 1) ω) := by
          refine Finset.sum_le_sum ?_
          intro ω _hω
          exact mul_le_mul_of_nonneg_left (hstep m hm_lt_n ω) (hw_nonneg ω)
        exact hprev.trans hnext
  exact hmono n (Nat.le_refl n)
