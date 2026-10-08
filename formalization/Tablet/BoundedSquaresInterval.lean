import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: BoundedSquaresInterval]
theorem BoundedSquaresInterval :
    ∀ {n : ℕ} (a b : ℝ) (r : Fin n → ℝ),
      a ≤ b →
      (∀ i, a ≤ r i ∧ r i ≤ b) →
      (∑ i : Fin n, (r i) ^ (2 : ℕ)) ≤
        (a + b) * (∑ i : Fin n, r i) - (n : ℝ) * a * b := by
-- BODY
  intro n a b r hab hr
  have hpoint :
      ∀ i : Fin n, (r i) ^ (2 : ℕ) ≤ (a + b) * r i - a * b := by
    intro i
    have hnonneg : 0 ≤ (r i - a) * (b - r i) := by
      exact mul_nonneg (sub_nonneg.mpr (hr i).1) (sub_nonneg.mpr (hr i).2)
    nlinarith [hnonneg]
  calc
    (∑ i : Fin n, (r i) ^ (2 : ℕ))
        ≤ ∑ i : Fin n, ((a + b) * r i - a * b) :=
          Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (a + b) * (∑ i : Fin n, r i) - (n : ℝ) * a * b := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
