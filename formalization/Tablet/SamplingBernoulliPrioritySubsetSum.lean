import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingBernoulliPrioritySubsetSum]
theorem SamplingBernoulliPrioritySubsetSum
    {α : Type*} [DecidableEq α] (s : Finset α) (p x : ℝ) :
    (∑ A ∈ s.powerset,
        p ^ A.card * (1 - p) ^ (s.card - A.card) * x ^ A.card) =
      ((1 - p) + p * x) ^ s.card := by
-- BODY
  calc
    (∑ A ∈ s.powerset,
        p ^ A.card * (1 - p) ^ (s.card - A.card) * x ^ A.card)
        = ∑ A ∈ s.powerset,
            (p * x) ^ A.card * (1 - p) ^ (s.card - A.card) := by
          refine Finset.sum_congr rfl ?_
          intro A hA
          rw [mul_pow]
          ring
    _ = ((p * x) + (1 - p)) ^ s.card := by
          simpa using
            (Finset.sum_pow_mul_eq_add_pow (s := s) (a := p * x) (b := 1 - p))
    _ = ((1 - p) + p * x) ^ s.card := by
          ring
