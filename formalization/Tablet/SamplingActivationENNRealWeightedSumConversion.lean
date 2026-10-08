import Tablet.Preamble
import Mathlib.MeasureTheory.Measure.MeasureSpace

open BigOperators

-- [TABLET NODE: SamplingActivationENNRealWeightedSumConversion]
theorem SamplingActivationENNRealWeightedSumConversion
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (Q : Finset V) (atom F : Finset V → ℝ)
    (hνatom : ∀ A : Finset V, ν {ω | ω.1 = A} = ENNReal.ofReal (atom A))
    (hatom_nonneg : ∀ A : Finset V, 0 ≤ atom A)
    (hF_nonneg : ∀ A : Finset V, Q ⊆ A → 0 ≤ F A) :
    (∑ A : Finset V,
      if Q ⊆ A then
        ν {ω | ω.1 = A} * ENNReal.ofReal (F A)
      else 0) =
      ENNReal.ofReal
        (∑ A : Finset V, if Q ⊆ A then atom A * F A else 0) := by
-- BODY
  classical
  calc
    (∑ A : Finset V,
      if Q ⊆ A then
        ν {ω | ω.1 = A} * ENNReal.ofReal (F A)
      else 0)
        = ∑ A : Finset V,
            if hQA : Q ⊆ A then
              ENNReal.ofReal (atom A) * ENNReal.ofReal (F A)
            else 0 := by
          apply Finset.sum_congr rfl
          intro A _hA
          by_cases hQA : Q ⊆ A
          · simp [hQA, hνatom A]
          · simp [hQA]
    _ = ∑ A : Finset V,
          ENNReal.ofReal (if Q ⊆ A then atom A * F A else 0) := by
          apply Finset.sum_congr rfl
          intro A _hA
          by_cases hQA : Q ⊆ A
          · simp [hQA, ENNReal.ofReal_mul (hatom_nonneg A)]
          · simp [hQA]
    _ = ENNReal.ofReal
        (∑ A : Finset V, if Q ⊆ A then atom A * F A else 0) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro A _hA
          by_cases hQA : Q ⊆ A
          · exact by
              simpa [hQA] using mul_nonneg (hatom_nonneg A) (hF_nonneg A hQA)
          · simp [hQA]
