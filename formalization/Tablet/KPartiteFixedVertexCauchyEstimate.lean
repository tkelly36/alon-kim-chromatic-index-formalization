import Tablet.Preamble
import Mathlib.Algebra.Order.Chebyshev

-- [TABLET NODE: KPartiteFixedVertexCauchyEstimate]
theorem KPartiteFixedVertexCauchyEstimate :
    ∀ k : ℕ, ∀ i : Fin k, ∀ w : Fin k → Fin k → ℝ,
      (∀ a b, 0 ≤ w a b) →
      let s : Finset (Fin k × Fin k) :=
        (Finset.univ.filter
          (fun p : Fin k × Fin k => p.1 < p.2 ∧ p.1 ≠ i ∧ p.2 ≠ i))
      s.sum (fun p =>
          Real.sqrt (w i p.1 * w i p.2 * w p.1 p.2)) ≤
        Real.sqrt (s.sum (fun p => w i p.1 * w i p.2)) *
          Real.sqrt (s.sum (fun p => w p.1 p.2)) := by
-- BODY
  intro k i w hw s
  have hf : ∀ p : Fin k × Fin k, 0 ≤ w i p.1 * w i p.2 := by
    intro p
    exact mul_nonneg (hw i p.1) (hw i p.2)
  have hg : ∀ p : Fin k × Fin k, 0 ≤ w p.1 p.2 := by
    intro p
    exact hw p.1 p.2
  have hcs :
      (∑ p ∈ s,
          Real.sqrt (w i p.1 * w i p.2) * Real.sqrt (w p.1 p.2)) ≤
        Real.sqrt (∑ p ∈ s, w i p.1 * w i p.2) *
          Real.sqrt (∑ p ∈ s, w p.1 p.2) := by
    simpa using
      (Real.sum_sqrt_mul_sqrt_le s
        (f := fun p : Fin k × Fin k => w i p.1 * w i p.2)
        (g := fun p : Fin k × Fin k => w p.1 p.2) hf hg)
  have hrewrite :
      s.sum (fun p =>
          Real.sqrt (w i p.1 * w i p.2 * w p.1 p.2)) =
        ∑ p ∈ s,
          Real.sqrt (w i p.1 * w i p.2) * Real.sqrt (w p.1 p.2) := by
    refine Finset.sum_congr rfl ?_
    intro p _hp
    rw [Real.sqrt_mul (hf p) (w p.1 p.2)]
  rw [hrewrite]
  exact hcs
