import Tablet.SamplingFiniteProductCandidateReplacementStep
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open BigOperators MeasureTheory

-- [TABLET NODE: SamplingIntegratedCandidatePriorityReplacementStep]
theorem SamplingIntegratedCandidatePriorityReplacementStep
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : ℝ) (lam : @MeasureTheory.Measure (α → ℝ) ⊤)
    (η : (α → ℝ) → @MeasureTheory.Measure (Bool × ℝ) ⊤)
    (θ : (α → ℝ) → @MeasureTheory.Measure (α → Bool × ℝ) ⊤)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ_mem : ∀ᵐ π ∂lam, ∀ x : α, π x ∈ Set.Icc (0 : ℝ) 1)
    (hη_univ : ∀ π, η π Set.univ = 1)
    (hη_active_unit :
      ∀ π, η π {ω | ω.1 = true ∧ ω.2 ∈ Set.Icc (0 : ℝ) 1} =
        ENNReal.ofReal p)
    (hη_lower :
      ∀ π, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        η π {ω | ω.1 = true ∧ 0 ≤ ω.2 ∧ ω.2 ≤ t} =
          ENNReal.ofReal (p * t))
    (hθ_univ : ∀ π, θ π Set.univ = 1)
    (hθ_cylinder :
      ∀ π, ∀ A : Finset α, ∀ t : α → ℝ,
        (∀ x : α, x ∈ A → t x ∈ Set.Icc (0 : ℝ) 1) →
          θ π {ω |
            (∀ x : α, (ω x).1 = decide (x ∈ A)) ∧
              ∀ x : α, x ∈ A → 0 ≤ (ω x).2 ∧ (ω x).2 ≤ t x} =
            ENNReal.ofReal
              (p ^ A.card *
                (1 - p) ^ ((Finset.univ : Finset α).card - A.card) *
                  ∏ x ∈ A, t x)) :
    (∫⁻ π, η π {ω |
        ¬ (ω.1 = true ∧
          (∀ x : α, π x < ω.2) ∧
            ω.2 ∈ Set.Icc (0 : ℝ) 1)} ∂lam) ≤
      (∫⁻ π, θ π {ω |
        ∃ x : α,
          ¬ ((ω x).1 = true ∧
            π x < (ω x).2 ∧
              (ω x).2 ∈ Set.Icc (0 : ℝ) 1)} ∂lam) := by
-- BODY
  refine lintegral_mono_ae ?_
  filter_upwards [hπ_mem] with π hπ_mem_pi
  exact SamplingFiniteProductCandidateReplacementStep p π (η π) (θ π) hp0 hp1
    (fun x => (hπ_mem_pi x).1) (fun x => (hπ_mem_pi x).2)
    (hη_univ π) (hη_active_unit π) (hη_lower π)
    (hθ_univ π) (hθ_cylinder π)
