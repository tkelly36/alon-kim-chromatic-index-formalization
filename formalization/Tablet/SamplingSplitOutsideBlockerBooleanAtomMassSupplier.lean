import Tablet.Preamble

open BigOperators
open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerBooleanAtomMassSupplier]
theorem SamplingSplitOutsideBlockerBooleanAtomMassSupplier :
    ∀ {α β Ω₀ Λ : Type u} [MeasurableSpace α] [MeasurableSpace β]
      [Fintype Λ] [DecidableEq Λ],
      ∀ (ν : MeasureTheory.Measure α) (ν' : MeasureTheory.Measure β)
        (baseCell : Ω₀ → Set α) (targetBaseCell : Ω₀ → Set β)
        (sourceLabel : Λ → Set α) (targetLabel : Λ → Set β),
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          MeasurableSet (baseCell ω₀ ∩
            {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          MeasurableSet (targetBaseCell ω₀ ∩
            {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀, ∀ η : α,
          η ∈ baseCell ω₀ ↔
            ∃ truth : Finset Λ,
              η ∈ baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) →
        (∀ ω₀ : Ω₀, ∀ η' : β,
          η' ∈ targetBaseCell ω₀ ↔
            ∃ truth : Finset Λ,
              η' ∈ targetBaseCell ω₀ ∩
                {η' | ∀ ℓ : Λ, (η' ∈ targetLabel ℓ ↔ ℓ ∈ truth)}) →
        (∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
          Disjoint
            (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₁)})
            (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₂)})) →
        (∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
          Disjoint
            (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth₁)})
            (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth₂)})) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ν (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) =
            ν' (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀,
          ν (baseCell ω₀) =
            ∑ truth : Finset Λ,
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀,
          ν' (targetBaseCell ω₀) =
            ∑ truth : Finset Λ,
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ν (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) =
            ν' (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) := by
-- BODY
  intro α β Ω₀ Λ _ _ _ _ ν ν' baseCell targetBaseCell sourceLabel targetLabel
    hsource_meas htarget_meas hsource_cover htarget_cover
    hsource_disjoint htarget_disjoint hatom_eq hweight
  refine ⟨?_, ?_, hatom_eq, hweight⟩
  · intro ω₀
    have hcover : baseCell ω₀ = ⋃ truth : Finset Λ,
        baseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)} := by
      ext η
      simpa only [Set.mem_iUnion] using hsource_cover ω₀ η
    calc
      ν (baseCell ω₀) = ν (⋃ truth : Finset Λ,
          baseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) :=
        congrArg ν hcover
      _ = _ := by
        simpa only [tsum_fintype] using
          measure_iUnion (μ := ν) (hsource_disjoint ω₀) (hsource_meas ω₀)
  · intro ω₀
    have hcover : targetBaseCell ω₀ = ⋃ truth : Finset Λ,
        targetBaseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)} := by
      ext η
      simpa only [Set.mem_iUnion] using htarget_cover ω₀ η
    calc
      ν' (targetBaseCell ω₀) = ν' (⋃ truth : Finset Λ,
          targetBaseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)}) :=
        congrArg ν' hcover
      _ = _ := by
        simpa only [tsum_fintype] using
          measure_iUnion (μ := ν') (htarget_disjoint ω₀) (htarget_meas ω₀)
