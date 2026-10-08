import Tablet.SamplingSplitOutsideBlockerHybridRefinedAtomMassLaw
import Tablet.SamplingSplitOutsideBlockerStageCellCommonRefinement

open BigOperators MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMeasuredStageCellRefinement]
theorem SamplingSplitOutsideBlockerMeasuredStageCellRefinement :
    ∀ {V V' Ω₀ Λ : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω₀] [DecidableEq Ω₀]
      [Fintype Λ] [DecidableEq Λ],
      ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
        (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
        (baseCell : Ω₀ → Set (Finset V × (V → ℝ)))
        (targetBaseCell : Ω₀ → Set (Finset V' × (V' → ℝ)))
        (sourceLabel : Λ → Set (Finset V × (V → ℝ)))
        (targetLabel : Λ → Set (Finset V' × (V' → ℝ)))
        (transport : Ω₀ → (Finset V × (V → ℝ)) →
          (Finset V' × (V' → ℝ)) → Prop),
        (∀ ω₀ : Ω₀,
          @MeasurableSet (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
            (baseCell ω₀)) →
        (∀ ω₀ : Ω₀,
          @MeasurableSet (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
            (targetBaseCell ω₀)) →
        (∀ ℓ : Λ,
          @MeasurableSet (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
            (sourceLabel ℓ)) →
        (∀ ℓ : Λ,
          @MeasurableSet (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
            (targetLabel ℓ)) →
        (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ → Disjoint (baseCell ω₁) (baseCell ω₂)) →
        (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ →
          Disjoint (targetBaseCell ω₁) (targetBaseCell ω₂)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            (η ∈ baseCell ω₀ ↔ η' ∈ targetBaseCell ω₀)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ η' ∈ targetLabel ℓ)) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        ∃ (Ω : Type u) (_ : Fintype Ω) (baseOf : Ω → Ω₀)
          (truth : Ω → Finset Λ)
          (cell : Ω → Set (Finset V × (V → ℝ)))
          (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
          (w : Ω → ℝ),
          (∀ ω : Ω,
            cell ω =
              baseCell (baseOf ω) ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth ω)}) ∧
          (∀ ω : Ω,
            targetCell ω =
              targetBaseCell (baseOf ω) ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth ω)}) ∧
          (∀ ω₀ : Ω₀, ∀ η : Finset V × (V → ℝ),
            η ∈ baseCell ω₀ → ∃ ω : Ω, baseOf ω = ω₀ ∧ η ∈ cell ω) ∧
          (∀ ω₀ : Ω₀, ∀ η' : Finset V' × (V' → ℝ),
            η' ∈ targetBaseCell ω₀ →
              ∃ ω : Ω, baseOf ω = ω₀ ∧ η' ∈ targetCell ω) ∧
          (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) ∧
          (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
            Disjoint (targetCell ω₁) (targetCell ω₂)) ∧
          (∀ ω : Ω, ∀ ℓ : Λ, ∀ η : Finset V × (V → ℝ),
            η ∈ cell ω → (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth ω)) ∧
          (∀ ω : Ω, ∀ ℓ : Λ, ∀ η' : Finset V' × (V' → ℝ),
            η' ∈ targetCell ω → (η' ∈ targetLabel ℓ ↔ ℓ ∈ truth ω)) ∧
          (∀ ω : Ω, ∀ η η',
            transport (baseOf ω) η η' →
              (η ∈ cell ω ↔ η' ∈ targetCell ω)) ∧
          (∀ ω : Ω, 0 ≤ w ω) ∧
          (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) ∧
          (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) ∧
          (∀ ω₀ : Ω₀,
            ν (baseCell ω₀) =
              ∑ ω : Ω, if baseOf ω = ω₀ then ν (cell ω) else 0) ∧
          (∀ ω₀ : Ω₀,
            ν' (targetBaseCell ω₀) =
              ∑ ω : Ω, if baseOf ω = ω₀ then ν' (targetCell ω) else 0) := by
-- BODY
  classical
  intro V V' Ω₀ Λ _ _ _ _ _ _ _ _ ν ν' baseCell targetBaseCell sourceLabel
    targetLabel transport hbaseMeas htargetBaseMeas hsourceLabelMeas htargetLabelMeas
    hbaseDisjoint htargetDisjoint hbaseTransport hlabelTransport hatomMass
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  letI : MeasurableSpace (Finset V' × (V' → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  have hrefined :=
    SamplingSplitOutsideBlockerHybridRefinedAtomMassLaw
      (ν := ν) (ν' := ν') (baseCell := baseCell) (targetBaseCell := targetBaseCell)
      (sourceLabel := sourceLabel) (targetLabel := targetLabel) (transport := transport)
      hbaseMeas htargetBaseMeas hsourceLabelMeas htargetLabelMeas
      hbaseTransport hlabelTransport hatomMass
  exact
    SamplingSplitOutsideBlockerStageCellCommonRefinement
      (ν := ν) (ν' := ν') (baseCell := baseCell) (targetBaseCell := targetBaseCell)
      (sourceLabel := sourceLabel) (targetLabel := targetLabel) (transport := transport)
      hbaseDisjoint htargetDisjoint hbaseTransport hlabelTransport
      hrefined.2.2.2.2.2.2.2.2.2.1
      hrefined.2.2.2.2.2.2.2.2.2.2
      hrefined.2.2.2.2.2.2.2.1
      hrefined.2.2.2.2.2.2.2.2.1
