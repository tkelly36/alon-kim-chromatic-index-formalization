import Tablet.SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
import Tablet.SamplingFiniteBooleanAtomPartition
import Tablet.SamplingSplitOutsideBlockerOutsideBkResidualLabelStructure

open BigOperators MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerOutsideBkResidualLabelPartition]
theorem SamplingSplitOutsideBlockerOutsideBkResidualLabelPartition :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (φ : V → V') (r : V) (X : Finset V)
          [LinearOrder {x : V // x ∈ X}]
          (β :
            (Σ x : {x : V // x ∈ X},
              {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
          (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
          (k : ℕ) (hk : k < n) (ω : Ω)
          (cell : Ω → Set (Finset V × (V → ℝ)))
          (targetCell : Ω → Set (Finset V' × (V' → ℝ))),
          Function.Injective zAt →
          Function.Injective φ →
          Function.Injective β →
          (hOutside : ∀ i : Fin n, zAt i ∉ insert r X) →
          (∀ x : V, ∀ hx : x ∈ X,
            ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
            ∀ y : V, y ∈ insert r X →
              β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ≠ φ y) →
          (∀ i : Fin n, ∀ x : V,
            x ∈ B i ↔ x ∈ X ∧ G.Adj x (zAt i)) →
          (∀ η : Finset V × (V → ℝ), η ∈ cell ω →
            ∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
          (∀ η' : Finset V' × (V' → ℝ), η' ∈ targetCell ω →
            ∀ v' : V', 0 ≤ η'.2 v' ∧ η'.2 v' ≤ 1) →
          (label : Type u) → [Fintype label] → [DecidableEq label] →
          (sourceLabelEvent : label → Set (Finset V × (V → ℝ))) →
          (targetLabelEvent : label → Set (Finset V' × (V' → ℝ))) →
          (selectedWitnessLabels : Finset label) →
          (earlierFirstWitnessLabels : Finset label) →
          (cellPredicateLabels : Finset label) →
          (retainedCommonSourceTestLabels : Finset label) →
          (alreadyPrivateTargetTestLabels : Finset label) →
          (globalBoundaryComplementLabels : Finset label) →
          ∀ x : {x : V // x ∈ X}, x.1 ∉ B ⟨k, hk⟩ →
            let pieces :=
              SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
                G φ r X β n zAt B k hk
            let sourceAtom : Finset label → Set (Finset V × (V → ℝ)) :=
              fun truth =>
                {η | ∀ ℓ : label, (η ∈ sourceLabelEvent ℓ ↔ ℓ ∈ truth)}
            let targetAtom : Finset label → Set (Finset V' × (V' → ℝ)) :=
              fun truth =>
                {η' | ∀ ℓ : label, (η' ∈ targetLabelEvent ℓ ↔ ℓ ∈ truth)}
            pieces.1 x ∩ cell ω = ⋃ a : Finset label, sourceAtom a →
            pieces.2 x ∩ targetCell ω = ⋃ a : Finset label, targetAtom a →
            SamplingSplitOutsideBlockerOutsideBkResidualLabelStructure
              G φ r X β n zAt B k hk ω cell targetCell hOutside x
              sourceAtom targetAtom sourceLabelEvent targetLabelEvent
              (fun truth ℓ => decide (ℓ ∈ truth)) selectedWitnessLabels
              earlierFirstWitnessLabels cellPredicateLabels
              retainedCommonSourceTestLabels alreadyPrivateTargetTestLabels
              globalBoundaryComplementLabels →
            (∀ ℓ : label,
              @NullMeasurableSet
                (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (sourceLabelEvent ℓ) ν) →
            (∀ ℓ : label,
              @NullMeasurableSet
                (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (targetLabelEvent ℓ) ν') →
            ∃ ι : Type u, ∃ instι : Fintype ι,
              ∃ sourceAtom : ι → Set (Finset V × (V → ℝ)),
              ∃ targetAtom : ι → Set (Finset V' × (V' → ℝ)),
              ∃ label : Type u, ∃ instLabel : Fintype label,
              ∃ sourceLabelEvent : label → Set (Finset V × (V → ℝ)),
              ∃ targetLabelEvent : label → Set (Finset V' × (V' → ℝ)),
              ∃ labelTruth : ι → label → Bool,
              ∃ selectedWitnessLabels : Finset label,
              ∃ earlierFirstWitnessLabels : Finset label,
              ∃ cellPredicateLabels : Finset label,
              ∃ retainedCommonSourceTestLabels : Finset label,
              ∃ alreadyPrivateTargetTestLabels : Finset label,
              ∃ globalBoundaryComplementLabels : Finset label,
              ∃ residualLabelStructure :
                SamplingSplitOutsideBlockerOutsideBkResidualLabelStructure
                  G φ r X β n zAt B k hk ω cell targetCell hOutside x
                  sourceAtom targetAtom sourceLabelEvent targetLabelEvent
                  labelTruth selectedWitnessLabels earlierFirstWitnessLabels
                  cellPredicateLabels retainedCommonSourceTestLabels
                  alreadyPrivateTargetTestLabels globalBoundaryComplementLabels,
                pieces.1 x ∩ cell ω = ⋃ a : ι, sourceAtom a ∧
                pieces.2 x ∩ targetCell ω = ⋃ a : ι, targetAtom a ∧
                Set.Pairwise (Set.univ : Set ι)
                  (Function.onFun (AEDisjoint ν) sourceAtom) ∧
                Set.Pairwise (Set.univ : Set ι)
                  (Function.onFun (AEDisjoint ν') targetAtom) ∧
                (∀ a : ι,
                  @NullMeasurableSet
                    (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                    (sourceAtom a) ν) ∧
                (∀ a : ι,
                  @NullMeasurableSet
                    (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                    (targetAtom a) ν') := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ ν ν' φ r X _ β n zAt B k hk ω cell
    targetCell hzAtInj hφInj hβInj hOutside hβFresh hB hcellUnit
    htargetCellUnit label instLabel instDecLabel sourceLabelEvent targetLabelEvent
    selectedWitnessLabels earlierFirstWitnessLabels cellPredicateLabels
    retainedCommonSourceTestLabels alreadyPrivateTargetTestLabels
    globalBoundaryComplementLabels x hxOutside
  dsimp only
  intro hsourceCover htargetCover hResidualLabelStructure hsourceLabelNull
    htargetLabelNull
  let sourceAtom : Finset label → Set (Finset V × (V → ℝ)) :=
    fun truth =>
      {η | ∀ ℓ : label, (η ∈ sourceLabelEvent ℓ ↔ ℓ ∈ truth)}
  let targetAtom : Finset label → Set (Finset V' × (V' → ℝ)) :=
    fun truth =>
      {η' | ∀ ℓ : label, (η' ∈ targetLabelEvent ℓ ↔ ℓ ∈ truth)}
  have hsourceBase : @NullMeasurableSet
      (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
      Set.univ ν := nullMeasurableSet_univ
  have htargetBase : @NullMeasurableSet
      (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
      Set.univ ν' := nullMeasurableSet_univ
  rcases
      @SamplingFiniteBooleanAtomPartition label (Finset V × (V → ℝ))
        instLabel instDecLabel (MeasurableSpace.prod ⊤ inferInstance)
        ν (Set.univ : Set (Finset V × (V → ℝ))) sourceLabelEvent
        hsourceBase hsourceLabelNull with
    ⟨sourceAtom₀, hsourceAtom₀_def, _hsourceUnivCover, hsourceDisjoint₀,
      hsourceNull₀⟩
  rcases
      @SamplingFiniteBooleanAtomPartition label (Finset V' × (V' → ℝ))
        instLabel instDecLabel (MeasurableSpace.prod ⊤ inferInstance)
        ν' (Set.univ : Set (Finset V' × (V' → ℝ))) targetLabelEvent
        htargetBase htargetLabelNull with
    ⟨targetAtom₀, htargetAtom₀_def, _htargetUnivCover, htargetDisjoint₀,
      htargetNull₀⟩
  have hsourceAtom₀_eq : sourceAtom₀ = sourceAtom := by
    funext truth
    rw [hsourceAtom₀_def truth]
    ext η
    simp [sourceAtom]
  have htargetAtom₀_eq : targetAtom₀ = targetAtom := by
    funext truth
    rw [htargetAtom₀_def truth]
    ext η'
    simp [targetAtom]
  refine
    ⟨Finset label, inferInstance, sourceAtom, targetAtom, label, instLabel,
      sourceLabelEvent, targetLabelEvent, (fun truth ℓ => decide (ℓ ∈ truth)),
      selectedWitnessLabels, earlierFirstWitnessLabels, cellPredicateLabels,
      retainedCommonSourceTestLabels, alreadyPrivateTargetTestLabels,
      globalBoundaryComplementLabels, hResidualLabelStructure, hsourceCover,
      htargetCover, ?_, ?_, ?_, ?_⟩
  · simpa [hsourceAtom₀_eq] using hsourceDisjoint₀
  · simpa [htargetAtom₀_eq] using htargetDisjoint₀
  · intro a
    simpa [hsourceAtom₀_eq] using hsourceNull₀ a
  · intro a
    simpa [htargetAtom₀_eq] using htargetNull₀ a
