import Tablet.SamplingFiniteMassSubcellNormalization
import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingData

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualMixedStageMassNormalization]
theorem SamplingSplitOutsideBlockerActualMixedStageMassNormalization :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (φ : V → V') (r : V) (X : Finset V)
          (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
          (sourceCoord : Finset V) (targetCommonCoord : Finset V')
          (cell : Ω → Set (Finset V × (V → ℝ)))
          (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
          (w : Ω → ℝ)
          (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
          (β :
            (Σ x : {x : V // x ∈ X},
              {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
          (coupling :
            SamplingSplitOutsideBlockerMarginalPreservingCouplingData
              ν ν' φ sourceCoord targetCommonCoord cell targetCell w),
          (∀ ω : Ω, 0 ≤ w ω) →
          ∃ (mixedStage :
              ℕ → Ω →
                Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))))
            (mixedMass : ℕ → Ω → ℝ),
            (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
              mixedStage j ω =
                {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
                  ∃ x : V, ∃ hxX : x ∈ X,
                    x ∈ ζ.1.1 ∧
                      φ x ∈ ζ.2.1 ∧
                      (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
                        G.Adj x y → ζ.1.2 y < ζ.1.2 x) ∧
                      (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
                        G.Adj x y → ζ.2.2 (φ y) < ζ.2.2 (φ x)) ∧
                      (∀ i : Fin n, (i : ℕ) < j → x ∈ B i →
                        ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                          ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ ζ.2.1 ∧
                            ζ.2.2 (φ x) <
                              ζ.2.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                ζ.2.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                  Set.Icc (0 : ℝ) 1)) ∧
                      (∀ i : Fin n, j ≤ (i : ℕ) → x ∈ B i →
                        ¬ (zAt i ∈ ζ.1.1 ∧
                          ζ.1.2 x < ζ.1.2 (zAt i) ∧
                            ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}) ∧
            (∀ j : ℕ, ∀ ω : Ω, 0 ≤ mixedMass j ω) ∧
            (∀ j : ℕ, ∀ ω : Ω, w ω = 0 → mixedMass j ω = 0) ∧
            (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
              ENNReal.ofReal (w ω * mixedMass j ω) =
                coupling.pairedMeasure (mixedStage j ω ∩ coupling.pairedCell ω)) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ ν ν' φ r X n zAt B sourceCoord
  intro targetCommonCoord cell targetCell w hOutside β coupling hw_nonneg
  let mixedStage :
      ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun j ω =>
      {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
        ∃ x : V, ∃ hxX : x ∈ X,
          x ∈ ζ.1.1 ∧
            φ x ∈ ζ.2.1 ∧
            (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
              G.Adj x y → ζ.1.2 y < ζ.1.2 x) ∧
            (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
              G.Adj x y → ζ.2.2 (φ y) < ζ.2.2 (φ x)) ∧
            (∀ i : Fin n, (i : ℕ) < j → x ∈ B i →
              ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ ζ.2.1 ∧
                  ζ.2.2 (φ x) <
                    ζ.2.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                      ζ.2.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                        Set.Icc (0 : ℝ) 1)) ∧
            (∀ i : Fin n, j ≤ (i : ℕ) → x ∈ B i →
              ¬ (zAt i ∈ ζ.1.1 ∧
                ζ.1.2 x < ζ.1.2 (zAt i) ∧
                  ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}
  letI : MeasurableSpace
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    MeasurableSpace.prod (MeasurableSpace.prod ⊤ inferInstance)
      (MeasurableSpace.prod ⊤ inferInstance)
  have hnorm :
      ∀ j : ℕ, ∀ ω : Ω,
        ∃ p : ℝ, 0 ≤ p ∧ (w ω = 0 → p = 0) ∧
          ENNReal.ofReal (w ω * p) =
            coupling.pairedMeasure (mixedStage j ω ∩ coupling.pairedCell ω) := by
    intro j ω
    exact
      SamplingFiniteMassSubcellNormalization coupling.pairedMeasure (w ω)
        (coupling.pairedCell ω) (mixedStage j ω ∩ coupling.pairedCell ω)
        (hw_nonneg ω) (coupling.pairedCell_mass ω).symm (by
          intro ζ hζ
          exact hζ.2)
  choose mixedMass hmixedMass_nonneg hmixedMass_zero hmixedMass_measure using hnorm
  refine ⟨mixedStage, mixedMass, ?_, ?_, ?_, ?_⟩
  · intro j hj ω
    rfl
  · exact hmixedMass_nonneg
  · exact hmixedMass_zero
  · intro j hj ω
    exact hmixedMass_measure j ω
