import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPairedMixedMeasureSurface]
structure SamplingSplitOutsideBlockerPairedMixedMeasureSurface
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
    (β :
      (Σ x : {x : V // x ∈ X},
        {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
    (w : Ω → ℝ) where
-- BODY
  zAt_injective :
    Function.Injective zAt
  candidate_sets :
    ∀ i : Fin n, ∀ x : V, x ∈ B i ↔ x ∈ X ∧ G.Adj x (zAt i)
  sourceCoord :
    Finset V
  targetCommonCoord :
    Finset V'
  targetCommonCoord_eq :
    targetCommonCoord = sourceCoord.image φ
  sourceCoord_contains_embedded :
    ∀ x : V, x ∈ insert r X → x ∈ sourceCoord
  pairedMeasure :
    @MeasureTheory.Measure
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      (MeasurableSpace.prod
        (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))
  pairedCell :
    Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
  paired_common_trace :
    ∀ ω : Ω, ∀ ζ ∈ pairedCell ω,
      ζ.2.1 ∩ targetCommonCoord = (ζ.1.1 ∩ sourceCoord).image φ
  paired_common_priorities :
    ∀ ω : Ω, ∀ ζ ∈ pairedCell ω,
      ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v
  pairedCell_projects :
    ∀ ω : Ω, pairedCell ω ⊆
      {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
        ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω}
  pairedCell_mass :
    ∀ ω : Ω, pairedMeasure (pairedCell ω) = ENNReal.ofReal (w ω)
  mixedStage :
    ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
  mixedStage_def :
    ∀ j : ℕ, j ≤ n → ∀ ω : Ω,
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
                    ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}
  mixedMass :
    ℕ → Ω → ℝ
  mixedMass_nonneg :
    ∀ j : ℕ, ∀ ω : Ω, 0 ≤ mixedMass j ω
  mixedMass_zero_of_zero_weight :
    ∀ j : ℕ, ∀ ω : Ω, w ω = 0 → mixedMass j ω = 0
  mixedMass_measures_stage :
    ∀ j : ℕ, j ≤ n → ∀ ω : Ω,
      ENNReal.ofReal (w ω * mixedMass j ω) =
        pairedMeasure (mixedStage j ω ∩ pairedCell ω)
