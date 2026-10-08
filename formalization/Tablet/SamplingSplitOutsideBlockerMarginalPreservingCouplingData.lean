import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMarginalPreservingCouplingData]
structure SamplingSplitOutsideBlockerMarginalPreservingCouplingData
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (φ : V → V') (sourceCoord : Finset V) (targetCommonCoord : Finset V')
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
    (w : Ω → ℝ) where
-- BODY
  pairedMeasure :
    @MeasureTheory.Measure
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      (MeasurableSpace.prod
        (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))
  pairedCell :
    Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
  pairedCell_projects :
    ∀ ω : Ω, pairedCell ω ⊆
      {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
        ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω}
  pairedCell_mass :
    ∀ ω : Ω, pairedMeasure (pairedCell ω) = ENNReal.ofReal (w ω)
  pairedCell_common_trace :
    ∀ ω : Ω, ∀ ζ ∈ pairedCell ω,
      ζ.2.1 ∩ targetCommonCoord = (ζ.1.1 ∩ sourceCoord).image φ
  pairedCell_common_priorities :
    ∀ ω : Ω, ∀ ζ ∈ pairedCell ω,
      ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v
  source_restricted_marginal :
    ∀ ω : Ω, ∀ E : Set (Finset V × (V → ℝ)),
      @MeasurableSet (Finset V × (V → ℝ))
        (MeasurableSpace.prod ⊤ inferInstance) E →
      pairedMeasure ({ζ | ζ.1 ∈ E} ∩ pairedCell ω) = ν (E ∩ cell ω)
  target_restricted_marginal :
    ∀ ω : Ω, ∀ E' : Set (Finset V' × (V' → ℝ)),
      @MeasurableSet (Finset V' × (V' → ℝ))
        (MeasurableSpace.prod ⊤ inferInstance) E' →
      pairedMeasure ({ζ | ζ.2 ∈ E'} ∩ pairedCell ω) = ν' (E' ∩ targetCell ω)
