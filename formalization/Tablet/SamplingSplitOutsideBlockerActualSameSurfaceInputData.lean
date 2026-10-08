import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualSameSurfaceInputData]
structure SamplingSplitOutsideBlockerActualSameSurfaceInputData
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
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
  surface :
    SamplingSplitOutsideBlockerPairedMixedMeasureSurface
      G G' φ r X n zAt B hOutside β cell targetCell w
  source_endpoint_mass :
    ∀ ω : Ω,
      ENNReal.ofReal (w ω * surface.mixedMass 0 ω) =
        ν ({η : Finset V × (V → ℝ) |
          ((Finset.univ.filter fun z : V =>
            z ∈ η.1 ∧
              ∀ y : V, y ∈ η.1 → G.Adj z y →
                η.2 y < η.2 z) ∩ X).Nonempty} ∩ cell ω)
  target_endpoint_mass :
    ∀ ω : Ω,
      ENNReal.ofReal (w ω * surface.mixedMass n ω) =
        ν' ({η : Finset V' × (V' → ℝ) |
          ((Finset.univ.filter fun z : V' =>
            z ∈ η.1 ∧
              ∀ y : V', y ∈ η.1 → G'.Adj z y →
                η.2 y < η.2 z) ∩ X.image φ).Nonempty} ∩
          targetCell ω)
  adjacent_shared_context_comparison :
    ∀ k : ℕ, k < n → ∀ ω : Ω,
      ∃ (unchanged leftBoundary rightBoundary : ℝ),
        surface.mixedMass k ω = unchanged + leftBoundary ∧
          surface.mixedMass (k + 1) ω = unchanged + rightBoundary ∧
            leftBoundary ≤ rightBoundary
