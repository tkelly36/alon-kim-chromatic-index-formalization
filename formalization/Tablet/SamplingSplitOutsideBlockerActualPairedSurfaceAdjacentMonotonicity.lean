import Tablet.SamplingSplitOutsideBlockerActualOneStepMixedProductComparison
import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualPairedSurfaceAdjacentMonotonicity]
theorem SamplingSplitOutsideBlockerActualPairedSurfaceAdjacentMonotonicity :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ (Delta : ℕ) (gamma : ℝ)
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
            (w : Ω → ℝ)
            (surface :
              SamplingSplitOutsideBlockerPairedMixedMeasureSurface
                G G' φ r X n zAt B hOutside β cell targetCell w),
            (adjacent_shared_context_comparison :
              ∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                ∃ (unchanged leftBoundary rightBoundary : ℝ),
                  surface.mixedMass k ω = unchanged + leftBoundary ∧
                    surface.mixedMass (k + 1) ω = unchanged + rightBoundary ∧
                      leftBoundary ≤ rightBoundary) →
            (∀ k : ℕ, k < n → ∀ ω : Ω,
              surface.mixedMass k ω ≤ surface.mixedMass (k + 1) ω) := by
-- BODY
  intro V V' Ω _ _ _ _ _
  intro G _ G' _
  intro Delta gamma ν ν' φ r X n zAt B hOutside β cell targetCell w surface
  intro adjacent_shared_context_comparison
  intro k hk ω
  rcases adjacent_shared_context_comparison k hk ω with
    ⟨unchanged, leftBoundary, rightBoundary, hleft, hright, hle⟩
  linarith
