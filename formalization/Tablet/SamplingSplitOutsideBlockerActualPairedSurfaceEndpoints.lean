import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualPairedSurfaceEndpoints]
theorem SamplingSplitOutsideBlockerActualPairedSurfaceEndpoints :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
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
            (source_endpoint_projection :
              ∀ ω : Ω,
                {η : Finset V × (V → ℝ) |
                  ∃ η' : Finset V' × (V' → ℝ),
                    (η, η') ∈ surface.mixedStage 0 ω ∩ surface.pairedCell ω} =
                  {η : Finset V × (V → ℝ) |
                    ((Finset.univ.filter fun z : V =>
                      z ∈ η.1 ∧
                        ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                        X).Nonempty} ∩ cell ω) →
            (source_endpoint_marginal :
              ∀ ω : Ω,
                surface.pairedMeasure (surface.mixedStage 0 ω ∩ surface.pairedCell ω) =
                  ν {η : Finset V × (V → ℝ) |
                    ∃ η' : Finset V' × (V' → ℝ),
                      (η, η') ∈ surface.mixedStage 0 ω ∩ surface.pairedCell ω}) →
            (target_endpoint_projection :
              ∀ ω : Ω,
                {η' : Finset V' × (V' → ℝ) |
                  ∃ η : Finset V × (V → ℝ),
                    (η, η') ∈ surface.mixedStage n ω ∩ surface.pairedCell ω} =
                  {η : Finset V' × (V' → ℝ) |
                    ((Finset.univ.filter fun z : V' =>
                      z ∈ η.1 ∧
                        ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                        X.image φ).Nonempty} ∩ targetCell ω) →
            (target_endpoint_marginal :
              ∀ ω : Ω,
                surface.pairedMeasure (surface.mixedStage n ω ∩ surface.pairedCell ω) =
                  ν' {η' : Finset V' × (V' → ℝ) |
                    ∃ η : Finset V × (V → ℝ),
                      (η, η') ∈ surface.mixedStage n ω ∩ surface.pairedCell ω}) →
            (∀ ω : Ω,
              ENNReal.ofReal (w ω * surface.mixedMass 0 ω) =
                ν ({η : Finset V × (V → ℝ) |
                  ((Finset.univ.filter fun z : V =>
                    z ∈ η.1 ∧
                      ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                      X).Nonempty} ∩ cell ω)) ∧
            (∀ ω : Ω,
              ENNReal.ofReal (w ω * surface.mixedMass n ω) =
                ν' ({η : Finset V' × (V' → ℝ) |
                  ((Finset.univ.filter fun z : V' =>
                    z ∈ η.1 ∧
                      ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                      X.image φ).Nonempty} ∩ targetCell ω)) := by
-- BODY
  intro V V' Ω _ _ _ _ _
  intro G _ G' _
  intro ν ν' φ r X n zAt B hOutside β cell targetCell w surface
  intro source_endpoint_projection source_endpoint_marginal
  intro target_endpoint_projection target_endpoint_marginal
  constructor
  · intro ω
    calc
      ENNReal.ofReal (w ω * surface.mixedMass 0 ω)
          = surface.pairedMeasure (surface.mixedStage 0 ω ∩ surface.pairedCell ω) :=
            surface.mixedMass_measures_stage 0 (Nat.zero_le n) ω
      _ = ν {η : Finset V × (V → ℝ) |
            ∃ η' : Finset V' × (V' → ℝ),
              (η, η') ∈ surface.mixedStage 0 ω ∩ surface.pairedCell ω} :=
            source_endpoint_marginal ω
      _ = ν ({η : Finset V × (V → ℝ) |
            ((Finset.univ.filter fun z : V =>
              z ∈ η.1 ∧
                ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                X).Nonempty} ∩ cell ω) := by
            rw [source_endpoint_projection ω]
  · intro ω
    calc
      ENNReal.ofReal (w ω * surface.mixedMass n ω)
          = surface.pairedMeasure (surface.mixedStage n ω ∩ surface.pairedCell ω) :=
            surface.mixedMass_measures_stage n (Nat.le_refl n) ω
      _ = ν' {η' : Finset V' × (V' → ℝ) |
            ∃ η : Finset V × (V → ℝ),
              (η, η') ∈ surface.mixedStage n ω ∩ surface.pairedCell ω} :=
            target_endpoint_marginal ω
      _ = ν' ({η : Finset V' × (V' → ℝ) |
            ((Finset.univ.filter fun z : V' =>
              z ∈ η.1 ∧
                ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                X.image φ).Nonempty} ∩ targetCell ω) := by
            rw [target_endpoint_projection ω]
