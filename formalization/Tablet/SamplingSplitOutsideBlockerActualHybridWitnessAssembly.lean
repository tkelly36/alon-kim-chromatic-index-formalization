import Tablet.SamplingSplitOutsideBlockerActualCoordinatePackage
import Tablet.SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage
import Tablet.SamplingSplitOutsideBlockerActualSameSurfaceInputConstruction
import Tablet.SamplingSplitOutsideBlockerActualSameSurfaceInputData
import Tablet.SamplingSplitOutsideBlockerActualCompleteStageMassLaw
import Tablet.SamplingFiniteCellEndpointSumDecomposition
import Tablet.SamplingFiniteProductCylinderProjection
import Tablet.SamplingFiniteProductPriorityCoordinateExtensionLaw
import Tablet.SamplingRandomIndependentSetMatchedCoordinateExtensionLaw
import Tablet.SamplingSplitOutsideBlockerActualCompleteStageTwoPieceDecomposition
import Tablet.SamplingSplitOutsideBlockerActualCurrentAdjacentPieceMass
import Tablet.SamplingSplitOutsideBlockerFirstWitnessCellRefinement
import Tablet.SamplingSplitOutsideBlockerMixedContextProjectionSubsets
import Tablet.SamplingSplitOutsideBlockerMixedStageEndpointIdentities
import Tablet.SamplingSplitOutsideBlockerOutsideBkResidualLabelPartition
import Tablet.SamplingSplitOutsideBlockerOutsideBkResidualSurfaceIncludesGlobalBoundary
import Tablet.SamplingSplitOutsideBlockerSameWitnessAdjacentEvents
import Tablet.SamplingSplitOutsideBlockerUnchangedCandidateUnionProjection

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualHybridWitnessAssembly]
theorem SamplingSplitOutsideBlockerActualHybridWitnessAssembly :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ,
            ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
            ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              0 ≤ gamma / (Delta : ℝ) →
              gamma / (Delta : ℝ) ≤ 1 →
              (∀ A : Finset V,
                ν {ω | ω.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V).card - A.card))) →
              (∀ A : Finset V, ∀ t : V → ℝ,
                (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν {ω |
                    ω.1 = A ∧
                      ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                    ν {ω | ω.1 = A} *
                      ENNReal.ofReal (∏ v : V, t v)) →
              (∀ A : Finset V',
                ν' {ω | ω.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V').card - A.card))) →
              (∀ A : Finset V', ∀ t : V' → ℝ,
                (∀ v : V', t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν' {ω |
                    ω.1 = A ∧
                      ∀ v : V', 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                    ν' {ω | ω.1 = A} *
                      ENNReal.ofReal (∏ v : V', t v)) →
              ∀ (φ : V → V') (r : V) (X : Finset V),
                Function.Injective φ →
                (∀ x : V, x ∈ X → G.Adj r x) →
                (∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
                  (G.Adj a b ↔ G'.Adj (φ a) (φ b))) →
                ∀ (β :
                  (Σ x : {x : V // x ∈ X},
                    {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
                  Function.Injective β →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                    ∀ y : V, y ∈ insert r X →
                      β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ≠ φ y) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      G'.Adj (φ x)
                        (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                    ∀ y : V, y ∈ X →
                      G'.Adj (φ y) (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) → y = x) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      ¬ G'.Adj (φ r)
                        (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X, ∀ w' : V',
                    G'.Adj (φ x) w' →
                      (∃ y : V, y ∈ insert r X ∧ w' = φ y ∧ G.Adj x y) ∨
                        ∃ z : V, ∃ hz : z ∉ insert r X ∧ G.Adj x z,
                          w' = β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) →
                  ∃ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (sourceCoord sourceExtensionCoord : Finset V)
                    (targetCommonCoord targetExtensionCoord targetCoord : Finset V')
                    (Ω : Type u) (_ : Fintype Ω)
                    (cell : Ω → Set (Finset V × (V → ℝ)))
                    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                    (w : Ω → ℝ)
                    (sourceStage : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (targetStage : ℕ → Ω → Set (Finset V' × (V' → ℝ)))
                    (P : ℕ → Ω → ℝ),
                    Function.Injective zAt ∧
                    (∀ k : Fin n,
                      zAt k ∉ insert r X ∧
                        (∃ x : V, x ∈ X ∧ G.Adj x (zAt k))) ∧
                    (∀ z : V, z ∉ insert r X →
                      (∃ x : V, x ∈ X ∧ G.Adj x z) →
                        ∃ k : Fin n, zAt k = z) ∧
                    (∀ k : Fin n, ∀ x : V,
                      x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) ∧
                    (∀ k : Fin n, zAt k ∈ sourceExtensionCoord) ∧
                    Disjoint sourceCoord sourceExtensionCoord ∧
                    (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) ∧
                    targetCommonCoord = sourceCoord.image φ ∧
                    Disjoint targetCommonCoord targetExtensionCoord ∧
                    targetCoord = targetCommonCoord ∪ targetExtensionCoord ∧
                    (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) ∧
                    (∀ k : Fin n, ∀ x : V, ∀ hx : x ∈ X,
                      ∀ hz : zAt k ∉ insert r X ∧ G.Adj x (zAt k),
                        β ⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩ ∈ targetExtensionCoord) ∧
                    (∀ ω : Ω, 0 ≤ w ω) ∧
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) ∧
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) ∧
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) ∧
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
                      Disjoint (targetCell ω₁) (targetCell ω₂)) ∧
                    (∀ η : Finset V × (V → ℝ),
                      (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
                        ∃ ω : Ω, η ∈ cell ω) ∧
                    (∀ η : Finset V' × (V' → ℝ),
                      (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1) →
                        ∃ ω : Ω, η ∈ targetCell ω) ∧
                    ν {η | ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)} = 0 ∧
                    ν' {η | ¬ (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1)} = 0 ∧
                    (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
                      sourceStage j ω =
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ η.1 ∧
                              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                G.Adj x y → η.2 y < η.2 x) ∧
                              ∀ i : Fin n, j ≤ (i : ℕ) → x ∈ B i →
                                ¬ (zAt i ∈ η.1 ∧
                                  η.2 x < η.2 (zAt i) ∧
                                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) ∧
                    (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
                      targetStage j ω =
                        {η' : Finset V' × (V' → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            φ x ∈ η'.1 ∧
                              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                              ∀ i : Fin n, (i : ℕ) < j → x ∈ B i →
                                ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                    η'.2 (φ x) <
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                        Set.Icc (0 : ℝ) 1)}) ∧
                    (∀ j : ℕ, ∀ ω : Ω, 0 ≤ P j ω) ∧
                    (∀ j : ℕ, ∀ ω : Ω, w ω = 0 → P j ω = 0) ∧
                    (∀ ω : Ω,
                      ENNReal.ofReal (w ω * P 0 ω) =
                        ν ({η |
                          ((Finset.univ.filter fun z : V =>
                            z ∈ η.1 ∧
                              ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                              X).Nonempty} ∩ cell ω)) ∧
                    (∀ ω : Ω,
                      ENNReal.ofReal (w ω * P n ω) =
                        ν' ({η |
                          ((Finset.univ.filter fun z : V' =>
                            z ∈ η.1 ∧
                              ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                              X.image φ).Nonempty} ∩ targetCell ω)) ∧
                    ENNReal.ofReal (∑ ω : Ω, w ω * P 0 ω) =
                      ν {η |
                        ((Finset.univ.filter fun z : V =>
                          z ∈ η.1 ∧
                            ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                            X).Nonempty} ∧
                    ENNReal.ofReal (∑ ω : Ω, w ω * P n ω) =
                      ν' {η |
                        ((Finset.univ.filter fun z : V' =>
                          z ∈ η.1 ∧
                            ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                            X.image φ).Nonempty} ∧
                    (∀ k : ℕ, k < n → ∀ ω : Ω, P k ω ≤ P (k + 1) ω) := by
-- BODY
  intro V V' _ _ _ _ G _ G' _ Delta gamma ν ν'
  intro hp0 hp1 hact hpriority hact' hpriority' φ r X hφ hX hlocal β
  intro hβ hfresh hadj hunique hnotr hneighbors
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  obtain ⟨n, zAt, B, sourceCoord, sourceExtensionCoord, targetCommonCoord,
    targetExtensionCoord, targetCoord, Ω, hΩ, cell, targetCell, w, hOutside,
    hinj, hhits, hcover, hB, hext, hdisj, hcontains, hcommon, hdisj',
    hcoords, hcontains', hprivate, hw, hmass, hmass', hcells, hcells',
    hsupport, hsupport', hnull, hnull', htransport, hmeas, hmeas', hE, hE',
    ⟨input⟩⟩ :=
    SamplingSplitOutsideBlockerActualSameSurfaceInputConstruction
      G G' Delta gamma ν ν' hp0 hp1 hact hpriority hact' hpriority'
      φ r X hφ hX hlocal β hβ hfresh hadj hunique hnotr hneighbors
  letI : Fintype Ω := hΩ
  let sourceStage : ℕ → Ω → Set (Finset V × (V → ℝ)) := fun j _ =>
    {η | ∃ x : V, ∃ hxX : x ∈ X, x ∈ η.1 ∧
      (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
      ∀ i : Fin n, j ≤ (i : ℕ) → x ∈ B i →
        ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
          η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}
  let targetStage : ℕ → Ω → Set (Finset V' × (V' → ℝ)) := fun j _ =>
    {η | ∃ x : V, ∃ hxX : x ∈ X, φ x ∈ η.1 ∧
      (∀ y : V, y ∈ insert r X → φ y ∈ η.1 →
        G.Adj x y → η.2 (φ y) < η.2 (φ x)) ∧
      ∀ i : Fin n, (i : ℕ) < j → x ∈ B i →
        ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
          ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η.1 ∧
            η.2 (φ x) < η.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
            η.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
  refine ⟨n, zAt, B, sourceCoord, sourceExtensionCoord, targetCommonCoord,
    targetExtensionCoord, targetCoord, Ω, hΩ, cell, targetCell, w,
    sourceStage, targetStage, input.surface.mixedMass, hinj,
    (fun k => ⟨hOutside k, hhits k⟩), hcover, hB, hext, hdisj, hcontains,
    hcommon, hdisj', hcoords, hcontains', hprivate, hw, hmass, hmass',
    hcells, hcells', hsupport, hsupport', hnull, hnull',
    (fun _ _ _ => rfl), (fun _ _ _ => rfl), input.surface.mixedMass_nonneg,
    input.surface.mixedMass_zero_of_zero_weight, input.source_endpoint_mass,
    input.target_endpoint_mass, ?_, ?_, ?_⟩
  · apply SamplingFiniteCellEndpointSumDecomposition ν _ (⋃ ω, cell ω)
      cell w (input.surface.mixedMass 0) hE hmeas hw
      (input.surface.mixedMass_nonneg 0)
      (input.surface.mixedMass_zero_of_zero_weight 0) input.source_endpoint_mass
      (fun ω => Set.subset_iUnion cell ω) hcells
    · exact Set.inter_iUnion _ _
    · apply measure_mono_null (t := {η | ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)})
        _ hnull
      intro η hη hunit
      obtain ⟨ω, hω⟩ := hsupport η hunit
      exact hη.2 (Set.mem_iUnion.mpr ⟨ω, hω⟩)
  · apply SamplingFiniteCellEndpointSumDecomposition ν' _ (⋃ ω, targetCell ω)
      targetCell w (input.surface.mixedMass n) hE' hmeas' hw
      (input.surface.mixedMass_nonneg n)
      (input.surface.mixedMass_zero_of_zero_weight n) input.target_endpoint_mass
      (fun ω => Set.subset_iUnion targetCell ω) hcells'
    · exact Set.inter_iUnion _ _
    · apply measure_mono_null (t := {η | ¬ (∀ v : V', 0 ≤ η.2 v ∧ η.2 v ≤ 1)})
        _ hnull'
      intro η hη hunit
      obtain ⟨ω, hω⟩ := hsupport' η hunit
      exact hη.2 (Set.mem_iUnion.mpr ⟨ω, hω⟩)
  · intro k hk ω
    obtain ⟨a, b, c, hleft, hright, hle⟩ :=
      input.adjacent_shared_context_comparison k hk ω
    rw [hleft, hright]
    exact add_le_add_right hle a
