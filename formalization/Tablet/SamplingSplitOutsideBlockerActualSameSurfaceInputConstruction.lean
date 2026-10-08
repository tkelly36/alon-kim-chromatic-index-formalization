import Tablet.SamplingSplitOutsideBlockerActualCoordinatePackage
import Tablet.SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage
import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingConstruction
import Tablet.SamplingSplitOutsideBlockerActualSameSurfaceInputData
import Tablet.SamplingSplitOutsideBlockerActualSourceEndpointFromCoupling
import Tablet.SamplingSplitOutsideBlockerActualTargetEndpointFromCoupling
import Tablet.SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer
import Tablet.SamplingSplitOutsideBlockerPairedContextCurrentInvariant
import Tablet.SamplingSplitOutsideBlockerActualMixedStageMassNormalization
import Tablet.SamplingSplitOutsideBlockerProductAtomContextInvariant
import Tablet.SamplingSplitOutsideBlockerActualProductAdjacentIntegral

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualSameSurfaceInputConstruction]
theorem SamplingSplitOutsideBlockerActualSameSurfaceInputConstruction :
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
                    (hOutside : ∀ k : Fin n, zAt k ∉ insert r X),
                    Function.Injective zAt ∧
                    (∀ k : Fin n, ∃ x : V, x ∈ X ∧ G.Adj x (zAt k)) ∧
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
                    ν {η : Finset V × (V → ℝ) |
                      ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)} = 0 ∧
                    ν' {η : Finset V' × (V' → ℝ) |
                      ¬ (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1)} = 0 ∧
                    (∀ ω : Ω, ∀ η η',
                      η'.1 ∩ targetCommonCoord =
                        (η.1 ∩ sourceCoord).image φ →
                      (∀ v : V, v ∈ sourceCoord →
                        η'.2 (φ v) = η.2 v) →
                        (η ∈ cell ω ↔ η' ∈ targetCell ω)) ∧
                    (∀ ω : Ω,
                      @MeasurableSet (Finset V × (V → ℝ))
                        (MeasurableSpace.prod ⊤ inferInstance) (cell ω)) ∧
                    (∀ ω : Ω,
                      @MeasurableSet (Finset V' × (V' → ℝ))
                        (MeasurableSpace.prod ⊤ inferInstance) (targetCell ω)) ∧
                    @MeasurableSet (Finset V × (V → ℝ))
                      (MeasurableSpace.prod ⊤ inferInstance)
                      {η : Finset V × (V → ℝ) |
                        ((Finset.univ.filter fun z : V =>
                          z ∈ η.1 ∧
                            ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                            X).Nonempty} ∧
                    @MeasurableSet (Finset V' × (V' → ℝ))
                      (MeasurableSpace.prod ⊤ inferInstance)
                      {η : Finset V' × (V' → ℝ) |
                        ((Finset.univ.filter fun z : V' =>
                          z ∈ η.1 ∧
                            ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                      X.image φ).Nonempty} ∧
                    Nonempty
                      (SamplingSplitOutsideBlockerActualSameSurfaceInputData
                        G G' ν ν' φ r X n zAt B hOutside β cell targetCell w) := by
-- BODY
  intro V V' _ _ _ _ G _ G' _ Delta gamma ν ν'
  intro hgamma_nonneg hgamma_le hsource_activation hsource_priority
  intro htarget_activation htarget_priority φ r X hφ hX_neighbors hφ_adj β
  intro hβ_inj hβ_fresh hβ_adj hβ_unique hβ_not_r hβ_neighbor
  rcases
    SamplingSplitOutsideBlockerActualCoordinatePackage
      (G := G) (G' := G') φ r X hφ β hβ_inj hβ_fresh hβ_adj with
    ⟨n, zAt, B, sourceCoord, sourceExtensionCoord, targetCommonCoord,
      targetExtensionCoord, targetCoord, hzAt_hits, hzAt_cover, hB,
      hzAt_sourceExtension, hsource_disjoint, hsource_contains,
      htargetCommon_eq, htarget_disjoint, htargetCoord, htarget_contains,
      hβ_targetExtension, hzAt_inj⟩
  let hOutside : ∀ k : Fin n, zAt k ∉ insert r X := fun k => (hzAt_hits k).1
  rcases
    SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage
      (G := G) (G' := G') Delta gamma ν ν' hgamma_nonneg hgamma_le
      hsource_activation hsource_priority htarget_activation htarget_priority
      φ r X hφ β hβ_inj hβ_fresh hβ_adj n zAt B sourceCoord
      sourceExtensionCoord targetCommonCoord targetExtensionCoord targetCoord
      hzAt_inj hzAt_hits hzAt_cover hB hzAt_sourceExtension hsource_disjoint
      hsource_contains htargetCommon_eq htarget_disjoint htargetCoord
      htarget_contains hβ_targetExtension with
    ⟨Ω, hΩ, cell, targetCell, w, hw_nonneg, hw_source, hw_target,
      hcell_disjoint, htargetCell_disjoint, hcell_cover, htargetCell_cover,
      hnu_null, hnu'_null, htransport, hcell_meas, htargetCell_meas,
      hsource_endpoint_meas, htarget_endpoint_meas⟩
  letI : Fintype Ω := hΩ
  rcases
    SamplingSplitOutsideBlockerMarginalPreservingCouplingConstruction
      (V := V) (V' := V') (Ω := Ω) Delta gamma ν ν' hgamma_nonneg
      hgamma_le hsource_activation hsource_priority htarget_activation
      htarget_priority φ sourceCoord targetCommonCoord cell targetCell w hφ
      htargetCommon_eq hw_nonneg hw_source hw_target hcell_disjoint
      htargetCell_disjoint htransport hcell_meas htargetCell_meas with
    ⟨coupling, ⟨productRealization⟩, hpairedCell_def⟩
  rcases
    SamplingSplitOutsideBlockerActualMixedStageMassNormalization
      (G := G) ν ν' φ r X n zAt B sourceCoord targetCommonCoord cell
      targetCell w hOutside β coupling hw_nonneg with
    ⟨mixedStage, mixedMass, hmixedStage_def, hmixedMass_nonneg,
      hmixedMass_zero, hmixedMass_measure⟩
  let surface : SamplingSplitOutsideBlockerPairedMixedMeasureSurface
      G G' φ r X n zAt B hOutside β cell targetCell w :=
    { zAt_injective := hzAt_inj
      candidate_sets := hB
      sourceCoord := sourceCoord
      targetCommonCoord := targetCommonCoord
      targetCommonCoord_eq := htargetCommon_eq
      sourceCoord_contains_embedded := hsource_contains
      pairedMeasure := coupling.pairedMeasure
      pairedCell := coupling.pairedCell
      paired_common_trace := coupling.pairedCell_common_trace
      paired_common_priorities := coupling.pairedCell_common_priorities
      pairedCell_projects := coupling.pairedCell_projects
      pairedCell_mass := coupling.pairedCell_mass
      mixedStage := mixedStage
      mixedStage_def := hmixedStage_def
      mixedMass := mixedMass
      mixedMass_nonneg := hmixedMass_nonneg
      mixedMass_zero_of_zero_weight := hmixedMass_zero
      mixedMass_measures_stage := hmixedMass_measure }
  have hsource := SamplingSplitOutsideBlockerActualSourceEndpointFromCoupling
    G G' ν ν' φ r X n zAt B hOutside β sourceCoord targetCommonCoord
    cell targetCell w (gamma / (Delta : ℝ)) coupling surface hφ hzAt_cover
    rfl rfl hgamma_nonneg hgamma_le hsource_activation hsource_priority
    hsource_endpoint_meas
  have htarget := SamplingSplitOutsideBlockerActualTargetEndpointFromCoupling
    G G' ν ν' φ r X n zAt B hOutside β sourceCoord targetCommonCoord
    cell targetCell w (gamma / (Delta : ℝ)) coupling surface hφ hφ_adj
    hβ_adj hβ_unique hβ_not_r hβ_neighbor hzAt_cover rfl rfl
    hgamma_nonneg hgamma_le htarget_activation htarget_priority
    htarget_endpoint_meas
  have hcurrent (i : Fin n) : zAt i ∉ surface.sourceCoord := by
    intro hi
    exact Finset.disjoint_left.mp hsource_disjoint hi (hzAt_sourceExtension i)
  have hprivate (i : Fin n) (x : {x : V // x ∈ X})
      (hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i)) :
      β ⟨x, ⟨zAt i, hz⟩⟩ ∉ surface.targetCommonCoord := by
    intro hi
    exact Finset.disjoint_left.mp htarget_disjoint hi
      (hβ_targetExtension i x.1 x.2 hz)
  have hadjacent : ∀ k : ℕ, k < n → ∀ ω : Ω,
      ∃ unchanged leftBoundary rightBoundary : ℝ,
        surface.mixedMass k ω = unchanged + leftBoundary ∧
        surface.mixedMass (k + 1) ω = unchanged + rightBoundary ∧
        leftBoundary ≤ rightBoundary := by
    intro k hk ω
    obtain ⟨a, b, c, _, _, _, _, _, _, hleft, hright, hle⟩ :=
      SamplingSplitOutsideBlockerActualProductAdjacentIntegral
        G G' φ r X n zAt B hOutside β cell targetCell w surface
        (gamma / (Delta : ℝ)) hgamma_nonneg hgamma_le productRealization
        hβ_inj (fun a y hy => hβ_fresh a.1.1 a.1.2 a.2.1 a.2.2 y hy)
        hcurrent hprivate hw_nonneg hcell_meas htargetCell_meas
        htransport hpairedCell_def ⟨k, hk⟩ ω
    exact ⟨a, b, c, hleft, hright, hle⟩
  refine ⟨n, zAt, B, sourceCoord, sourceExtensionCoord, targetCommonCoord,
    targetExtensionCoord, targetCoord, Ω, hΩ, cell, targetCell, w, hOutside,
    hzAt_inj, ?_, hzAt_cover, hB, hzAt_sourceExtension, hsource_disjoint,
    hsource_contains, htargetCommon_eq, htarget_disjoint, htargetCoord,
    htarget_contains, hβ_targetExtension, hw_nonneg, hw_source, hw_target,
    hcell_disjoint, htargetCell_disjoint, hcell_cover, htargetCell_cover,
    hnu_null, hnu'_null, htransport, hcell_meas, htargetCell_meas,
    hsource_endpoint_meas, htarget_endpoint_meas, ?_⟩
  · exact fun k => (hzAt_hits k).2
  · exact ⟨{ surface := surface
             source_endpoint_mass := hsource
             target_endpoint_mass := htarget
             adjacent_shared_context_comparison := hadjacent }⟩
