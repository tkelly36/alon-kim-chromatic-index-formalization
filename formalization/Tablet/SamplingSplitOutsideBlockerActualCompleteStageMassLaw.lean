import Tablet.SamplingSplitOutsideBlockerActualOneStepMixedProductComparison
import Tablet.SamplingSplitOutsideBlockerAdjacentValueChainAssembly
import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface
import Tablet.SamplingSplitOutsideBlockerActualPairedSurfaceEndpoints
import Tablet.SamplingSplitOutsideBlockerActualPairedSurfaceAdjacentMonotonicity

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualCompleteStageMassLaw]
theorem SamplingSplitOutsideBlockerActualCompleteStageMassLaw :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ,
            ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
            ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              0 ≤ gamma / (Delta : ℝ) →
              gamma / (Delta : ℝ) ≤ 1 →
              (∀ A : Finset V,
                ν {η | η.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V).card - A.card))) →
              (∀ A : Finset V, ∀ t : V → ℝ,
                (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν {η |
                    η.1 = A ∧
                      ∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ t v} =
                    ν {η | η.1 = A} *
                      ENNReal.ofReal (∏ v : V, t v)) →
              (∀ A : Finset V',
                ν' {η | η.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V').card - A.card))) →
              (∀ A : Finset V', ∀ t : V' → ℝ,
                (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
                  ν' {η |
                    η.1 = A ∧
                      ∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ t v'} =
                    ν' {η | η.1 = A} *
                      ENNReal.ofReal (∏ v' : V', t v')) →
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
                  ∀ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (sourceCoord sourceExtensionCoord : Finset V)
                    (targetCommonCoord targetExtensionCoord targetCoord : Finset V')
                    (cell : Ω → Set (Finset V × (V → ℝ)))
                    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                    (w : Ω → ℝ)
                    (sourceStage : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (targetStage : ℕ → Ω → Set (Finset V' × (V' → ℝ)))
                    (leftAdjacentEvent : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (rightAdjacentEvent : ℕ → Ω → Set (Finset V' × (V' → ℝ))),
                    Function.Injective zAt →
                    (hActualOutside : ∀ k : Fin n,
                      zAt k ∉ insert r X ∧
                        (∃ x : V, x ∈ X ∧ G.Adj x (zAt k))) →
                    (∀ z : V, z ∉ insert r X →
                      (∃ x : V, x ∈ X ∧ G.Adj x z) →
                        ∃ k : Fin n, zAt k = z) →
                    (∀ k : Fin n, ∀ x : V,
                      x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) →
                    (∀ k : Fin n, zAt k ∈ sourceExtensionCoord) →
                    Disjoint sourceCoord sourceExtensionCoord →
                    (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) →
                    targetCommonCoord = sourceCoord.image φ →
                    Disjoint targetCommonCoord targetExtensionCoord →
                    targetCoord = targetCommonCoord ∪ targetExtensionCoord →
                    (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) →
                    (∀ k : Fin n, ∀ x : V, ∀ hx : x ∈ X,
                      ∀ hz : zAt k ∉ insert r X ∧ G.Adj x (zAt k),
                        β ⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩ ∈ targetExtensionCoord) →
                    (∀ ω : Ω, 0 ≤ w ω) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) →
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) →
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
                      Disjoint (targetCell ω₁) (targetCell ω₂)) →
                    (∀ η : Finset V × (V → ℝ),
                      (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
                        ∃ ω : Ω, η ∈ cell ω) →
                    (∀ η : Finset V' × (V' → ℝ),
                      (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1) →
                        ∃ ω : Ω, η ∈ targetCell ω) →
                    ν {η : Finset V × (V → ℝ) |
                      ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)} = 0 →
                    ν' {η : Finset V' × (V' → ℝ) |
                      ¬ (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1)} = 0 →
                    (∀ ω : Ω, ∀ η η',
                      η'.1 ∩ targetCommonCoord =
                        (η.1 ∩ sourceCoord).image φ →
                      (∀ v : V, v ∈ sourceCoord →
                        η'.2 (φ v) = η.2 v) →
                        (η ∈ cell ω ↔ η' ∈ targetCell ω)) →
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
                                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) →
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
                                        Set.Icc (0 : ℝ) 1)}) →
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      leftAdjacentEvent k ω =
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ η.1 ∧
                              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                G.Adj x y → η.2 y < η.2 x) ∧
                              (∀ i : Fin n, (k : ℕ) ≤ i → i ≠ ⟨k, hk⟩ →
                                x ∈ B i →
                                  ¬ (zAt i ∈ η.1 ∧
                                    η.2 x < η.2 (zAt i) ∧
                                      η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
                              x ∈ B ⟨k, hk⟩ ∧
                              ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                                η.2 x < η.2 (zAt ⟨k, hk⟩) ∧
                                  η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}) →
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      ∃ βFlat : V → V → V',
                        (∀ x : V, ∀ hxX : x ∈ X,
                          ∀ hxAdj : G.Adj x (zAt ⟨k, hk⟩),
                          ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X,
                            βFlat x (zAt ⟨k, hk⟩) =
                              β ⟨⟨x, hxX⟩,
                                ⟨zAt ⟨k, hk⟩, ⟨hz, hxAdj⟩⟩⟩) ∧
                        rightAdjacentEvent k ω =
                          {η' : Finset V' × (V' → ℝ) |
                            ∃ x : V, ∃ hxX : x ∈ X,
                              φ x ∈ η'.1 ∧
                                (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                  G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                                (∀ i : Fin n, (i : ℕ) < k + 1 →
                                  i ≠ ⟨k, hk⟩ → x ∈ B i →
                                    ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                      ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                        η'.2 (φ x) <
                                          η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                          η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                            Set.Icc (0 : ℝ) 1)) ∧
                                x ∈ B ⟨k, hk⟩ ∧
                                ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                                    G.Adj x (zAt ⟨k, hk⟩),
                                  ¬ (βFlat x (zAt ⟨k, hk⟩) ∈ η'.1 ∧
                                    η'.2 (φ x) <
                                      η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∧
                                      η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∈
                                        Set.Icc (0 : ℝ) 1)}) →
                    (surface :
                      SamplingSplitOutsideBlockerPairedMixedMeasureSurface
                        G G' φ r X n zAt B (fun i => (hActualOutside i).1)
                          β cell targetCell w) →
                    (source_endpoint_mass :
                      ∀ ω : Ω,
                        ENNReal.ofReal (w ω * surface.mixedMass 0 ω) =
                          ν ({η : Finset V × (V → ℝ) |
                            ((Finset.univ.filter fun z : V =>
                              z ∈ η.1 ∧
                                ∀ y : V, y ∈ η.1 → G.Adj z y →
                                  η.2 y < η.2 z) ∩ X).Nonempty} ∩ cell ω)) →
                    (target_endpoint_mass :
                      ∀ ω : Ω,
                        ENNReal.ofReal (w ω * surface.mixedMass n ω) =
                          ν' ({η : Finset V' × (V' → ℝ) |
                            ((Finset.univ.filter fun z : V' =>
                              z ∈ η.1 ∧
                                ∀ y : V', y ∈ η.1 → G'.Adj z y →
                                  η.2 y < η.2 z) ∩ X.image φ).Nonempty} ∩
                            targetCell ω)) →
                    (adjacent_shared_context_comparison :
                      ∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                        ∃ (unchanged leftBoundary rightBoundary : ℝ),
                          surface.mixedMass k ω = unchanged + leftBoundary ∧
                            surface.mixedMass (k + 1) ω =
                              unchanged + rightBoundary ∧
                              leftBoundary ≤ rightBoundary) →
                    (∃ (hybridMass : ℕ → Ω → ℝ),
                      (∀ j : ℕ, ∀ ω : Ω, 0 ≤ hybridMass j ω) ∧
                      (∀ j : ℕ, ∀ ω : Ω, w ω = 0 → hybridMass j ω = 0) ∧
                      (∀ ω : Ω,
                        ENNReal.ofReal (w ω * hybridMass 0 ω) =
                          ν ({η |
                            ((Finset.univ.filter fun z : V =>
                              z ∈ η.1 ∧
                                ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                                X).Nonempty} ∩ cell ω)) ∧
                      (∀ ω : Ω,
                        ENNReal.ofReal (w ω * hybridMass n ω) =
                          ν' ({η |
                            ((Finset.univ.filter fun z : V' =>
                              z ∈ η.1 ∧
                                ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                                X.image φ).Nonempty} ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        hybridMass k ω ≤ hybridMass (k + 1) ω)) := by
-- BODY
  intro V V' Ω _ _ _ _ _
  intro G _ G' _
  intro Delta gamma ν ν' hgamma_nonneg hgamma_le hsource_activation
  intro hsource_priority htarget_activation htarget_priority
  intro φ r X hφ hX hlocal β hβ hβ_fresh hβ_adj hβ_unique hβ_not_r hβ_exhaust
  intro n zAt B sourceCoord sourceExtensionCoord
  intro targetCommonCoord targetExtensionCoord targetCoord
  intro cell targetCell w sourceStage targetStage leftAdjacentEvent rightAdjacentEvent
  intro hzAt_inj hActualOutside hcover hB hsourceExt hdisjSource hsourceCoord
  intro htargetCommon hdisjTarget htargetCoord htargetCommon_mem htargetExt
  intro hw_nonneg hw_source hw_target hcell_disj htargetCell_disj
  intro hcell_cover htargetCell_cover hsource_null htarget_null hcell_transport
  intro hsourceStage htargetStage hleftAdjacent hrightAdjacent
  intro surface source_endpoint_mass target_endpoint_mass adjacent_shared_context_comparison
  refine ⟨surface.mixedMass, ?_, ?_, ?_, ?_, ?_⟩
  · exact surface.mixedMass_nonneg
  · exact surface.mixedMass_zero_of_zero_weight
  · exact source_endpoint_mass
  · exact target_endpoint_mass
  · exact
      SamplingSplitOutsideBlockerActualPairedSurfaceAdjacentMonotonicity G G'
        Delta gamma ν ν' φ r X n zAt B (fun i => (hActualOutside i).1)
        β cell targetCell w surface adjacent_shared_context_comparison
