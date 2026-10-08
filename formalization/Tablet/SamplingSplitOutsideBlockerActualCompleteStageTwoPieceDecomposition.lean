import Tablet.SamplingSplitOutsideBlockerTrueHybridStageSurface
import Tablet.SamplingSplitOutsideBlockerMixedStageCompleteDecomposition
import Tablet.SamplingFiniteMassSubcellNormalization

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualCompleteStageTwoPieceDecomposition]
theorem SamplingSplitOutsideBlockerActualCompleteStageTwoPieceDecomposition :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
            ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              ∀ (φ : V → V') (r : V) (X : Finset V),
                ∀ (β :
                  (Σ x : {x : V // x ∈ X},
                    {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
                  ∀ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (Ω : Type u) (_ : Fintype Ω)
                    (cell : Ω → Set (Finset V × (V → ℝ)))
                    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                    (w : Ω → ℝ)
                    (leftAdjacentEvent : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (rightAdjacentEvent : ℕ → Ω → Set (Finset V' × (V' → ℝ))),
                    Function.Injective zAt →
                    (∀ k : Fin n, ∀ x : V,
                      x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) →
                    (∀ ω : Ω, 0 ≤ w ω) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) →
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
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      leftAdjacentEvent k ω ⊆
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ η.1 ∧
                              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                G.Adj x y → η.2 y < η.2 x) ∧
                              ∀ i : Fin n, (k : ℕ) ≤ i → x ∈ B i →
                                ¬ (zAt i ∈ η.1 ∧
                                  η.2 x < η.2 (zAt i) ∧
                                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) →
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      rightAdjacentEvent k ω ⊆
                        {η' : Finset V' × (V' → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            φ x ∈ η'.1 ∧
                              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                              ∀ i : Fin n, (i : ℕ) < k + 1 → x ∈ B i →
                                ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                    η'.2 (φ x) <
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                        Set.Icc (0 : ℝ) 1)}) →
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      @MeasurableSet (Finset V × (V → ℝ))
                        (MeasurableSpace.prod ⊤ inferInstance)
                        (leftAdjacentEvent k ω ∩ cell ω)) →
                    (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
                      @MeasurableSet (Finset V' × (V' → ℝ))
                        (MeasurableSpace.prod ⊤ inferInstance)
                        (rightAdjacentEvent k ω ∩ targetCell ω)) →
                    ∃ (sourceComplete sourceUnchanged sourceBoundary :
                          ℕ → Ω → Set (Finset V × (V → ℝ)))
                      (targetComplete targetUnchanged targetBoundary :
                          ℕ → Ω → Set (Finset V' × (V' → ℝ)))
                      (sourceMass sourceUnchangedMass sourceBoundaryMass
                        targetMass targetUnchangedMass targetBoundaryMass :
                          ℕ → Ω → ℝ),
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        sourceComplete k ω =
                          {η |
                            ∃ x : V, ∃ hxX : x ∈ X,
                              x ∈ η.1 ∧
                                (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                  G.Adj x y → η.2 y < η.2 x) ∧
                                ∀ i : Fin n, (k : ℕ) ≤ i → x ∈ B i →
                                  ¬ (zAt i ∈ η.1 ∧
                                    η.2 x < η.2 (zAt i) ∧
                                      η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        targetComplete (k + 1) ω =
                          {η' |
                            ∃ x : V, ∃ hxX : x ∈ X,
                              φ x ∈ η'.1 ∧
                                (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                  G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                                ∀ i : Fin n, (i : ℕ) < k + 1 → x ∈ B i →
                                  ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                    ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                      η'.2 (φ x) <
                                        η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                        η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                          Set.Icc (0 : ℝ) 1)}) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        sourceBoundary k ω = leftAdjacentEvent k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        targetBoundary k ω = rightAdjacentEvent k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        sourceUnchanged k ω =
                          sourceComplete k ω \ sourceBoundary k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        targetUnchanged k ω =
                          targetComplete (k + 1) ω \ targetBoundary k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        sourceComplete k ω ∩ cell ω =
                          (sourceUnchanged k ω ∪ sourceBoundary k ω) ∩ cell ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        Disjoint (sourceUnchanged k ω ∩ cell ω)
                          (sourceBoundary k ω ∩ cell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        targetComplete (k + 1) ω ∩ targetCell ω =
                          (targetUnchanged k ω ∪ targetBoundary k ω) ∩ targetCell ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        Disjoint (targetUnchanged k ω ∩ targetCell ω)
                          (targetBoundary k ω ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        0 ≤ sourceMass k ω ∧ 0 ≤ sourceUnchangedMass k ω ∧
                          0 ≤ sourceBoundaryMass k ω ∧
                          sourceMass k ω =
                            sourceUnchangedMass k ω + sourceBoundaryMass k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        0 ≤ targetMass (k + 1) ω ∧ 0 ≤ targetUnchangedMass k ω ∧
                          0 ≤ targetBoundaryMass k ω ∧
                          targetMass (k + 1) ω =
                            targetUnchangedMass k ω + targetBoundaryMass k ω) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ν (sourceComplete k ω ∩ cell ω) =
                          ν (sourceUnchanged k ω ∩ cell ω) +
                            ν (sourceBoundary k ω ∩ cell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ν' (targetComplete (k + 1) ω ∩ targetCell ω) =
                          ν' (targetUnchanged k ω ∩ targetCell ω) +
                            ν' (targetBoundary k ω ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * sourceMass k ω) =
                          ν (sourceComplete k ω ∩ cell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * sourceUnchangedMass k ω) =
                          ν (sourceUnchanged k ω ∩ cell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * sourceBoundaryMass k ω) =
                          ν (sourceBoundary k ω ∩ cell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * targetMass (k + 1) ω) =
                          ν' (targetComplete (k + 1) ω ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * targetUnchangedMass k ω) =
                          ν' (targetUnchanged k ω ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        ENNReal.ofReal (w ω * targetBoundaryMass k ω) =
                          ν' (targetBoundary k ω ∩ targetCell ω)) ∧
                      (∀ k : ℕ, k < n → ∀ ω : Ω,
                        w ω = 0 →
                          sourceMass k ω = 0 ∧ sourceUnchangedMass k ω = 0 ∧
                            sourceBoundaryMass k ω = 0 ∧
                            targetMass (k + 1) ω = 0 ∧
                            targetUnchangedMass k ω = 0 ∧
                            targetBoundaryMass k ω = 0) := by
-- BODY
  classical
  intro V V' _ _ _ _ G _ G' _ ν ν' φ r X β n zAt B Ω _ cell targetCell w
  intro leftAdjacentEvent rightAdjacentEvent hzAt_inj hB hw_nonneg hw_source
  intro hw_target hleftAdjacent hrightAdjacent hsourceBoundary_subset
  intro htargetBoundary_subset hsourceBoundary_meas htargetBoundary_meas
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  letI : MeasurableSpace (Finset V' × (V' → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let sourceComplete : ℕ → Ω → Set (Finset V × (V → ℝ)) :=
    fun k _ω =>
      {η |
        ∃ x : V, ∃ hxX : x ∈ X,
          x ∈ η.1 ∧
            (∀ y : V, y ∈ insert r X → y ∈ η.1 →
              G.Adj x y → η.2 y < η.2 x) ∧
            ∀ i : Fin n, (k : ℕ) ≤ i → x ∈ B i →
              ¬ (zAt i ∈ η.1 ∧
                η.2 x < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}
  let targetComplete : ℕ → Ω → Set (Finset V' × (V' → ℝ)) :=
    fun k _ω =>
      {η' |
        ∃ x : V, ∃ hxX : x ∈ X,
          φ x ∈ η'.1 ∧
            (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
              G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
            ∀ i : Fin n, (i : ℕ) < k → x ∈ B i →
              ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ x) <
                    η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                    η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1)}
  let sourceBoundary : ℕ → Ω → Set (Finset V × (V → ℝ)) := leftAdjacentEvent
  let targetBoundary : ℕ → Ω → Set (Finset V' × (V' → ℝ)) := rightAdjacentEvent
  let sourceUnchanged : ℕ → Ω → Set (Finset V × (V → ℝ)) :=
    fun k ω => sourceComplete k ω \ sourceBoundary k ω
  let targetUnchanged : ℕ → Ω → Set (Finset V' × (V' → ℝ)) :=
    fun k ω => targetComplete (k + 1) ω \ targetBoundary k ω
  let sourceNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν (w ω) (cell ω)
      (sourceComplete k ω ∩ cell ω) (hw_nonneg ω) (hw_source ω)
      (by intro η hη; exact hη.2)
  let sourceUnchangedNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν (w ω) (cell ω)
      (sourceUnchanged k ω ∩ cell ω) (hw_nonneg ω) (hw_source ω)
      (by intro η hη; exact hη.2)
  let sourceBoundaryNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν (w ω) (cell ω)
      (sourceBoundary k ω ∩ cell ω) (hw_nonneg ω) (hw_source ω)
      (by intro η hη; exact hη.2)
  let targetNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν' (w ω) (targetCell ω)
      (targetComplete k ω ∩ targetCell ω) (hw_nonneg ω) (hw_target ω)
      (by intro η hη; exact hη.2)
  let targetUnchangedNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν' (w ω) (targetCell ω)
      (targetUnchanged k ω ∩ targetCell ω) (hw_nonneg ω) (hw_target ω)
      (by intro η hη; exact hη.2)
  let targetBoundaryNorm (k : ℕ) (ω : Ω) :=
    SamplingFiniteMassSubcellNormalization ν' (w ω) (targetCell ω)
      (targetBoundary k ω ∩ targetCell ω) (hw_nonneg ω) (hw_target ω)
      (by intro η hη; exact hη.2)
  let sourceMass : ℕ → Ω → ℝ := fun k ω => Classical.choose (sourceNorm k ω)
  let sourceUnchangedMass : ℕ → Ω → ℝ :=
    fun k ω => Classical.choose (sourceUnchangedNorm k ω)
  let sourceBoundaryMass : ℕ → Ω → ℝ :=
    fun k ω => Classical.choose (sourceBoundaryNorm k ω)
  let targetMass : ℕ → Ω → ℝ := fun k ω => Classical.choose (targetNorm k ω)
  let targetUnchangedMass : ℕ → Ω → ℝ :=
    fun k ω => Classical.choose (targetUnchangedNorm k ω)
  let targetBoundaryMass : ℕ → Ω → ℝ :=
    fun k ω => Classical.choose (targetBoundaryNorm k ω)
  have hsourceNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ sourceMass k ω ∧
          (w ω = 0 → sourceMass k ω = 0) ∧
          ENNReal.ofReal (w ω * sourceMass k ω) =
            ν (sourceComplete k ω ∩ cell ω) := by
    intro k ω
    exact Classical.choose_spec (sourceNorm k ω)
  have hsourceUnchangedNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ sourceUnchangedMass k ω ∧
          (w ω = 0 → sourceUnchangedMass k ω = 0) ∧
          ENNReal.ofReal (w ω * sourceUnchangedMass k ω) =
            ν (sourceUnchanged k ω ∩ cell ω) := by
    intro k ω
    exact Classical.choose_spec (sourceUnchangedNorm k ω)
  have hsourceBoundaryNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ sourceBoundaryMass k ω ∧
          (w ω = 0 → sourceBoundaryMass k ω = 0) ∧
          ENNReal.ofReal (w ω * sourceBoundaryMass k ω) =
            ν (sourceBoundary k ω ∩ cell ω) := by
    intro k ω
    exact Classical.choose_spec (sourceBoundaryNorm k ω)
  have htargetNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ targetMass k ω ∧
          (w ω = 0 → targetMass k ω = 0) ∧
          ENNReal.ofReal (w ω * targetMass k ω) =
            ν' (targetComplete k ω ∩ targetCell ω) := by
    intro k ω
    exact Classical.choose_spec (targetNorm k ω)
  have htargetUnchangedNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ targetUnchangedMass k ω ∧
          (w ω = 0 → targetUnchangedMass k ω = 0) ∧
          ENNReal.ofReal (w ω * targetUnchangedMass k ω) =
            ν' (targetUnchanged k ω ∩ targetCell ω) := by
    intro k ω
    exact Classical.choose_spec (targetUnchangedNorm k ω)
  have htargetBoundaryNorm :
      ∀ k : ℕ, ∀ ω : Ω,
        0 ≤ targetBoundaryMass k ω ∧
          (w ω = 0 → targetBoundaryMass k ω = 0) ∧
          ENNReal.ofReal (w ω * targetBoundaryMass k ω) =
            ν' (targetBoundary k ω ∩ targetCell ω) := by
    intro k ω
    exact Classical.choose_spec (targetBoundaryNorm k ω)
  have hsource_cover_inter :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        sourceComplete k ω ∩ cell ω =
          (sourceUnchanged k ω ∩ cell ω) ∪ (sourceBoundary k ω ∩ cell ω) := by
    intro k hk ω
    ext η
    constructor
    · intro hη
      by_cases hb : η ∈ sourceBoundary k ω
      · exact Or.inr ⟨hb, hη.2⟩
      · exact Or.inl ⟨⟨hη.1, hb⟩, hη.2⟩
    · intro hη
      rcases hη with hη | hη
      · exact ⟨hη.1.1, hη.2⟩
      · exact ⟨hsourceBoundary_subset k hk ω hη.1, hη.2⟩
  have htarget_cover_inter :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        targetComplete (k + 1) ω ∩ targetCell ω =
          (targetUnchanged k ω ∩ targetCell ω) ∪
            (targetBoundary k ω ∩ targetCell ω) := by
    intro k hk ω
    ext η
    constructor
    · intro hη
      by_cases hb : η ∈ targetBoundary k ω
      · exact Or.inr ⟨hb, hη.2⟩
      · exact Or.inl ⟨⟨hη.1, hb⟩, hη.2⟩
    · intro hη
      rcases hη with hη | hη
      · exact ⟨hη.1.1, hη.2⟩
      · exact ⟨htargetBoundary_subset k hk ω hη.1, hη.2⟩
  have hsource_cover :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        sourceComplete k ω ∩ cell ω =
          (sourceUnchanged k ω ∪ sourceBoundary k ω) ∩ cell ω := by
    intro k hk ω
    rw [hsource_cover_inter k hk ω]
    ext η
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have htarget_cover :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        targetComplete (k + 1) ω ∩ targetCell ω =
          (targetUnchanged k ω ∪ targetBoundary k ω) ∩ targetCell ω := by
    intro k hk ω
    rw [htarget_cover_inter k hk ω]
    ext η
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  have hsource_disjoint :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        Disjoint (sourceUnchanged k ω ∩ cell ω) (sourceBoundary k ω ∩ cell ω) := by
    intro k hk ω
    rw [Set.disjoint_left]
    intro η hηU hηB
    exact hηU.1.2 hηB.1
  have htarget_disjoint :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        Disjoint (targetUnchanged k ω ∩ targetCell ω)
          (targetBoundary k ω ∩ targetCell ω) := by
    intro k hk ω
    rw [Set.disjoint_left]
    intro η hηU hηB
    exact hηU.1.2 hηB.1
  have hsource_add :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        ν (sourceComplete k ω ∩ cell ω) =
          ν (sourceUnchanged k ω ∩ cell ω) +
            ν (sourceBoundary k ω ∩ cell ω) := by
    intro k hk ω
    rw [hsource_cover_inter k hk ω]
    exact measure_union (hsource_disjoint k hk ω)
      (by simpa [sourceBoundary] using hsourceBoundary_meas k hk ω)
  have htarget_add :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        ν' (targetComplete (k + 1) ω ∩ targetCell ω) =
          ν' (targetUnchanged k ω ∩ targetCell ω) +
            ν' (targetBoundary k ω ∩ targetCell ω) := by
    intro k hk ω
    rw [htarget_cover_inter k hk ω]
    exact measure_union (htarget_disjoint k hk ω)
      (by simpa [targetBoundary] using htargetBoundary_meas k hk ω)
  have hsource_split :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        sourceMass k ω =
          sourceUnchangedMass k ω + sourceBoundaryMass k ω :=
    SamplingSplitOutsideBlockerMixedStageCompleteDecomposition
      (n := n) (w := w) (ν := ν) (cell := cell)
      (complete := sourceComplete) (unchanged := sourceUnchanged)
      (boundary := sourceBoundary) (stageMass := sourceMass)
      (unchangedMass := sourceUnchangedMass) (boundaryMass := sourceBoundaryMass)
      (by intro k hk ω; exact hw_nonneg ω)
      (by intro k hk ω; exact (hsourceNorm k ω).1)
      (by intro k hk ω; exact (hsourceUnchangedNorm k ω).1)
      (by intro k hk ω; exact (hsourceBoundaryNorm k ω).1)
      (by intro k hk ω; exact (hsourceNorm k ω).2.1)
      (by intro k hk ω; exact (hsourceUnchangedNorm k ω).2.1)
      (by intro k hk ω; exact (hsourceBoundaryNorm k ω).2.1)
      hsource_cover_inter hsource_disjoint hsource_add
      (by intro k hk ω; exact (hsourceNorm k ω).2.2)
      (by intro k hk ω; exact (hsourceUnchangedNorm k ω).2.2)
      (by intro k hk ω; exact (hsourceBoundaryNorm k ω).2.2)
  have htarget_split :
      ∀ k : ℕ, k < n → ∀ ω : Ω,
        targetMass (k + 1) ω =
          targetUnchangedMass k ω + targetBoundaryMass k ω :=
    SamplingSplitOutsideBlockerMixedStageCompleteDecomposition
      (n := n) (w := w) (ν := ν') (cell := targetCell)
      (complete := fun k ω => targetComplete (k + 1) ω)
      (unchanged := targetUnchanged) (boundary := targetBoundary)
      (stageMass := fun k ω => targetMass (k + 1) ω)
      (unchangedMass := targetUnchangedMass) (boundaryMass := targetBoundaryMass)
      (by intro k hk ω; exact hw_nonneg ω)
      (by intro k hk ω; exact (htargetNorm (k + 1) ω).1)
      (by intro k hk ω; exact (htargetUnchangedNorm k ω).1)
      (by intro k hk ω; exact (htargetBoundaryNorm k ω).1)
      (by intro k hk ω; exact (htargetNorm (k + 1) ω).2.1)
      (by intro k hk ω; exact (htargetUnchangedNorm k ω).2.1)
      (by intro k hk ω; exact (htargetBoundaryNorm k ω).2.1)
      htarget_cover_inter htarget_disjoint htarget_add
      (by intro k hk ω; exact (htargetNorm (k + 1) ω).2.2)
      (by intro k hk ω; exact (htargetUnchangedNorm k ω).2.2)
      (by intro k hk ω; exact (htargetBoundaryNorm k ω).2.2)
  refine
    ⟨sourceComplete, sourceUnchanged, sourceBoundary,
      targetComplete, targetUnchanged, targetBoundary,
      sourceMass, sourceUnchangedMass, sourceBoundaryMass,
      targetMass, targetUnchangedMass, targetBoundaryMass, ?_⟩
  constructor
  · intro k hk ω
    rfl
  constructor
  · intro k hk ω
    rfl
  constructor
  · intro k hk ω
    rfl
  constructor
  · intro k hk ω
    rfl
  constructor
  · intro k hk ω
    rfl
  constructor
  · intro k hk ω
    rfl
  constructor
  · exact hsource_cover
  constructor
  · exact hsource_disjoint
  constructor
  · exact htarget_cover
  constructor
  · exact htarget_disjoint
  constructor
  · intro k hk ω
    exact ⟨(hsourceNorm k ω).1, (hsourceUnchangedNorm k ω).1,
      (hsourceBoundaryNorm k ω).1, hsource_split k hk ω⟩
  constructor
  · intro k hk ω
    exact ⟨(htargetNorm (k + 1) ω).1, (htargetUnchangedNorm k ω).1,
      (htargetBoundaryNorm k ω).1, htarget_split k hk ω⟩
  constructor
  · exact hsource_add
  constructor
  · exact htarget_add
  constructor
  · intro k hk ω
    exact (hsourceNorm k ω).2.2
  constructor
  · intro k hk ω
    exact (hsourceUnchangedNorm k ω).2.2
  constructor
  · intro k hk ω
    exact (hsourceBoundaryNorm k ω).2.2
  constructor
  · intro k hk ω
    exact (htargetNorm (k + 1) ω).2.2
  constructor
  · intro k hk ω
    exact (htargetUnchangedNorm k ω).2.2
  constructor
  · intro k hk ω
    exact (htargetBoundaryNorm k ω).2.2
  · intro k hk ω hw_zero
    exact ⟨(hsourceNorm k ω).2.1 hw_zero,
      (hsourceUnchangedNorm k ω).2.1 hw_zero,
      (hsourceBoundaryNorm k ω).2.1 hw_zero,
      (htargetNorm (k + 1) ω).2.1 hw_zero,
      (htargetUnchangedNorm k ω).2.1 hw_zero,
      (htargetBoundaryNorm k ω).2.1 hw_zero⟩
