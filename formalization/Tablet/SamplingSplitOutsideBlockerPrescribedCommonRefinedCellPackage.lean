import Tablet.SamplingSplitOutsideBlockerActualCoordinatePackage
import Tablet.SamplingSplitOutsideBlockerPrescribedCommonAtomMassSupport
import Tablet.SamplingSplitOutsideBlockerMeasuredStageCellRefinement

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage]
theorem SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage :
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
                      ENNReal.ofReal (∏ v' : V', t v')) →
              ∀ (φ : V → V') (r : V) (X : Finset V),
                Function.Injective φ →
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
                  ∀ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (sourceCoord sourceExtensionCoord : Finset V)
                    (targetCommonCoord targetExtensionCoord targetCoord : Finset V'),
                    Function.Injective zAt →
                    (∀ k : Fin n,
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
                    ∃ (Ω : Type u) (_ : Fintype Ω)
                      (cell : Ω → Set (Finset V × (V → ℝ)))
                      (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                      (w : Ω → ℝ),
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
                        {η |
                          ((Finset.univ.filter fun z : V =>
                            z ∈ η.1 ∧
                              ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                              X).Nonempty} ∧
                      @MeasurableSet (Finset V' × (V' → ℝ))
                        (MeasurableSpace.prod ⊤ inferInstance)
                        {η |
                          ((Finset.univ.filter fun z : V' =>
                            z ∈ η.1 ∧
                              ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                              X.image φ).Nonempty} := by
-- BODY
  classical
  intro V V' _ _ _ _ G _ G' _ Delta gamma ν ν' hp hp1 ha hr ha' hr'
    φ r X hφ β hβ hfresh hadj n zAt B S E S' E' T' hz hin hout hB
    hzE hSE hXS hS' hSE' hT' hXS' hβE
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  have endpoint {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (Y : Finset W) :
      @MeasurableSet (Finset W × (W → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
        {η | ((Finset.univ.filter fun z : W => z ∈ η.1 ∧
          ∀ y : W, y ∈ η.1 → H.Adj z y → η.2 y < η.2 z) ∩ Y).Nonempty} := by
    letI : MeasurableSpace (Finset W) := ⊤
    simp only [Finset.nonempty_def, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro z
    have hact (y : W) : MeasurableSet {η : Finset W × (W → ℝ) | y ∈ η.1} :=
      measurable_fst (show MeasurableSet {A : Finset W | y ∈ A} from trivial)
    have hneigh : MeasurableSet {η : Finset W × (W → ℝ) |
        ∀ y : W, y ∈ η.1 → H.Adj z y → η.2 y < η.2 z} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun y => (hact y).imp
        ((MeasurableSet.const (H.Adj z y)).imp
          (measurableSet_lt ((measurable_pi_apply y).comp measurable_snd)
            ((measurable_pi_apply z).comp measurable_snd)))
    exact ((hact z).inter hneigh).inter (MeasurableSet.const (z ∈ Y))
  obtain ⟨hbase, hbase', hlabel, hlabel', hdis, hdis', htrans, hltrans,
    hmass, hcover, hcover', hnull, hnull'⟩ :=
    SamplingSplitOutsideBlockerPrescribedCommonAtomMassSupport S S' φ hφ hS'
      Delta gamma ν ν' hp hp1 ha hr ha' hr'
  obtain ⟨Ω, instΩ, baseOf, truth, cell, targetCell, w, hcell, hcell',
    hfiber, hfiber', hd, hd', hl, hl', ht, hw, hm, hm', hsum, hsum'⟩ :=
    SamplingSplitOutsideBlockerMeasuredStageCellRefinement ν ν' _ _ _ _ _
      hbase hbase' hlabel hlabel' hdis hdis' htrans hltrans hmass
  refine ⟨Ω, instΩ, cell, targetCell, w, hw, hm, hm', hd, hd', ?_, ?_,
    hnull, hnull', ?_, ?_, ?_, ?_, ?_⟩
  · intro η hη
    obtain ⟨A, hA⟩ := hcover η hη
    obtain ⟨ω, _, hω⟩ := hfiber A η hA
    exact ⟨ω, hω⟩
  · intro η hη
    obtain ⟨A, hA⟩ := hcover' η hη
    obtain ⟨ω, _, hω⟩ := hfiber' A η hA
    exact ⟨ω, hω⟩
  · intro ω η η' hact hprio
    exact ht ω η η' ⟨hact, hprio⟩
  · intro ω
    rw [hcell ω, Set.setOf_forall]
    exact (hbase _).inter (MeasurableSet.iInter fun ℓ =>
      (hlabel ℓ).iff (MeasurableSet.const _))
  · intro ω
    rw [hcell' ω, Set.setOf_forall]
    exact (hbase' _).inter (MeasurableSet.iInter fun ℓ =>
      (hlabel' ℓ).iff (MeasurableSet.const _))
  · exact endpoint G X
  · exact endpoint G' (X.image φ)
