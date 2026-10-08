import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingData
import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface
import Tablet.SamplingSplitOutsideBlockerEndpointBoundaryCellReduction
import Tablet.SamplingSplitOutsideBlockerSourceDisplayedEndpointMeasurable

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualSourceEndpointFromCoupling]
theorem SamplingSplitOutsideBlockerActualSourceEndpointFromCoupling :
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
            (sourceCoord : Finset V) (targetCommonCoord : Finset V')
            (cell : Ω → Set (Finset V × (V → ℝ)))
            (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
            (w : Ω → ℝ)
            (p : ℝ)
            (coupling :
              SamplingSplitOutsideBlockerMarginalPreservingCouplingData
                ν ν' φ sourceCoord targetCommonCoord cell targetCell w)
            (surface :
              SamplingSplitOutsideBlockerPairedMixedMeasureSurface
                G G' φ r X n zAt B hOutside β cell targetCell w),
            Function.Injective φ →
            (∀ z : V, z ∉ insert r X →
              (∃ x : V, x ∈ X ∧ G.Adj x z) →
                ∃ k : Fin n, zAt k = z) →
            surface.pairedMeasure = coupling.pairedMeasure →
            surface.pairedCell = coupling.pairedCell →
            0 ≤ p →
            p ≤ 1 →
            (∀ A : Finset V,
              ν {ω | ω.1 = A} =
                ENNReal.ofReal
                  (p ^ A.card *
                    (1 - p) ^ ((Finset.univ : Finset V).card - A.card))) →
            (∀ A : Finset V, ∀ t : V → ℝ,
              (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                ν {ω |
                  ω.1 = A ∧
                    ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                  ν {ω | ω.1 = A} *
                    ENNReal.ofReal (∏ v : V, t v)) →
            @MeasurableSet (Finset V × (V → ℝ))
              (MeasurableSpace.prod ⊤ inferInstance)
              {η : Finset V × (V → ℝ) |
                ((Finset.univ.filter fun z : V =>
                  z ∈ η.1 ∧
                    ∀ y : V, y ∈ η.1 → G.Adj z y →
                      η.2 y < η.2 z) ∩ X).Nonempty} →
            ∀ ω : Ω,
              ENNReal.ofReal (w ω * surface.mixedMass 0 ω) =
                ν ({η : Finset V × (V → ℝ) |
                  ((Finset.univ.filter fun z : V =>
                    z ∈ η.1 ∧
                      ∀ y : V, y ∈ η.1 → G.Adj z y →
                        η.2 y < η.2 z) ∩ X).Nonempty} ∩ cell ω) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ G' _ ν ν' φ r X n zAt B hOutside β
    sourceCoord targetCommonCoord cell targetCell w p coupling surface
    hφ hcover hmeasure hcell hp0 hp1 hatom hrect _ ω
  let D : Set (Finset V × (V → ℝ)) :=
    {η | ∃ x : V, x ∈ X ∧ x ∈ η.1 ∧
      (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
      (∀ i : Fin n, x ∈ B i →
        ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
          η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}
  have hD := SamplingSplitOutsideBlockerSourceDisplayedEndpointMeasurable G r X zAt B
  have hprojection : surface.mixedStage 0 ω ∩ surface.pairedCell ω =
      {ζ | ζ.1 ∈ D} ∩ surface.pairedCell ω := by
    rw [surface.mixedStage_def 0 (Nat.zero_le n) ω]
    ext ζ
    constructor
    · rintro ⟨⟨x, hx, ha, _, hl, _, _, hb⟩, hc⟩
      exact ⟨⟨x, hx, ha, hl, fun i hi => hb i (Nat.zero_le _) hi⟩, hc⟩
    · rintro ⟨⟨x, hx, ha, hl, hb⟩, hc⟩
      have hact (v : V) (hv : v ∈ insert r X) :
          φ v ∈ ζ.2.1 ↔ v ∈ ζ.1.1 := by
        have hvs := surface.sourceCoord_contains_embedded v hv
        have hvt : φ v ∈ surface.targetCommonCoord := by
          rw [surface.targetCommonCoord_eq]
          exact Finset.mem_image.mpr ⟨v, hvs, rfl⟩
        have ht := surface.paired_common_trace ω ζ hc
        constructor
        · intro ha'
          have hm : φ v ∈ (ζ.1.1 ∩ surface.sourceCoord).image φ := by
            rw [← ht]
            exact Finset.mem_inter.mpr ⟨ha', hvt⟩
          obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
          have heq := hφ he
          subst a
          exact (Finset.mem_inter.mp ha).1
        · intro ha'
          have hm : φ v ∈ ζ.2.1 ∩ surface.targetCommonCoord := by
            rw [ht]
            exact Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨ha', hvs⟩, rfl⟩
          exact (Finset.mem_inter.mp hm).1
      have hxlocal : x ∈ insert r X := Finset.mem_insert_of_mem hx
      refine ⟨⟨x, hx, ha, (hact x hxlocal).mpr ha, hl, ?_, ?_, ?_⟩, hc⟩
      · intro y hy hya hadj
        rw [surface.paired_common_priorities ω ζ hc y
          (surface.sourceCoord_contains_embedded y hy),
          surface.paired_common_priorities ω ζ hc x
            (surface.sourceCoord_contains_embedded x hxlocal)]
        exact hl y hy ((hact y hy).mp hya) hadj
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
      · intro i _ hi
        exact hb i hi
  have hboundary := SamplingSplitOutsideBlockerEndpointBoundaryCellReduction
    G ν p (Finset.univ : Finset {x : V // x ∈ X}) Subtype.val
    (insert r X) (fun i _ => zAt i) (fun i x => x.1 ∈ B i) (cell ω)
    hp0 hp1 hatom hrect
    (by
      intro x _ y hadj
      by_cases hy : y ∈ insert r X
      · exact Or.inl hy
      · obtain ⟨i, hi⟩ := hcover y hy ⟨x.1, x.2, hadj⟩
        exact Or.inr ⟨i, (surface.candidate_sets i x.1).mpr
          ⟨x.2, hi.symm ▸ hadj⟩, hi.symm⟩)
    (by
      intro i x _ hi
      exact ((surface.candidate_sets i x.1).mp hi).2)
    (by
      intro x _
      exact Finset.mem_insert_of_mem x.2)
  have himage : (Finset.univ : Finset {x : V // x ∈ X}).image
      (Subtype.val : {x : V // x ∈ X} → V) = X := by
    ext x
    simp
  have hdisplay :
      {η : Finset V × (V → ℝ) |
        ∃ x : {x : V // x ∈ X}, ∃ _ : x ∈ (Finset.univ : Finset {x : V // x ∈ X}),
          x.1 ∈ η.1 ∧
            (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x.1 y → η.2 y < η.2 x.1) ∧
            ∀ i : Fin n, x.1 ∈ B i →
              ¬ (zAt i ∈ η.1 ∧ η.2 x.1 < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} = D := by
    ext η
    simp only [Finset.mem_univ, exists_const, Subtype.exists, D, Set.mem_setOf_eq,
      exists_prop]
  rw [himage, hdisplay] at hboundary
  rw [surface.mixedMass_measures_stage 0 (Nat.zero_le n) ω, hprojection,
    hmeasure, hcell, coupling.source_restricted_marginal ω D hD]
  exact hboundary.symm
