import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingData
import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface
import Tablet.SamplingSplitOutsideBlockerEndpointBoundaryCellReduction
import Tablet.SamplingSplitOutsideBlockerTargetDisplayedEndpointMeasurable

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualTargetEndpointFromCoupling]
theorem SamplingSplitOutsideBlockerActualTargetEndpointFromCoupling :
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
            (∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
              (G.Adj a b ↔ G'.Adj (φ a) (φ b))) →
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
            (∀ z : V, z ∉ insert r X →
              (∃ x : V, x ∈ X ∧ G.Adj x z) →
                ∃ k : Fin n, zAt k = z) →
            surface.pairedMeasure = coupling.pairedMeasure →
            surface.pairedCell = coupling.pairedCell →
            0 ≤ p →
            p ≤ 1 →
            (∀ A : Finset V',
              ν' {ω | ω.1 = A} =
                ENNReal.ofReal
                  (p ^ A.card *
                    (1 - p) ^ ((Finset.univ : Finset V').card - A.card))) →
            (∀ A : Finset V', ∀ t : V' → ℝ,
              (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
                ν' {ω |
                  ω.1 = A ∧
                    ∀ v' : V', 0 ≤ ω.2 v' ∧ ω.2 v' ≤ t v'} =
                  ν' {ω | ω.1 = A} *
                    ENNReal.ofReal (∏ v' : V', t v')) →
            @MeasurableSet (Finset V' × (V' → ℝ))
              (MeasurableSpace.prod ⊤ inferInstance)
              {η : Finset V' × (V' → ℝ) |
                ((Finset.univ.filter fun z : V' =>
                  z ∈ η.1 ∧
                    ∀ y : V', y ∈ η.1 → G'.Adj z y →
                      η.2 y < η.2 z) ∩ X.image φ).Nonempty} →
            ∀ ω : Ω,
              ENNReal.ofReal (w ω * surface.mixedMass n ω) =
                ν' ({η : Finset V' × (V' → ℝ) |
                  ((Finset.univ.filter fun z : V' =>
                    z ∈ η.1 ∧
                      ∀ y : V', y ∈ η.1 → G'.Adj z y →
                        η.2 y < η.2 z) ∩ X.image φ).Nonempty} ∩
                  targetCell ω) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ G' _ ν ν' φ r X n zAt B hOutside β
    sourceCoord targetCommonCoord cell targetCell w p coupling surface
    hφ hadj hprivate _ _ hexhaust hcover hmeasure hcell hp0 hp1 hatom hrect _ ω
  let D : Set (Finset V' × (V' → ℝ)) :=
    {η | ∃ x : V, ∃ hx : x ∈ X, φ x ∈ η.1 ∧
      (∀ y : V, y ∈ insert r X → φ y ∈ η.1 →
        G.Adj x y → η.2 (φ y) < η.2 (φ x)) ∧
      (∀ i : Fin n, x ∈ B i →
        ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
          ¬ (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩ ∈ η.1 ∧
            η.2 (φ x) < η.2 (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩) ∧
            η.2 (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1))}
  have hD := SamplingSplitOutsideBlockerTargetDisplayedEndpointMeasurable G φ r X zAt B β
  have hprojection : surface.mixedStage n ω ∩ surface.pairedCell ω =
      {ζ | ζ.2 ∈ D} ∩ surface.pairedCell ω := by
    rw [surface.mixedStage_def n le_rfl ω]
    ext ζ
    constructor
    · rintro ⟨⟨x, hx, _, ha, _, hl, hb, _⟩, hc⟩
      exact ⟨⟨x, hx, ha, hl, fun i hi => hb i i.isLt hi⟩, hc⟩
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
      refine ⟨⟨x, hx, (hact x hxlocal).mp ha, ha, ?_, hl, ?_, ?_⟩, hc⟩
      · intro y hy hya hxy
        rw [← surface.paired_common_priorities ω ζ hc y
          (surface.sourceCoord_contains_embedded y hy),
          ← surface.paired_common_priorities ω ζ hc x
            (surface.sourceCoord_contains_embedded x hxlocal)]
        exact hl y hy ((hact y hy).mpr hya) hxy
      · intro i _ hi
        exact hb i hi
      · intro i hi
        exact (Nat.not_le_of_lt i.isLt hi).elim
  let blocker (i : Fin n) (x : {x : V // x ∈ X}) : V' :=
    if hi : x.1 ∈ B i then
      β ⟨x, ⟨zAt i, hOutside i, ((surface.candidate_sets i x.1).mp hi).2⟩⟩
    else φ x.1
  have hb (i : Fin n) (x : {x : V // x ∈ X}) (hi : x.1 ∈ B i)
      (hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i)) :
      blocker i x = β ⟨x, ⟨zAt i, hz⟩⟩ := by
    simp only [blocker, dif_pos hi]
  have hboundary := SamplingSplitOutsideBlockerEndpointBoundaryCellReduction
    G' ν' p (Finset.univ : Finset {x : V // x ∈ X}) (fun x => φ x.1)
    ((insert r X).image φ) blocker (fun i x => x.1 ∈ B i) (targetCell ω)
    hp0 hp1 hatom hrect
    (by
      intro x _ y hxy
      rcases hexhaust x.1 x.2 y hxy with ⟨v, hv, rfl, _⟩ | ⟨z, hz, rfl⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      · obtain ⟨i, hi⟩ := hcover z hz.1 ⟨x.1, x.2, hz.2⟩
        subst z
        have hxi := (surface.candidate_sets i x.1).mpr ⟨x.2, hz.2⟩
        exact Or.inr ⟨i, hxi, (hb i x hxi hz).symm⟩)
    (by
      intro i x _ hi
      have hz := And.intro (hOutside i) ((surface.candidate_sets i x.1).mp hi).2
      rw [hb i x hi hz]
      exact hprivate x.1 x.2 (zAt i) hz)
    (by
      intro x _
      exact Finset.mem_image.mpr ⟨x.1, Finset.mem_insert_of_mem x.2, rfl⟩)
  have himage : (Finset.univ : Finset {x : V // x ∈ X}).image
      (fun x => φ x.1) = X.image φ := by
    ext y
    simp
  have hdisplay :
      {η : Finset V' × (V' → ℝ) |
        ∃ x : {x : V // x ∈ X}, ∃ _ : x ∈ (Finset.univ : Finset {x : V // x ∈ X}),
          φ x.1 ∈ η.1 ∧
            (∀ y : V', y ∈ (insert r X).image φ → y ∈ η.1 →
              G'.Adj (φ x.1) y → η.2 y < η.2 (φ x.1)) ∧
            ∀ i : Fin n, x.1 ∈ B i →
              ¬ (blocker i x ∈ η.1 ∧ η.2 (φ x.1) < η.2 (blocker i x) ∧
                η.2 (blocker i x) ∈ Set.Icc (0 : ℝ) 1)} = D := by
    ext η
    have hlocal (y : V) (hy : y ∈ insert r X) : y ∈ X ∨ y = r := by
      rcases Finset.mem_insert.mp hy with h | h
      · exact Or.inr h
      · exact Or.inl h
    constructor
    · rintro ⟨x, _, ha, hl, ht⟩
      refine ⟨x.1, x.2, ha, ?_, ?_⟩
      · intro y hy hya hxy
        exact hl (φ y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hya
          ((hadj x.1 y (Or.inl x.2) (hlocal y hy)).mp hxy)
      · intro i hi hz
        simpa only [hb i x hi hz] using ht i hi
    · rintro ⟨x, hx, ha, hl, ht⟩
      refine ⟨⟨x, hx⟩, Finset.mem_univ _, ha, ?_, ?_⟩
      · intro y hy hya hxy
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        exact hl v hv hya ((hadj x v (Or.inl hx) (hlocal v hv)).mpr hxy)
      · intro i hi
        have hz := And.intro (hOutside i) ((surface.candidate_sets i x).mp hi).2
        simpa only [hb i ⟨x, hx⟩ hi hz] using ht i hi hz
  rw [himage, hdisplay] at hboundary
  rw [surface.mixedMass_measures_stage n le_rfl ω, hprojection,
    hmeasure, hcell, coupling.target_restricted_marginal ω D hD]
  exact hboundary.symm
