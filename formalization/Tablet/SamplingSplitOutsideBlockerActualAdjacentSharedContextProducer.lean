import Tablet.SamplingSplitOutsideBlockerPairedMixedMeasureSurface
import Tablet.SamplingSplitOutsideBlockerPairedCandidateEvent
import Tablet.SamplingSplitOutsideBlockerPairedCandidateEventMeasurable

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer]
theorem SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
    (w : Ω → ℝ)
    (surface : SamplingSplitOutsideBlockerPairedMixedMeasureSurface
      G G' φ r X n zAt B hOutside β cell targetCell w)
    (k : Fin n) (ω : Ω) :
    letI : MeasurableSpace (Finset V) := ⊤
    letI : MeasurableSpace (Finset V') := ⊤
    let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
      (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
    let U := {ζ | ∃ x : {x : V // x ∈ X}, x.1 ∉ B k ∧ ζ ∈ C x}
    let L := {ζ | ζ ∉ U ∧ ∃ x : {x : V // x ∈ X},
      x.1 ∈ B k ∧ ζ ∈ C x ∧
        ¬ (zAt k ∈ ζ.1.1 ∧ ζ.1.2 x.1 < ζ.1.2 (zAt k) ∧
          ζ.1.2 (zAt k) ∈ Set.Icc (0 : ℝ) 1)}
    let R := {ζ | ζ ∉ U ∧ ∃ x : {x : V // x ∈ X},
      x.1 ∈ B k ∧ ζ ∈ C x ∧
        ∀ hz : zAt k ∉ insert r X ∧ G.Adj x.1 (zAt k),
          ¬ (β ⟨x, ⟨zAt k, hz⟩⟩ ∈ ζ.2.1 ∧
            ζ.2.2 (φ x.1) < ζ.2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∧
            ζ.2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
    surface.mixedStage k ω = U ∪ L ∧
    surface.mixedStage (k.val + 1) ω = U ∪ R ∧
    Disjoint U L ∧ Disjoint U R ∧
    (∀ x, MeasurableSet (C x)) ∧ MeasurableSet U ∧
    MeasurableSet L ∧ MeasurableSet R := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  dsimp only
  let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
    (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
  let sourceTest := fun (x : {x : V // x ∈ X})
      (ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) =>
    ¬ (zAt k ∈ ζ.1.1 ∧ ζ.1.2 x.1 < ζ.1.2 (zAt k) ∧
      ζ.1.2 (zAt k) ∈ Set.Icc (0 : ℝ) 1)
  let targetTest := fun (x : {x : V // x ∈ X})
      (ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) =>
    ∀ hz : zAt k ∉ insert r X ∧ G.Adj x.1 (zAt k),
      ¬ (β ⟨x, ⟨zAt k, hz⟩⟩ ∈ ζ.2.1 ∧
        ζ.2.2 (φ x.1) < ζ.2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∧
        ζ.2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)
  have splitSource (ζ) :
      ζ ∈ surface.mixedStage k ω ↔
        ∃ x : {x : V // x ∈ X}, ζ ∈ C x ∧ (x.1 ∈ B k → sourceTest x ζ) := by
    rw [surface.mixedStage_def k (Nat.le_of_lt k.isLt) ω]
    constructor
    · rintro ⟨x, hx, ha, ha', hc, hc', hp, ht⟩
      refine ⟨⟨x, hx⟩, ⟨ha, ha', hc, hc', ?_, ?_⟩, ?_⟩
      · intro i hi hB hz
        exact hp i (by simpa using (Finset.mem_filter.mp hi).2) hB hz
      · intro i hi hB
        exact ht i (Nat.le_of_lt (by simpa using (Finset.mem_filter.mp hi).2)) hB
      · exact ht k le_rfl
    · rintro ⟨x, ⟨ha, ha', hc, hc', hp, ht⟩, hcurrent⟩
      refine ⟨x.1, x.2, ha, ha', hc, hc', ?_, ?_⟩
      · intro i hi
        exact hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · intro i hi hB
        by_cases heq : i = k
        · subst i
          exact hcurrent hB
        · exact ht i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_le_of_ne hi (fun h => heq h.symm)⟩) hB
  have splitTarget (ζ) :
      ζ ∈ surface.mixedStage (k.val + 1) ω ↔
        ∃ x : {x : V // x ∈ X}, ζ ∈ C x ∧ (x.1 ∈ B k → targetTest x ζ) := by
    rw [surface.mixedStage_def (k.val + 1) (by omega) ω]
    constructor
    · rintro ⟨x, hx, ha, ha', hc, hc', hp, ht⟩
      refine ⟨⟨x, hx⟩, ⟨ha, ha', hc, hc', ?_, ?_⟩, ?_⟩
      · intro i hi hB hz
        exact hp i (by have := (Finset.mem_filter.mp hi).2; exact Nat.lt_succ_of_lt this) hB hz
      · intro i hi hB
        exact ht i (Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2) hB
      · exact hp k (Nat.lt_succ_self _)
    · rintro ⟨x, ⟨ha, ha', hc, hc', hp, ht⟩, hcurrent⟩
      refine ⟨x.1, x.2, ha, ha', hc, hc', ?_, ?_⟩
      · intro i hi hB hz
        by_cases heq : i = k
        · subst i
          exact hcurrent hB hz
        · exact hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_le_of_ne (Nat.le_of_lt_succ hi) heq⟩) hB hz
      · intro i hi
        exact ht i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_succ_le hi⟩)
  have algebra (T : {x : V // x ∈ X} →
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) → Prop) (ζ) :
      (∃ x, ζ ∈ C x ∧ (x.1 ∈ B k → T x ζ)) ↔
      (∃ x, x.1 ∉ B k ∧ ζ ∈ C x) ∨
        (¬ (∃ x, x.1 ∉ B k ∧ ζ ∈ C x) ∧
          ∃ x, x.1 ∈ B k ∧ ζ ∈ C x ∧ T x ζ) := by
    constructor
    · rintro ⟨x, hx, ht⟩
      by_cases hU : ∃ x, x.1 ∉ B k ∧ ζ ∈ C x
      · exact Or.inl hU
      · right
        have hB : x.1 ∈ B k := by
          by_contra h
          exact hU ⟨x, h, hx⟩
        exact ⟨hU, x, hB, hx, ht hB⟩
    · rintro (⟨x, hB, hx⟩ | ⟨_, x, hB, hx, ht⟩)
      · exact ⟨x, hx, fun h => (hB h).elim⟩
      · exact ⟨x, hx, fun _ => ht⟩
  have hC (x) : MeasurableSet (C x) :=
    SamplingSplitOutsideBlockerPairedCandidateEventMeasurable G φ r X zAt B β _ _ x
  have hU : MeasurableSet {ζ | ∃ x, x.1 ∉ B k ∧ ζ ∈ C x} :=
    (Measurable.exists fun x => measurable_const.and (hC x).mem).setOf
  have hstage (j : ℕ) (hj : j ≤ n) : MeasurableSet (surface.mixedStage j ω) := by
    rw [surface.mixedStage_def j hj ω]
    have hm := MeasurableSet.iUnion (fun x : {x : V // x ∈ X} =>
      SamplingSplitOutsideBlockerPairedCandidateEventMeasurable G φ r X zAt B β
        (Finset.univ.filter (fun i => i.val < j))
        (Finset.univ.filter (fun i => j ≤ i.val)) x)
    convert hm using 1
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion,
      SamplingSplitOutsideBlockerPairedCandidateEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, Subtype.exists]
  refine ⟨?_, ?_, ?_, ?_, hC, hU, ?_, ?_⟩
  · ext ζ
    exact (splitSource ζ).trans (algebra sourceTest ζ)
  · ext ζ
    exact (splitTarget ζ).trans (algebra targetTest ζ)
  · exact Set.disjoint_left.mpr (fun ζ hU hL => hL.1 hU)
  · exact Set.disjoint_left.mpr (fun ζ hU hR => hR.1 hU)
  · convert (hstage k (Nat.le_of_lt k.isLt)).diff hU using 1
    ext ζ
    rw [Set.mem_diff, splitSource ζ, algebra sourceTest ζ]
    change (¬ (∃ x, x.1 ∉ B k ∧ ζ ∈ C x) ∧
      ∃ x, x.1 ∈ B k ∧ ζ ∈ C x ∧ sourceTest x ζ) ↔ _
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => ⟨Or.inr h, h.1⟩, fun h => h.1.resolve_left h.2⟩
  · convert (hstage (k.val + 1) (by omega)).diff hU using 1
    ext ζ
    rw [Set.mem_diff, splitTarget ζ, algebra targetTest ζ]
    change (¬ (∃ x, x.1 ∉ B k ∧ ζ ∈ C x) ∧
      ∃ x, x.1 ∈ B k ∧ ζ ∈ C x ∧ targetTest x ζ) ↔ _
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => ⟨Or.inr h, h.1⟩, fun h => h.1.resolve_left h.2⟩
