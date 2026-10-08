import Tablet.SamplingFinitePriorityCutProductFormula
import Mathlib.MeasureTheory.Measure.AEDisjoint

open BigOperators

set_option maxHeartbeats 1000000

-- [TABLET NODE: SamplingFiniteCoordinateMarginalCellLaw]
theorem SamplingFiniteCoordinateMarginalCellLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (C A0 L U : Finset V) (t : V → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA0 : A0 ⊆ C)
    (hL : L ⊆ C) (hU : U ⊆ C)
    (hLU : Disjoint L U)
    (ht0 : ∀ v : V, v ∈ L ∪ U → 0 ≤ t v)
    (ht1 : ∀ v : V, v ∈ L ∪ U → t v ≤ 1)
    (hν_atom : ∀ A : Finset V,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)))
    (hν_rect : ∀ A : Finset V, ∀ s : V → ℝ,
      (∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v : V, s v)) :
    ∃ w : ℝ, 0 ≤ w ∧
      ENNReal.ofReal w =
        ν {ω |
          ω.1 ∩ C = A0 ∧
            (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
              ∀ v : V, v ∈ U → t v < ω.2 v} ∧
      w =
        (p ^ A0.card * (1 - p) ^ (C.card - A0.card)) *
          (∏ v : V, if v ∈ L then t v else 1) *
            (∏ v : V, if v ∈ U then (1 - t v) else 1) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let S : Finset (Finset V) :=
    Finset.univ.filter fun A : Finset V => A ∩ C = A0
  let cuts : Set (Finset V × (V → ℝ)) :=
    {ω |
      (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
        ∀ v : V, v ∈ U → t v < ω.2 v}
  let cell : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 ∩ C = A0 ∧
        (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
          ∀ v : V, v ∈ U → t v < ω.2 v}
  let atomCell (A : Finset V) : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
          ∀ v : V, v ∈ U → t v < ω.2 v}
  let cubeAtomCell (A : Finset V) : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
          (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
            ∀ v : V, v ∈ U → t v < ω.2 v}
  let weight (A : Finset V) : ℝ :=
    p ^ A.card *
      (1 - p) ^ ((Finset.univ : Finset V).card - A.card) *
        (∏ v : V, if v ∈ L then t v else 1) *
          (∏ v : V, if v ∈ U then (1 - t v) else 1)
  have hcut_nonneg_L : 0 ≤ ∏ v : V, if v ∈ L then t v else 1 := by
    refine Finset.prod_nonneg ?_
    intro v hv
    by_cases hvL : v ∈ L
    · exact by
        simpa [hvL] using ht0 v (by simp [hvL])
    · simp [hvL]
  have hcut_nonneg_U : 0 ≤ ∏ v : V, if v ∈ U then (1 - t v) else 1 := by
    refine Finset.prod_nonneg ?_
    intro v hv
    by_cases hvU : v ∈ U
    · exact by
        simpa [hvU] using sub_nonneg.mpr (ht1 v (by simp [hvU]))
    · simp [hvU]
  have hweight_nonneg : ∀ A : Finset V, 0 ≤ weight A := by
    intro A
    dsimp [weight]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hp0 A.card)
          (pow_nonneg (sub_nonneg.mpr hp1)
            ((Finset.univ : Finset V).card - A.card)))
        hcut_nonneg_L)
      hcut_nonneg_U
  have hcube_full : ∀ A : Finset V,
      ν ({ω : Finset V × (V → ℝ) |
          ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1}) =
        ν {ω : Finset V × (V → ℝ) | ω.1 = A} := by
    intro A
    have hrect := hν_rect A (fun _ : V => (1 : ℝ)) (by intro v; simp)
    simpa using hrect
  have hatomCell_eq_cube : ∀ A : Finset V,
      ν (atomCell A) = ν (cubeAtomCell A) := by
    intro A
    let atom : Set (Finset V × (V → ℝ)) := {ω | ω.1 = A}
    let cubeAtom : Set (Finset V × (V → ℝ)) :=
      {ω | ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1}
    have hcube_subset_atom : cubeAtom ⊆ atom := by
      intro ω hω
      exact hω.1
    have hcube_mble : MeasureTheory.NullMeasurableSet cubeAtom ν := by
      exact (by
        dsimp [cubeAtom]
        measurability : MeasurableSet cubeAtom).nullMeasurableSet
    have hcube_ne_top : ν cubeAtom ≠ ⊤ := by
      rw [hcube_full A]
      rw [hν_atom A]
      exact ENNReal.ofReal_ne_top
    have hdiff_zero : ν (atom \ cubeAtom) = 0 := by
      rw [MeasureTheory.measure_diff hcube_subset_atom hcube_mble hcube_ne_top]
      rw [hcube_full A]
      rw [hν_atom A]
      simp
    have hcubeCell_subset_atomCell : cubeAtomCell A ⊆ atomCell A := by
      intro ω hω
      exact ⟨hω.1, hω.2.2.1, hω.2.2.2⟩
    have hatomCell_subset_atom : atomCell A ⊆ atom := by
      intro ω hω
      exact hω.1
    have hdiff_subset : atomCell A \ cubeAtomCell A ⊆ atom \ cubeAtom := by
      intro ω hω
      refine ⟨hatomCell_subset_atom hω.1, ?_⟩
      intro hωcube
      exact hω.2 ⟨hω.1.1, hωcube.2, hω.1.2.1, hω.1.2.2⟩
    have hdiff_cell_zero : ν (atomCell A \ cubeAtomCell A) = 0 :=
      le_antisymm ((ν.mono hdiff_subset).trans_eq hdiff_zero) bot_le
    exact (MeasureTheory.measure_eq_measure_of_null_diff
      hcubeCell_subset_atomCell hdiff_cell_zero).symm
  have hatom_measure : ∀ A : Finset V,
      ν (atomCell A) = ENNReal.ofReal (weight A) := by
    intro A
    rw [hatomCell_eq_cube A]
    change
      ν {ω |
          ω.1 = A ∧
            (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
              (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                ∀ v : V, v ∈ U → t v < ω.2 v} =
        ENNReal.ofReal (weight A)
    rw [SamplingFinitePriorityCutProductFormula ν p A L U t hp0 hp1 hLU ht0 ht1 hν_atom hν_rect]
  have hcell_union :
      cell = ⋃ A ∈ S, atomCell A := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.mpr ⟨ω.1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · simp [S, hω.1]
      · exact ⟨rfl, hω.2.1, hω.2.2⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨A, hAω⟩
      rcases Set.mem_iUnion.mp hAω with ⟨hAS, hωA⟩
      have hAinter : A ∩ C = A0 := by
        simpa [S] using hAS
      exact ⟨by simpa [hωA.1] using hAinter, hωA.2.1, hωA.2.2⟩
  have hpairwise :
      Set.Pairwise (↑S) (Function.onFun (MeasureTheory.AEDisjoint ν) atomCell) := by
    intro A hAS B hBS hAB
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro ω hωA hωB
    exact hAB (hωA.1.symm.trans hωB.1)
  have hm_atomCell : ∀ A ∈ S, MeasureTheory.NullMeasurableSet (atomCell A) ν := by
    intro A hA
    exact (by
      dsimp [atomCell]
      measurability : MeasurableSet (atomCell A)).nullMeasurableSet
  have hmeasure_cell :
      ν cell = ∑ A ∈ S, ENNReal.ofReal (weight A) := by
    rw [hcell_union]
    rw [MeasureTheory.measure_biUnion_finset₀ hpairwise hm_atomCell]
    simp_rw [hatom_measure]
  let cutWeight : ℝ :=
    (∏ v : V, if v ∈ L then t v else 1) *
      (∏ v : V, if v ∈ U then (1 - t v) else 1)
  have hweight_eq : ∀ A : Finset V,
      weight A =
        (p ^ A.card *
          (1 - p) ^ ((Finset.univ : Finset V).card - A.card)) *
          cutWeight := by
    intro A
    simp [weight, cutWeight, mul_assoc]
  have hsum_weight :
      ∑ A ∈ S, weight A =
        (p ^ A0.card * (1 - p) ^ (C.card - A0.card)) * cutWeight := by
    have hS_eq :
        S = (Cᶜ.powerset.image fun R : Finset V => A0 ∪ R) := by
      ext A
      constructor
      · intro hA
        have hAinter : A ∩ C = A0 := by
          simpa [S] using hA
        have hA0subA : A0 ⊆ A := by
          intro v hv
          have hmemInter : v ∈ A ∩ C := by simpa [hAinter] using hv
          exact (Finset.mem_inter.mp hmemInter).1
        refine Finset.mem_image.mpr ⟨A \ C, ?_, ?_⟩
        · exact Finset.mem_powerset.mpr (by intro v hv; simp at hv ⊢; exact hv.2)
        · ext v
          by_cases hvC : v ∈ C
          · constructor
            · intro hv
              rcases Finset.mem_union.mp hv with hvA0 | hvDiff
              · exact hA0subA hvA0
              · exact (Finset.mem_sdiff.mp hvDiff).1
            · intro hv
              exact Finset.mem_union.mpr (Or.inl (by
                have hmemInter : v ∈ A ∩ C :=
                  Finset.mem_inter.mpr ⟨hv, hvC⟩
                simpa [hAinter] using hmemInter))
          · constructor
            · intro hv
              rcases Finset.mem_union.mp hv with hvA0 | hvDiff
              · exfalso
                exact hvC (hA0 hvA0)
              · exact (Finset.mem_sdiff.mp hvDiff).1
            · intro hv
              exact Finset.mem_union.mpr
                (Or.inr (Finset.mem_sdiff.mpr ⟨hv, hvC⟩))
      · intro hA
        rcases Finset.mem_image.mp hA with ⟨R, hRpow, rfl⟩
        have hRsub : R ⊆ Cᶜ := Finset.mem_powerset.mp hRpow
        have hRdisjC : Disjoint R C := by
          rw [Finset.disjoint_left]
          intro v hvR hvC
          have : v ∈ Cᶜ := hRsub hvR
          have hvnotC : v ∉ C := by
            simpa using this
          exact hvnotC hvC
        have hA0R_inter : (A0 ∪ R) ∩ C = A0 := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_inter.mp hv with ⟨hvA0R, hvC⟩
            rcases Finset.mem_union.mp hvA0R with hvA0 | hvR
            · exact hvA0
            · exfalso
              exact (Finset.disjoint_left.mp hRdisjC hvR) hvC
          · intro hvA0
            exact Finset.mem_inter.mpr
              ⟨Finset.mem_union.mpr (Or.inl hvA0), hA0 hvA0⟩
        simp [S, hA0R_inter]
    have himage_inj : Set.InjOn (fun R : Finset V => A0 ∪ R) (↑Cᶜ.powerset) := by
      intro R hR T hT hRT
      have hRsub : R ⊆ Cᶜ := Finset.mem_powerset.mp hR
      have hTsub : T ⊆ Cᶜ := Finset.mem_powerset.mp hT
      ext v
      constructor
      · intro hvR
        have hvUnion : v ∈ A0 ∪ T := by
          simpa [hRT] using (Finset.mem_union.mpr (Or.inr hvR) : v ∈ A0 ∪ R)
        rcases Finset.mem_union.mp hvUnion with hvA0 | hvT
        · exfalso
          have hvC : v ∈ C := hA0 hvA0
          have hvnotC : v ∉ C := by simpa using hRsub hvR
          exact hvnotC hvC
        · exact hvT
      · intro hvT
        have hvUnion : v ∈ A0 ∪ R := by
          simpa [hRT] using (Finset.mem_union.mpr (Or.inr hvT) : v ∈ A0 ∪ T)
        rcases Finset.mem_union.mp hvUnion with hvA0 | hvR
        · exfalso
          have hvC : v ∈ C := hA0 hvA0
          have hvnotC : v ∉ C := by simpa using hTsub hvT
          exact hvnotC hvC
        · exact hvR
    rw [hS_eq]
    rw [Finset.sum_image]
    · simp_rw [hweight_eq]
      rw [← Finset.sum_mul]
      congr 1
      have hterm : ∀ R ∈ Cᶜ.powerset,
            p ^ (A0 ∪ R).card *
                (1 - p) ^ ((Finset.univ : Finset V).card - (A0 ∪ R).card) =
              p ^ A0.card * (1 - p) ^ (C.card - A0.card) *
                (p ^ R.card * (1 - p) ^ (Cᶜ.card - R.card)) := by
        intro R hR
        have hRsub : R ⊆ Cᶜ := Finset.mem_powerset.mp hR
        have hdisj : Disjoint A0 R := by
          rw [Finset.disjoint_left]
          intro v hvA0 hvR
          have hvC : v ∈ C := hA0 hvA0
          have hvnotC : v ∉ C := by simpa using hRsub hvR
          exact hvnotC hvC
        have hcard_union : (A0 ∪ R).card = A0.card + R.card := by
          exact Finset.card_union_of_disjoint hdisj
        have hC_card : C.card = A0.card + (C \ A0).card := by
          rw [add_comm, Finset.card_sdiff_add_card_eq_card hA0]
        have huniv_card : (Finset.univ : Finset V).card = C.card + Cᶜ.card := by
          rw [add_comm, ← Finset.card_sdiff_add_card_eq_card
            (by intro v hv; simp)]
          congr 1
        have hRle : R.card ≤ Cᶜ.card := Finset.card_le_card hRsub
        have hA0leC : A0.card ≤ C.card := Finset.card_le_card hA0
        have hdiff_nat' :
            (Finset.univ : Finset V).card - (A0.card + R.card) =
              (C.card - A0.card) + (Cᶜ.card - R.card) := by
          omega
        rw [hcard_union, hdiff_nat', pow_add, pow_add]
        ring
      calc
          ∑ R ∈ Cᶜ.powerset,
              p ^ (A0 ∪ R).card *
                (1 - p) ^ ((Finset.univ : Finset V).card - (A0 ∪ R).card)
          = ∑ R ∈ Cᶜ.powerset,
              p ^ A0.card * (1 - p) ^ (C.card - A0.card) *
                (p ^ R.card * (1 - p) ^ (Cᶜ.card - R.card)) := by
              exact Finset.sum_congr rfl hterm
          _ = p ^ A0.card * (1 - p) ^ (C.card - A0.card) *
                (∑ R ∈ Cᶜ.powerset, p ^ R.card * (1 - p) ^ (Cᶜ.card - R.card)) := by
                rw [Finset.mul_sum]
          _ = p ^ A0.card * (1 - p) ^ (C.card - A0.card) := by
              have hpadd : p + (1 - p) = 1 := by ring
              rw [Finset.sum_pow_mul_eq_add_pow, hpadd, one_pow, mul_one]
    · intro R hR T hT hRT
      exact himage_inj hR hT hRT
  let w : ℝ :=
    (p ^ A0.card * (1 - p) ^ (C.card - A0.card)) *
      (∏ v : V, if v ∈ L then t v else 1) *
        (∏ v : V, if v ∈ U then (1 - t v) else 1)
  refine ⟨w, ?_, ?_, rfl⟩
  · dsimp [w]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hp0 A0.card)
          (pow_nonneg (sub_nonneg.mpr hp1) (C.card - A0.card)))
        hcut_nonneg_L)
      hcut_nonneg_U
  · have hcell_target :
        cell =
          {ω |
            ω.1 ∩ C = A0 ∧
              (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                ∀ v : V, v ∈ U → t v < ω.2 v} := rfl
    rw [← hcell_target, hmeasure_cell]
    rw [← ENNReal.ofReal_sum_of_nonneg (s := S) (f := fun A => weight A)
      (by intro A hA; exact hweight_nonneg A)]
    rw [hsum_weight]
    simp [w, cutWeight, mul_assoc]
