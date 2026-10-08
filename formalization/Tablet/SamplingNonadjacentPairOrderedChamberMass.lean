import Tablet.SamplingFiniteCoordinateMarginalCellLaw
import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingBernoulliPrioritySubsetSum
import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable
import Tablet.SamplingTwoCoordinateComplementMeasurePreserving
import Tablet.SamplingTwoCoordinateFiberBoxVolume
import Tablet.SamplingTwoCoordinateChamberFiberVolume
import Tablet.SamplingTwoCoordinateChamberVolume

open BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

-- [TABLET NODE: SamplingNonadjacentPairOrderedChamberMass]
theorem SamplingNonadjacentPairOrderedChamberMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (u v : V) (uOnly vBlock : Finset V)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (huv : u ≠ v)
    (hu_not : u ∉ uOnly ∪ vBlock)
    (hv_not : v ∉ uOnly ∪ vBlock)
    (hdisj : Disjoint uOnly vBlock)
    (hν_atom : ∀ A : Finset V,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)))
    (hν_cube : ∀ A : Finset V,
      ν {ω | ω.1 = A ∧ ∀ q : V, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hν_rect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ q : V, t q ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ q : V, 0 ≤ ω.2 q ∧ ω.2 q ≤ t q} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ q : V, t q)) :
    ν {ω |
        u ∈ ω.1 ∧ v ∈ ω.1 ∧
          (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
                ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v} =
      ENNReal.ofReal
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            p ^ 2 *
              (((1 - p) + p * a) ^ uOnly.card *
                ((1 - p) + p * b) ^ vBlock.card)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  have hU_sum : ∀ a : ℝ,
      (∑ B ∈ uOnly.powerset,
          p ^ B.card * (1 - p) ^ (uOnly.card - B.card) * a ^ B.card) =
        ((1 - p) + p * a) ^ uOnly.card := by
    intro a
    exact SamplingBernoulliPrioritySubsetSum uOnly p a
  have hT_sum : ∀ b : ℝ,
      (∑ B ∈ vBlock.powerset,
          p ^ B.card * (1 - p) ^ (vBlock.card - B.card) * b ^ B.card) =
        ((1 - p) + p * b) ^ vBlock.card := by
    intro b
    exact SamplingBernoulliPrioritySubsetSum vBlock p b
  have hR_sum :
      (∑ R ∈ ((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)).powerset,
          p ^ R.card *
            (1 - p) ^
              (((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)).card -
                R.card) *
              (1 : ℝ) ^ R.card) =
        ((1 - p) + p * (1 : ℝ)) ^
          ((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)).card := by
    exact SamplingBernoulliPrioritySubsetSum
      ((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)) p (1 : ℝ)
  let chamber (BU BT : Finset V) : Set (V → ℝ) :=
    {q : V → ℝ |
      (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
        q v ≤ q u ∧
          (∀ z : V, z ∈ BU → q z < q u) ∧
            ∀ z : V, z ∈ BT → q z < q v}
  let fullCube : Set (Finset V × (V → ℝ)) :=
    {ω | ∀ x : V, ω.2 x ∈ Set.Icc (0 : ℝ) 1}
  have hchamber_meas (BU BT : Finset V) : MeasurableSet (chamber BU BT) := by
    dsimp [chamber]
    measurability
  have hfullCube_meas : MeasurableSet fullCube := by
    dsimp [fullCube]
    measurability
  have hatom_fullCube (A : Finset V) :
      ν ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩ fullCube) =
        ν {ω : Finset V × (V → ℝ) | ω.1 = A} := by
    have hone : ∀ x : V, (fun _ : V => (1 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := by
      intro x
      exact ⟨zero_le_one, le_rfl⟩
    have hrect := hν_rect A (fun _ : V => (1 : ℝ)) hone
    calc
      ν ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩ fullCube)
          = ν {ω : Finset V × (V → ℝ) |
              ω.1 = A ∧ ∀ x : V, 0 ≤ ω.2 x ∧ ω.2 x ≤ (fun _ : V => (1 : ℝ)) x} := by
            congr 1
      _ = ν {ω : Finset V × (V → ℝ) | ω.1 = A} *
            ENNReal.ofReal (∏ x : V, (fun _ : V => (1 : ℝ)) x) := hrect
      _ = ν {ω : Finset V × (V → ℝ) | ω.1 = A} := by
            simp
  have hpiece
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (_hR : R ∈ ((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)).powerset) :
      let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
      ν ({ω : Finset V × (V → ℝ) | ω.1 = A ∧ ω.2 ∈ chamber BU BT} ∩ fullCube) =
        ν {ω : Finset V × (V → ℝ) | ω.1 = A} *
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
              a ^ BU.card * b ^ BT.card) := by
    intro A
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hBUQ : Disjoint BU ({u, v} : Finset V) := by
      rw [Finset.disjoint_left]
      intro z hzBU hzpair
      rcases Finset.mem_insert.mp hzpair with hzu | hzv
      · subst z
        exact hu_not (Finset.mem_union.mpr (Or.inl (hBUsub hzBU)))
      · have hzv' : z = v := by simpa using hzv
        subst z
        exact hv_not (Finset.mem_union.mpr (Or.inl (hBUsub hzBU)))
    have hBTQ : Disjoint BT ({u, v} : Finset V) := by
      rw [Finset.disjoint_left]
      intro z hzBT hzpair
      rcases Finset.mem_insert.mp hzpair with hzu | hzv
      · subst z
        exact hu_not (Finset.mem_union.mpr (Or.inr (hBTsub hzBT)))
      · have hzv' : z = v := by simpa using hzv
        subst z
        exact hv_not (Finset.mem_union.mpr (Or.inr (hBTsub hzBT)))
    have hBdisj : Disjoint BU BT := hdisj.mono hBUsub hBTsub
    have hC_meas : MeasurableSet (chamber BU BT) := by
      dsimp [chamber]
      measurability
    have hC_cube :
        chamber BU BT ⊆ {q : V → ℝ | ∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1} := by
      intro q hq
      exact hq.1
    have hfinite_atom :
        ν {ω : Finset V × (V → ℝ) | ω.1 = A} ≠ ⊤ := by
      rw [hν_atom A]
      exact ENNReal.ofReal_ne_top
    have hlower :
        ∀ t : V → ℝ,
          (∀ x : V, t x ∈ Set.Icc (0 : ℝ) 1) →
            ν {ω : Finset V × (V → ℝ) |
              ω.1 = A ∧ ∀ x : V, 0 ≤ ω.2 x ∧ ω.2 x ≤ t x} =
              ν {ω : Finset V × (V → ℝ) | ω.1 = A} *
                ENNReal.ofReal (∏ x : V, t x) := by
      intro t ht
      exact hν_rect A t ht
    calc
      ν ({ω : Finset V × (V → ℝ) | ω.1 = A ∧ ω.2 ∈ chamber BU BT} ∩ fullCube)
          = ν {ω : Finset V × (V → ℝ) |
              (ω.1 = A ∧ ω.2 ∈ chamber BU BT) ∧
                ∀ x : V, ω.2 x ∈ Set.Icc (0 : ℝ) 1} := by
            rfl
      _ = ν {ω : Finset V × (V → ℝ) | ω.1 = A} *
            MeasureTheory.volume (chamber BU BT) := by
            exact SamplingFiniteProductLowerOrthantEqualityMeasurable
              (ν := ν)
              (F := fun ω : Finset V × (V → ℝ) => ω.1 = A)
              (p := fun ω : Finset V × (V → ℝ) => ω.2)
              (hp_meas := measurable_snd)
              (M := ν {ω : Finset V × (V → ℝ) | ω.1 = A})
              (C := chamber BU BT)
              hC_meas hC_cube hfinite_atom rfl hlower
      _ = ν {ω : Finset V × (V → ℝ) | ω.1 = A} *
            ENNReal.ofReal
              (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                a ^ BU.card * b ^ BT.card) := by
            rw [SamplingTwoCoordinateChamberVolume u v BU BT huv hBUQ hBTQ hBdisj]
  have hpiece_atom
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ ((Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)).powerset) :
      let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
      ν ({ω : Finset V × (V → ℝ) | ω.1 = A ∧ ω.2 ∈ chamber BU BT} ∩ fullCube) =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)) *
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
              a ^ BU.card * b ^ BT.card) := by
    intro A
    rw [hpiece BU BT R hBU hBT hR]
    rw [hν_atom A]
  let outside : Finset V := (Finset.univ : Finset V) \ ({u, v} ∪ uOnly ∪ vBlock)
  let activeEvent : Set (Finset V × (V → ℝ)) :=
    {ω |
      u ∈ ω.1 ∧ v ∈ ω.1 ∧
        (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
          ω.2 v ≤ ω.2 u ∧
            (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
              ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v}
  let piece (BU BT R : Finset V) : Set (Finset V × (V → ℝ)) :=
    ({ω : Finset V × (V → ℝ) |
      ω.1 = ({u, v} : Finset V) ∪ BU ∪ BT ∪ R ∧
        ω.2 ∈ chamber BU BT} ∩ fullCube)
  have hpiece_meas (BU BT R : Finset V) : MeasurableSet (piece BU BT R) := by
    dsimp [piece]
    let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
    have hmeas :
        MeasurableSet
          ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩
            ({ω : Finset V × (V → ℝ) | ω.2 ∈ chamber BU BT} ∩ fullCube)) :=
      ((measurableSet_singleton
          A).preimage measurable_fst).inter
        (((hchamber_meas BU BT).preimage measurable_snd).inter hfullCube_meas)
    convert hmeas using 1
    ext ω
    simp [A, and_assoc]
  have hdecomp
      (A : Finset V) (huA : u ∈ A) (hvA : v ∈ A) :
      A = ({u, v} : Finset V) ∪ (A ∩ uOnly) ∪ (A ∩ vBlock) ∪ (A ∩ outside) := by
    ext x
    constructor
    · intro hxA
      by_cases hxu : x = u
      · subst x
        simp [huA]
      · by_cases hxv : x = v
        · subst x
          simp [hvA]
        · by_cases hxU : x ∈ uOnly
          · simp [hxA, hxU]
          · by_cases hxT : x ∈ vBlock
            · simp [hxA, hxT]
            · have hxout : x ∈ outside := by
                simp [outside, hxu, hxv, hxU, hxT]
              simp [hxA, hxout]
    · intro hx
      have hx' :
          x = u ∨ x = v ∨ x ∈ A ∩ uOnly ∨ x ∈ A ∩ vBlock ∨
            x ∈ A ∩ outside := by
        simpa [Finset.mem_union] using hx
      rcases hx' with hxu | hxRest
      · subst x
        exact huA
      · rcases hxRest with hxAU | hxRest'
        · subst x
          exact hvA
        · rcases hxRest' with hxAT | hxAO
          · exact (Finset.mem_inter.mp hxAT).1
          · rcases hxAO with hxAV | hxAO
            · exact (Finset.mem_inter.mp hxAV).1
            · exact (Finset.mem_inter.mp hxAO).1
  have hinter_uOnly_of_decomp
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      ((({u, v} : Finset V) ∪ BU ∪ BT ∪ R) ∩ uOnly) = BU := by
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hRsub : R ⊆ outside := Finset.mem_powerset.mp hR
    ext x
    constructor
    · intro hx
      have hxA := (Finset.mem_inter.mp hx).1
      have hxU := (Finset.mem_inter.mp hx).2
      have hxA' :
          x = u ∨ x = v ∨ x ∈ BU ∨ x ∈ BT ∨ x ∈ R := by
        simpa [Finset.mem_union] using hxA
      rcases hxA' with hxu | hxRest
      · subst x
        exact False.elim (hu_not (Finset.mem_union.mpr (Or.inl hxU)))
      · rcases hxRest with hxBU | hxRest'
        · subst x
          exact False.elim (hv_not (Finset.mem_union.mpr (Or.inl hxU)))
        · rcases hxRest' with hxBT | hxR
          · exact hxBT
          · rcases hxR with hxBT | hxR
            · exact False.elim (Finset.disjoint_left.mp hdisj hxU (hBTsub hxBT))
            · have hxout : x ∈ outside := hRsub hxR
              have hxnotU : x ∉ uOnly := by
                intro hxU'
                exact (Finset.mem_sdiff.mp hxout).2 (by simp [hxU'])
              exact False.elim (hxnotU hxU)
    · intro hxBU
      exact Finset.mem_inter.mpr
        ⟨by simp [hxBU], hBUsub hxBU⟩
  have hinter_vBlock_of_decomp
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      ((({u, v} : Finset V) ∪ BU ∪ BT ∪ R) ∩ vBlock) = BT := by
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hRsub : R ⊆ outside := Finset.mem_powerset.mp hR
    ext x
    constructor
    · intro hx
      have hxA := (Finset.mem_inter.mp hx).1
      have hxT := (Finset.mem_inter.mp hx).2
      have hxA' :
          x = u ∨ x = v ∨ x ∈ BU ∨ x ∈ BT ∨ x ∈ R := by
        simpa [Finset.mem_union] using hxA
      rcases hxA' with hxu | hxRest
      · subst x
        exact False.elim (hu_not (Finset.mem_union.mpr (Or.inr hxT)))
      · rcases hxRest with hxBU | hxRest'
        · subst x
          exact False.elim (hv_not (Finset.mem_union.mpr (Or.inr hxT)))
        · rcases hxRest' with hxBT | hxR
          · exact False.elim (Finset.disjoint_left.mp hdisj (hBUsub hxBT) hxT)
          · rcases hxR with hxBT | hxR
            · exact hxBT
            · have hxout : x ∈ outside := hRsub hxR
              have hxnotT : x ∉ vBlock := by
                intro hxT'
                exact (Finset.mem_sdiff.mp hxout).2 (by simp [hxT'])
              exact False.elim (hxnotT hxT)
    · intro hxBT
      exact Finset.mem_inter.mpr
        ⟨by simp [hxBT], hBTsub hxBT⟩
  have hinter_outside_of_decomp
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      ((({u, v} : Finset V) ∪ BU ∪ BT ∪ R) ∩ outside) = R := by
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hRsub : R ⊆ outside := Finset.mem_powerset.mp hR
    ext x
    constructor
    · intro hx
      have hxA := (Finset.mem_inter.mp hx).1
      have hxout := (Finset.mem_inter.mp hx).2
      have hxA' :
          x = u ∨ x = v ∨ x ∈ BU ∨ x ∈ BT ∨ x ∈ R := by
        simpa [Finset.mem_union] using hxA
      rcases hxA' with hxu | hxRest
      · subst x
        exact False.elim ((Finset.mem_sdiff.mp hxout).2 (by simp))
      · rcases hxRest with hxv | hxRest'
        · subst x
          exact False.elim ((Finset.mem_sdiff.mp hxout).2 (by simp))
        · rcases hxRest' with hxBU | hxRest''
          · exact False.elim ((Finset.mem_sdiff.mp hxout).2 (by simp [hBUsub hxBU]))
          · rcases hxRest'' with hxBT | hxR
            · exact False.elim ((Finset.mem_sdiff.mp hxout).2 (by simp [hBTsub hxBT]))
            · exact hxR
    · intro hxR
      exact Finset.mem_inter.mpr
        ⟨by simp [hxR], hRsub hxR⟩
  have hfull_partition :
      activeEvent ∩ fullCube =
        ⋃ BU ∈ uOnly.powerset,
          ⋃ BT ∈ vBlock.powerset,
            ⋃ R ∈ outside.powerset, piece BU BT R := by
    ext ω
    constructor
    · intro hω
      let BU : Finset V := ω.1 ∩ uOnly
      let BT : Finset V := ω.1 ∩ vBlock
      let R : Finset V := ω.1 ∩ outside
      have hBU : BU ∈ uOnly.powerset := by
        exact Finset.mem_powerset.mpr (by intro x hx; exact (Finset.mem_inter.mp hx).2)
      have hBT : BT ∈ vBlock.powerset := by
        exact Finset.mem_powerset.mpr (by intro x hx; exact (Finset.mem_inter.mp hx).2)
      have hR : R ∈ outside.powerset := by
        exact Finset.mem_powerset.mpr (by intro x hx; exact (Finset.mem_inter.mp hx).2)
      refine Set.mem_iUnion.mpr ⟨BU, Set.mem_iUnion.mpr ⟨hBU, ?_⟩⟩
      refine Set.mem_iUnion.mpr ⟨BT, Set.mem_iUnion.mpr ⟨hBT, ?_⟩⟩
      refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, ?_⟩⟩
      have hA :
          ω.1 = ({u, v} : Finset V) ∪ BU ∪ BT ∪ R := by
        simpa [BU, BT, R] using hdecomp ω.1 hω.1.1 hω.1.2.1
      refine ⟨?_, hω.2⟩
      refine ⟨hA, ?_⟩
      dsimp [chamber]
      refine ⟨?_, hω.1.2.2.2.1, ?_, ?_⟩
      · intro x
        exact hω.2 x
      · intro z hzBU
        exact hω.1.2.2.2.2.1 z (Finset.mem_inter.mp hzBU).2
          (Finset.mem_inter.mp hzBU).1
      · intro z hzBT
        exact hω.1.2.2.2.2.2 z (Finset.mem_inter.mp hzBT).2
          (Finset.mem_inter.mp hzBT).1
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨BU, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hBU, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨BT, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hBT, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨R, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hR, hω⟩
      rcases hω with ⟨hpieceω, hfullω⟩
      rcases hpieceω with ⟨hA, hchamber⟩
      have hBUeq :
          ((({u, v} : Finset V) ∪ BU ∪ BT ∪ R) ∩ uOnly) = BU :=
        hinter_uOnly_of_decomp BU BT R hBU hBT hR
      have hBTeq :
          ((({u, v} : Finset V) ∪ BU ∪ BT ∪ R) ∩ vBlock) = BT :=
        hinter_vBlock_of_decomp BU BT R hBU hBT hR
      refine ⟨?_, hfullω⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hA]
      · simp [hA]
      · intro q _hq
        exact hfullω q
      · exact hchamber.2.1
      · intro z hzU hzA
        have hzBU : z ∈ BU := by
          rw [← hBUeq]
          exact Finset.mem_inter.mpr ⟨by simpa [hA] using hzA, hzU⟩
        exact hchamber.2.2.1 z hzBU
      · intro z hzT hzA
        have hzBT : z ∈ BT := by
          rw [← hBTeq]
          exact Finset.mem_inter.mpr ⟨by simpa [hA] using hzA, hzT⟩
        exact hchamber.2.2.2 z hzBT
  have hpiece_disjoint
      (BU BT R BU' BT' R' : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset)
      (hBU' : BU' ∈ uOnly.powerset)
      (hBT' : BT' ∈ vBlock.powerset)
      (hR' : R' ∈ outside.powerset)
      (hne : (BU, BT, R) ≠ (BU', BT', R')) :
      Disjoint (piece BU BT R) (piece BU' BT' R') := by
    rw [Set.disjoint_left]
    intro ω hω hω'
    rcases hω with ⟨hωpiece, _hωfull⟩
    rcases hωpiece with ⟨hA, _hchamber⟩
    rcases hω' with ⟨hωpiece', _hωfull'⟩
    rcases hωpiece' with ⟨hA', _hchamber'⟩
    let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
    let A' : Finset V := ({u, v} : Finset V) ∪ BU' ∪ BT' ∪ R'
    have hAA' : A = A' := hA.symm.trans hA'
    have hBUeq : BU = BU' := by
      have hcongr := congrArg (fun S : Finset V => S ∩ uOnly) hAA'
      have hleft : A ∩ uOnly = BU :=
        hinter_uOnly_of_decomp BU BT R hBU hBT hR
      have hright : A' ∩ uOnly = BU' :=
        hinter_uOnly_of_decomp BU' BT' R' hBU' hBT' hR'
      exact hleft.symm.trans (hcongr.trans hright)
    have hBTeq : BT = BT' := by
      have hcongr := congrArg (fun S : Finset V => S ∩ vBlock) hAA'
      have hleft : A ∩ vBlock = BT :=
        hinter_vBlock_of_decomp BU BT R hBU hBT hR
      have hright : A' ∩ vBlock = BT' :=
        hinter_vBlock_of_decomp BU' BT' R' hBU' hBT' hR'
      exact hleft.symm.trans (hcongr.trans hright)
    have hReq : R = R' := by
      have hcongr := congrArg (fun S : Finset V => S ∩ outside) hAA'
      have hleft : A ∩ outside = R :=
        hinter_outside_of_decomp BU BT R hBU hBT hR
      have hright : A' ∩ outside = R' :=
        hinter_outside_of_decomp BU' BT' R' hBU' hBT' hR'
      exact hleft.symm.trans (hcongr.trans hright)
    exact hne (by simp [hBUeq, hBTeq, hReq])
  have hmeasure_full_partition :
      ν (activeEvent ∩ fullCube) =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset, ν (piece BU BT R) := by
    rw [hfull_partition]
    rw [MeasureTheory.measure_biUnion_finset]
    · apply Finset.sum_congr rfl
      intro BU hBU
      rw [MeasureTheory.measure_biUnion_finset]
      · apply Finset.sum_congr rfl
        intro BT hBT
        rw [MeasureTheory.measure_biUnion_finset]
        · intro R hR R' hR' hRne
          exact hpiece_disjoint BU BT R BU BT R' hBU hBT hR hBU hBT hR'
            (by
              intro htriple
              exact hRne (by simpa using congrArg Prod.snd (congrArg Prod.snd htriple)))
        · intro R _hR
          exact hpiece_meas BU BT R
      · intro BT hBT BT' hBT' hBTne
        rw [Function.onFun, Set.disjoint_left]
        intro ω hω hω'
        rcases Set.mem_iUnion.mp hω with ⟨R, hωR⟩
        rcases Set.mem_iUnion.mp hωR with ⟨hR, hωpiece⟩
        rcases Set.mem_iUnion.mp hω' with ⟨R', hωR'⟩
        rcases Set.mem_iUnion.mp hωR' with ⟨hR', hωpiece'⟩
        exact (Set.disjoint_left.mp
          (hpiece_disjoint BU BT R BU BT' R' hBU hBT hR hBU hBT' hR'
            (by
              intro htriple
              exact hBTne (by simpa using congrArg Prod.fst (congrArg Prod.snd htriple))))
          hωpiece hωpiece')
      · intro BT _hBT
        exact Finset.measurableSet_biUnion outside.powerset (fun R _hR => hpiece_meas BU BT R)
    · intro BU hBU BU' hBU' hBUne
      rw [Function.onFun, Set.disjoint_left]
      intro ω hω hω'
      rcases Set.mem_iUnion.mp hω with ⟨BT, hωBT⟩
      rcases Set.mem_iUnion.mp hωBT with ⟨hBT, hωBT'⟩
      rcases Set.mem_iUnion.mp hωBT' with ⟨R, hωR⟩
      rcases Set.mem_iUnion.mp hωR with ⟨hR, hωpiece⟩
      rcases Set.mem_iUnion.mp hω' with ⟨BT', hωBT2⟩
      rcases Set.mem_iUnion.mp hωBT2 with ⟨hBT', hωBT2'⟩
      rcases Set.mem_iUnion.mp hωBT2' with ⟨R', hωR'⟩
      rcases Set.mem_iUnion.mp hωR' with ⟨hR', hωpiece'⟩
      exact (Set.disjoint_left.mp
        (hpiece_disjoint BU BT R BU' BT' R' hBU hBT hR hBU' hBT' hR'
          (by
            intro htriple
            exact hBUne (by simpa using congrArg Prod.fst htriple)))
        hωpiece hωpiece')
    · intro BU _hBU
      exact Finset.measurableSet_biUnion vBlock.powerset fun BT _hBT =>
        Finset.measurableSet_biUnion outside.powerset fun R _hR => hpiece_meas BU BT R
  have hmeasure_full_partition_atom :
      ν (activeEvent ∩ fullCube) =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset,
              let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
              ENNReal.ofReal
                (p ^ A.card *
                  (1 - p) ^ ((Finset.univ : Finset V).card - A.card)) *
                ENNReal.ofReal
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ BU.card * b ^ BT.card) := by
    rw [hmeasure_full_partition]
    apply Finset.sum_congr rfl
    intro BU hBU
    apply Finset.sum_congr rfl
    intro BT hBT
    apply Finset.sum_congr rfl
    intro R hR
    exact hpiece_atom BU BT R hBU hBT hR
  have hactive_fullCube :
      ν activeEvent = ν (activeEvent ∩ fullCube) := by
    let activeCubeAtom (A : Finset V) : Set (Finset V × (V → ℝ)) :=
      {ω | ω.1 = A ∧ ∀ q : V, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1}
    let fullCubeAtom (A : Finset V) : Set (Finset V × (V → ℝ)) :=
      {ω | ω.1 = A} ∩ fullCube
    let badAtom (A : Finset V) : Set (Finset V × (V → ℝ)) :=
      activeCubeAtom A \ fullCubeAtom A
    have hbadAtom_zero (A : Finset V) : ν (badAtom A) = 0 := by
      have hsub : fullCubeAtom A ⊆ activeCubeAtom A := by
        intro ω hω
        exact ⟨hω.1, fun q _hq => hω.2 q⟩
      have hfinite_full : ν (fullCubeAtom A) ≠ ⊤ := by
        rw [show fullCubeAtom A =
            ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩ fullCube) by rfl]
        rw [hatom_fullCube A, hν_atom A]
        exact ENNReal.ofReal_ne_top
      have hmeasure_eq : ν (activeCubeAtom A) = ν (fullCubeAtom A) := by
        rw [show activeCubeAtom A =
            {ω : Finset V × (V → ℝ) |
              ω.1 = A ∧ ∀ q : V, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1} by rfl]
        rw [show fullCubeAtom A =
            ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩ fullCube) by rfl]
        rw [hν_cube A, hatom_fullCube A]
      calc
        ν (badAtom A) = ν (activeCubeAtom A) - ν (fullCubeAtom A) := by
          exact MeasureTheory.measure_diff hsub
            ((show MeasurableSet (fullCubeAtom A) from by
              dsimp [fullCubeAtom]
              exact ((measurableSet_singleton A).preimage measurable_fst).inter hfullCube_meas).nullMeasurableSet)
            hfinite_full
        _ = 0 := by
          rw [hmeasure_eq, tsub_self]
    have hbad_union_zero :
        ν (⋃ A ∈ (Finset.univ : Finset V).powerset, badAtom A) = 0 := by
      apply le_antisymm
      · calc
          ν (⋃ A ∈ (Finset.univ : Finset V).powerset, badAtom A)
              ≤ ∑ A ∈ (Finset.univ : Finset V).powerset, ν (badAtom A) := by
                exact MeasureTheory.measure_biUnion_finset_le
                  ((Finset.univ : Finset V).powerset) badAtom
          _ = 0 := by
                simp [hbadAtom_zero]
      · exact zero_le _
    have hdiff_subset :
        activeEvent \ fullCube ⊆
          ⋃ A ∈ (Finset.univ : Finset V).powerset, badAtom A := by
      intro ω hω
      have hAuniv : ω.1 ∈ (Finset.univ : Finset V).powerset := by
        exact Finset.mem_powerset.mpr (by intro x _hx; exact Finset.mem_univ x)
      refine Set.mem_iUnion.mpr ⟨ω.1, Set.mem_iUnion.mpr ⟨hAuniv, ?_⟩⟩
      exact ⟨⟨rfl, hω.1.2.2.1⟩, by
        intro hfullAtom
        exact hω.2 hfullAtom.2⟩
    have hdiff_zero : ν (activeEvent \ fullCube) = 0 :=
      MeasureTheory.measure_mono_null hdiff_subset hbad_union_zero
    have hdiff_eq :
        activeEvent \ (activeEvent ∩ fullCube) = activeEvent \ fullCube := by
      ext ω
      by_cases hωE : ω ∈ activeEvent
      · simp [hωE]
      · simp [hωE]
    have hdiff_zero' : ν (activeEvent \ (activeEvent ∩ fullCube)) = 0 := by
      rw [hdiff_eq, hdiff_zero]
    exact (MeasureTheory.measure_eq_measure_of_null_diff
      (Set.inter_subset_left) hdiff_zero').symm
  have hintegral_nonneg (BU BT : Finset V) :
      0 ≤
        (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
          a ^ BU.card * b ^ BT.card) := by
    refine intervalIntegral.integral_nonneg zero_le_one ?_
    intro a ha
    refine intervalIntegral.integral_nonneg ha.1 ?_
    intro b hb
    exact mul_nonneg (pow_nonneg ha.1 _) (pow_nonneg hb.1 _)
  have hatom_weight_nonneg (A : Finset V) :
      0 ≤
        p ^ A.card *
          (1 - p) ^ ((Finset.univ : Finset V).card - A.card) := by
    exact mul_nonneg (pow_nonneg hp0 _)
      (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hpair_card : ({u, v} : Finset V).card = 2 := by
    simp [huv]
  have hpair_disj_uOnly : Disjoint ({u, v} : Finset V) uOnly := by
    rw [Finset.disjoint_left]
    intro z hzpair hzU
    rcases Finset.mem_insert.mp hzpair with hzu | hzv
    · subst z
      exact hu_not (Finset.mem_union.mpr (Or.inl hzU))
    · have hzv' : z = v := by simpa using hzv
      subst z
      exact hv_not (Finset.mem_union.mpr (Or.inl hzU))
  have hpair_disj_vBlock : Disjoint ({u, v} : Finset V) vBlock := by
    rw [Finset.disjoint_left]
    intro z hzpair hzT
    rcases Finset.mem_insert.mp hzpair with hzu | hzv
    · subst z
      exact hu_not (Finset.mem_union.mpr (Or.inr hzT))
    · have hzv' : z = v := by simpa using hzv
      subst z
      exact hv_not (Finset.mem_union.mpr (Or.inr hzT))
  have hpair_u_v_disj : Disjoint (({u, v} : Finset V) ∪ uOnly) vBlock := by
    rw [Finset.disjoint_union_left]
    exact ⟨hpair_disj_vBlock, hdisj⟩
  have hbase_card :
      (({u, v} : Finset V) ∪ uOnly ∪ vBlock).card =
        2 + uOnly.card + vBlock.card := by
    calc
      (({u, v} : Finset V) ∪ uOnly ∪ vBlock).card
          = (({u, v} : Finset V) ∪ uOnly).card + vBlock.card := by
            rw [Finset.card_union_of_disjoint hpair_u_v_disj]
      _ = (({u, v} : Finset V).card + uOnly.card) + vBlock.card := by
            rw [Finset.card_union_of_disjoint hpair_disj_uOnly]
      _ = 2 + uOnly.card + vBlock.card := by
            rw [hpair_card]
  have hbase_subset_univ :
      ({u, v} : Finset V) ∪ uOnly ∪ vBlock ⊆ (Finset.univ : Finset V) := by
    intro x _hx
    simp
  have huniv_card_split :
      (Finset.univ : Finset V).card =
        2 + uOnly.card + vBlock.card + outside.card := by
    have hsdiff :=
      Finset.card_sdiff_of_subset (s := ({u, v} : Finset V) ∪ uOnly ∪ vBlock)
        (t := (Finset.univ : Finset V)) hbase_subset_univ
    have hsdiff' :
        outside.card =
          (Finset.univ : Finset V).card -
            (({u, v} : Finset V) ∪ uOnly ∪ vBlock).card := by
      simpa [outside] using hsdiff
    have hbasele :
        (({u, v} : Finset V) ∪ uOnly ∪ vBlock).card ≤
          (Finset.univ : Finset V).card :=
      Finset.card_le_card hbase_subset_univ
    rw [hbase_card] at hsdiff'
    omega
  have hA_card
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      (({u, v} : Finset V) ∪ BU ∪ BT ∪ R).card =
        2 + BU.card + BT.card + R.card := by
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hRsub : R ⊆ outside := Finset.mem_powerset.mp hR
    have hpair_BU : Disjoint ({u, v} : Finset V) BU :=
      hpair_disj_uOnly.mono_right hBUsub
    have hpair_BT : Disjoint ({u, v} : Finset V) BT :=
      hpair_disj_vBlock.mono_right hBTsub
    have hBU_BT : Disjoint BU BT := hdisj.mono hBUsub hBTsub
    have hpair_R : Disjoint ({u, v} : Finset V) R := by
      rw [Finset.disjoint_left]
      intro z hzpair hzR
      have hzout : z ∈ outside := hRsub hzR
      have hzout' : ¬ z = u ∧ ¬ z = v ∧ z ∉ uOnly ∧ z ∉ vBlock := by
        simpa [outside] using hzout
      rcases Finset.mem_insert.mp hzpair with hzu | hzv
      · exact hzout'.1 hzu
      · exact hzout'.2.1 (by simpa using hzv)
    have hBU_R : Disjoint BU R := by
      rw [Finset.disjoint_left]
      intro z hzBU hzR
      have hzout : z ∈ outside := hRsub hzR
      have hzout' : ¬ z = u ∧ ¬ z = v ∧ z ∉ uOnly ∧ z ∉ vBlock := by
        simpa [outside] using hzout
      exact hzout'.2.2.1 (hBUsub hzBU)
    have hBT_R : Disjoint BT R := by
      rw [Finset.disjoint_left]
      intro z hzBT hzR
      have hzout : z ∈ outside := hRsub hzR
      have hzout' : ¬ z = u ∧ ¬ z = v ∧ z ∉ uOnly ∧ z ∉ vBlock := by
        simpa [outside] using hzout
      exact hzout'.2.2.2 (hBTsub hzBT)
    have hpair_BU_BT : Disjoint (({u, v} : Finset V) ∪ BU) BT := by
      rw [Finset.disjoint_union_left]
      exact ⟨hpair_BT, hBU_BT⟩
    have hpair_BU_BT_R : Disjoint (({u, v} : Finset V) ∪ BU ∪ BT) R := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨hpair_R, hBU_R⟩, hBT_R⟩
    calc
      (({u, v} : Finset V) ∪ BU ∪ BT ∪ R).card
          = (({u, v} : Finset V) ∪ BU ∪ BT).card + R.card := by
            rw [Finset.card_union_of_disjoint hpair_BU_BT_R]
      _ = (({u, v} : Finset V) ∪ BU).card + BT.card + R.card := by
            rw [Finset.card_union_of_disjoint hpair_BU_BT]
      _ = (({u, v} : Finset V).card + BU.card) + BT.card + R.card := by
            rw [Finset.card_union_of_disjoint hpair_BU]
      _ = 2 + BU.card + BT.card + R.card := by
            rw [hpair_card]
  have hA_compl_card
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      (Finset.univ : Finset V).card -
          (({u, v} : Finset V) ∪ BU ∪ BT ∪ R).card =
        (uOnly.card - BU.card) + (vBlock.card - BT.card) +
          (outside.card - R.card) := by
    have hBUsub : BU ⊆ uOnly := Finset.mem_powerset.mp hBU
    have hBTsub : BT ⊆ vBlock := Finset.mem_powerset.mp hBT
    have hRsub : R ⊆ outside := Finset.mem_powerset.mp hR
    have hc := hA_card BU BT R hBU hBT hR
    have hBUle : BU.card ≤ uOnly.card := Finset.card_le_card hBUsub
    have hBTle : BT.card ≤ vBlock.card := Finset.card_le_card hBTsub
    have hRle : R.card ≤ outside.card := Finset.card_le_card hRsub
    omega
  have hweight_factor
      (BU BT R : Finset V)
      (hBU : BU ∈ uOnly.powerset)
      (hBT : BT ∈ vBlock.powerset)
      (hR : R ∈ outside.powerset) :
      let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
      p ^ A.card *
          (1 - p) ^ ((Finset.univ : Finset V).card - A.card) =
        p ^ 2 *
          (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
            (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
              (p ^ R.card * (1 - p) ^ (outside.card - R.card)) := by
    intro A
    have hcomp' :
        (Finset.univ : Finset V).card - (2 + BU.card + BT.card + R.card) =
          (uOnly.card - BU.card) + (vBlock.card - BT.card) +
            (outside.card - R.card) := by
      rw [← hA_card BU BT R hBU hBT hR]
      exact hA_compl_card BU BT R hBU hBT hR
    rw [hA_card BU BT R hBU hBT hR, hcomp']
    simp only [pow_add]
    ring
  have hR_sum_one :
      (∑ R ∈ outside.powerset,
          p ^ R.card * (1 - p) ^ (outside.card - R.card)) = 1 := by
    calc
      (∑ R ∈ outside.powerset,
          p ^ R.card * (1 - p) ^ (outside.card - R.card))
          = ∑ R ∈ outside.powerset,
              p ^ R.card * (1 - p) ^ (outside.card - R.card) *
                (1 : ℝ) ^ R.card := by
              simp
      _ = ((1 - p) + p * (1 : ℝ)) ^ outside.card := by
              simpa [outside] using hR_sum
      _ = 1 := by
              ring
  let atomWeight : Finset V → ℝ := fun A =>
    p ^ A.card * (1 - p) ^ ((Finset.univ : Finset V).card - A.card)
  let chamberIntegral : Finset V → Finset V → ℝ := fun BU BT =>
    ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, a ^ BU.card * b ^ BT.card
  let atomFor : Finset V → Finset V → Finset V → Finset V := fun BU BT R =>
    ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
  let ennTerm : Finset V → Finset V → Finset V → ENNReal := fun BU BT R =>
    ENNReal.ofReal (atomWeight (atomFor BU BT R)) *
      ENNReal.ofReal (chamberIntegral BU BT)
  let realTerm : Finset V → Finset V → Finset V → ℝ := fun BU BT R =>
    atomWeight (atomFor BU BT R) * chamberIntegral BU BT
  have hsum_ofReal :
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset, ennTerm BU BT R) =
        ENNReal.ofReal
          (∑ BU ∈ uOnly.powerset,
            ∑ BT ∈ vBlock.powerset,
              ∑ R ∈ outside.powerset, realTerm BU BT R) := by
    calc
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset, ennTerm BU BT R)
          = ∑ BU ∈ uOnly.powerset,
              ∑ BT ∈ vBlock.powerset,
                ∑ R ∈ outside.powerset,
                  ENNReal.ofReal (realTerm BU BT R) := by
            apply Finset.sum_congr rfl
            intro BU hBU
            apply Finset.sum_congr rfl
            intro BT hBT
            apply Finset.sum_congr rfl
            intro R hR
            dsimp [ennTerm, realTerm, atomWeight, chamberIntegral, atomFor]
            exact (ENNReal.ofReal_mul
              (hatom_weight_nonneg (({u, v} : Finset V) ∪ BU ∪ BT ∪ R))).symm
      _ = ∑ BU ∈ uOnly.powerset,
              ∑ BT ∈ vBlock.powerset,
                ENNReal.ofReal
                  (∑ R ∈ outside.powerset, realTerm BU BT R) := by
            apply Finset.sum_congr rfl
            intro BU hBU
            apply Finset.sum_congr rfl
            intro BT hBT
            rw [← ENNReal.ofReal_sum_of_nonneg]
            intro R hR
            dsimp [realTerm, atomWeight, chamberIntegral, atomFor]
            exact mul_nonneg
              (hatom_weight_nonneg (({u, v} : Finset V) ∪ BU ∪ BT ∪ R))
              (hintegral_nonneg BU BT)
      _ = ∑ BU ∈ uOnly.powerset,
              ENNReal.ofReal
                (∑ BT ∈ vBlock.powerset,
                  ∑ R ∈ outside.powerset, realTerm BU BT R) := by
            apply Finset.sum_congr rfl
            intro BU hBU
            rw [← ENNReal.ofReal_sum_of_nonneg]
            intro BT hBT
            exact Finset.sum_nonneg (by
              intro R hR
              dsimp [realTerm, atomWeight, chamberIntegral, atomFor]
              exact mul_nonneg
                (hatom_weight_nonneg (({u, v} : Finset V) ∪ BU ∪ BT ∪ R))
                (hintegral_nonneg BU BT))
      _ = ENNReal.ofReal
          (∑ BU ∈ uOnly.powerset,
            ∑ BT ∈ vBlock.powerset,
              ∑ R ∈ outside.powerset, realTerm BU BT R) := by
            rw [← ENNReal.ofReal_sum_of_nonneg]
            intro BU hBU
            exact Finset.sum_nonneg (by
              intro BT hBT
              exact Finset.sum_nonneg (by
                intro R hR
                dsimp [realTerm, atomWeight, chamberIntegral, atomFor]
                exact mul_nonneg
                  (hatom_weight_nonneg (({u, v} : Finset V) ∪ BU ∪ BT ∪ R))
                  (hintegral_nonneg BU BT)))
  let F : Finset V → Finset V → ℝ → ℝ → ℝ := fun BU BT a b =>
    p ^ 2 *
      (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
        (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
          (a ^ BU.card * b ^ BT.card)
  have hreal_factor :
      (∑ BU ∈ uOnly.powerset,
        ∑ BT ∈ vBlock.powerset,
          ∑ R ∈ outside.powerset, realTerm BU BT R) =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, F BU BT a b := by
    apply Finset.sum_congr rfl
    intro BU hBU
    apply Finset.sum_congr rfl
    intro BT hBT
    calc
      (∑ R ∈ outside.powerset, realTerm BU BT R)
          = ∑ R ∈ outside.powerset,
              (p ^ 2 *
                (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                  (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                    (p ^ R.card * (1 - p) ^ (outside.card - R.card))) *
                (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                  a ^ BU.card * b ^ BT.card) := by
            apply Finset.sum_congr rfl
            intro R hR
            dsimp [realTerm, atomWeight, atomFor, chamberIntegral]
            have hw := hweight_factor BU BT R hBU hBT hR
            rw [show
              p ^ (({u, v} : Finset V) ∪ BU ∪ BT ∪ R).card *
                  (1 - p) ^
                    (Fintype.card V -
                      (({u, v} : Finset V) ∪ BU ∪ BT ∪ R).card) =
                p ^ 2 *
                  (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                    (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                      (p ^ R.card * (1 - p) ^ (outside.card - R.card)) by
                simpa [Finset.card_univ] using hw]
      _ = (p ^ 2 *
              (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ BU.card * b ^ BT.card)) *
            (∑ R ∈ outside.powerset,
              p ^ R.card * (1 - p) ^ (outside.card - R.card)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro R hR
            ring
      _ = p ^ 2 *
              (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ BU.card * b ^ BT.card) := by
            rw [hR_sum_one]
            ring
      _ = ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, F BU BT a b := by
            dsimp [F]
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro a _ha
            change
              p ^ 2 * (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                    (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                  (∫ b in (0 : ℝ)..a, a ^ BU.card * b ^ BT.card) =
                ∫ b in (0 : ℝ)..a,
                  p ^ 2 * (p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card)) *
                    (p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card)) *
                      (a ^ BU.card * b ^ BT.card)
            rw [← intervalIntegral.integral_const_mul]
  have houter_integrable (BU BT : Finset V) :
      IntervalIntegrable (fun a : ℝ => ∫ b in (0 : ℝ)..a, F BU BT a b)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont_uncurry : Continuous (Function.uncurry (fun a b : ℝ => F BU BT a b)) := by
      dsimp [F, Function.uncurry]
      fun_prop
    have hcont :
        Continuous fun a : ℝ => ∫ b in (0 : ℝ)..a, F BU BT a b := by
      simpa [Function.uncurry] using
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun a b : ℝ => F BU BT a b)
          (a₀ := (0 : ℝ)) hcont_uncurry continuous_id)
    exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hinner_integrable (BU BT : Finset V) (a : ℝ) :
      IntervalIntegrable (fun b : ℝ => F BU BT a b)
        MeasureTheory.volume (0 : ℝ) a := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hsum_integral :
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, F BU BT a b) =
        ∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            ∑ BU ∈ uOnly.powerset,
              ∑ BT ∈ vBlock.powerset, F BU BT a b := by
    calc
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, F BU BT a b)
          = ∑ BU ∈ uOnly.powerset,
              ∫ a in (0 : ℝ)..1,
                ∑ BT ∈ vBlock.powerset, ∫ b in (0 : ℝ)..a, F BU BT a b := by
            apply Finset.sum_congr rfl
            intro BU hBU
            simpa using
              (intervalIntegral.integral_finset_sum
                (s := vBlock.powerset)
                (f := fun BT a => ∫ b in (0 : ℝ)..a, F BU BT a b)
                (a := (0 : ℝ)) (b := 1)
                (by
                  intro BT hBT
                  exact houter_integrable BU BT)).symm
      _ = ∫ a in (0 : ℝ)..1,
              ∑ BU ∈ uOnly.powerset,
                ∑ BT ∈ vBlock.powerset,
                  ∫ b in (0 : ℝ)..a, F BU BT a b := by
            simpa using
              (intervalIntegral.integral_finset_sum
                (s := uOnly.powerset)
                (f := fun BU a =>
                  ∑ BT ∈ vBlock.powerset, ∫ b in (0 : ℝ)..a, F BU BT a b)
                (a := (0 : ℝ)) (b := 1)
                (by
                  intro BU hBU
                  have hcont : Continuous fun a : ℝ =>
                      ∑ BT ∈ vBlock.powerset, ∫ b in (0 : ℝ)..a, F BU BT a b := by
                    apply continuous_finset_sum
                    intro BT hBT
                    have hcont_uncurry :
                        Continuous (Function.uncurry (fun a b : ℝ => F BU BT a b)) := by
                      dsimp [F, Function.uncurry]
                      fun_prop
                    simpa [Function.uncurry] using
                      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
                        (f := fun a b : ℝ => F BU BT a b)
                        (a₀ := (0 : ℝ)) hcont_uncurry continuous_id)
                  exact hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).symm
      _ = ∫ a in (0 : ℝ)..1,
              ∫ b in (0 : ℝ)..a,
                ∑ BU ∈ uOnly.powerset,
                  ∑ BT ∈ vBlock.powerset, F BU BT a b := by
            apply intervalIntegral.integral_congr
            intro a _ha
            calc
              (∑ BU ∈ uOnly.powerset,
                  ∑ BT ∈ vBlock.powerset,
                    ∫ b in (0 : ℝ)..a, F BU BT a b)
                  = ∑ BU ∈ uOnly.powerset,
                      ∫ b in (0 : ℝ)..a,
                        ∑ BT ∈ vBlock.powerset, F BU BT a b := by
                    apply Finset.sum_congr rfl
                    intro BU hBU
                    simpa using
                      (intervalIntegral.integral_finset_sum
                        (s := vBlock.powerset)
                        (f := fun BT b => F BU BT a b)
                        (a := (0 : ℝ)) (b := a)
                        (by
                          intro BT hBT
                          exact hinner_integrable BU BT a)).symm
              _ = ∫ b in (0 : ℝ)..a,
                      ∑ BU ∈ uOnly.powerset,
                        ∑ BT ∈ vBlock.powerset, F BU BT a b := by
                    simpa using
                      (intervalIntegral.integral_finset_sum
                        (s := uOnly.powerset)
                        (f := fun BU b => ∑ BT ∈ vBlock.powerset, F BU BT a b)
                        (a := (0 : ℝ)) (b := a)
                        (by
                          intro BU hBU
                          apply Continuous.intervalIntegrable
                          apply continuous_finset_sum
                          intro BT hBT
                          dsimp [F]
                          fun_prop)).symm
  have hpointwise (a b : ℝ) :
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset, F BU BT a b) =
        p ^ 2 *
          (((1 - p) + p * a) ^ uOnly.card *
            ((1 - p) + p * b) ^ vBlock.card) := by
    let Uterm : Finset V → ℝ := fun BU =>
      p ^ BU.card * (1 - p) ^ (uOnly.card - BU.card) * a ^ BU.card
    let Tterm : Finset V → ℝ := fun BT =>
      p ^ BT.card * (1 - p) ^ (vBlock.card - BT.card) * b ^ BT.card
    calc
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset, F BU BT a b)
          = ∑ BU ∈ uOnly.powerset,
              p ^ 2 * Uterm BU *
                (∑ BT ∈ vBlock.powerset, Tterm BT) := by
            apply Finset.sum_congr rfl
            intro BU hBU
            calc
              (∑ BT ∈ vBlock.powerset, F BU BT a b)
                  = ∑ BT ∈ vBlock.powerset, p ^ 2 * Uterm BU * Tterm BT := by
                    apply Finset.sum_congr rfl
                    intro BT hBT
                    dsimp [F, Uterm, Tterm]
                    ring
              _ = p ^ 2 * Uterm BU *
                    (∑ BT ∈ vBlock.powerset, Tterm BT) := by
                    rw [Finset.mul_sum]
      _ = (∑ BU ∈ uOnly.powerset, p ^ 2 * Uterm BU) *
            (∑ BT ∈ vBlock.powerset, Tterm BT) := by
            rw [Finset.sum_mul]
      _ = p ^ 2 *
              (∑ BU ∈ uOnly.powerset, Uterm BU) *
                (∑ BT ∈ vBlock.powerset, Tterm BT) := by
            rw [← Finset.mul_sum]
      _ = p ^ 2 *
          (((1 - p) + p * a) ^ uOnly.card *
            ((1 - p) + p * b) ^ vBlock.card) := by
            dsimp [Uterm, Tterm]
            rw [hU_sum a, hT_sum b]
            ring
  have hreal_eq :
      (∑ BU ∈ uOnly.powerset,
        ∑ BT ∈ vBlock.powerset,
          ∑ R ∈ outside.powerset, realTerm BU BT R) =
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            p ^ 2 *
              (((1 - p) + p * a) ^ uOnly.card *
                ((1 - p) + p * b) ^ vBlock.card)) := by
    calc
      (∑ BU ∈ uOnly.powerset,
        ∑ BT ∈ vBlock.powerset,
          ∑ R ∈ outside.powerset, realTerm BU BT R)
          = ∑ BU ∈ uOnly.powerset,
              ∑ BT ∈ vBlock.powerset,
                ∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, F BU BT a b :=
            hreal_factor
      _ = ∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              ∑ BU ∈ uOnly.powerset,
                ∑ BT ∈ vBlock.powerset, F BU BT a b := hsum_integral
      _ = ∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              p ^ 2 *
                (((1 - p) + p * a) ^ uOnly.card *
                  ((1 - p) + p * b) ^ vBlock.card) := by
            apply intervalIntegral.integral_congr
            intro a _ha
            apply intervalIntegral.integral_congr
            intro b _hb
            exact hpointwise a b
  have hpartition_as_terms :
      (∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset,
              let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
              ENNReal.ofReal
                (p ^ A.card *
                  (1 - p) ^ ((Finset.univ : Finset V).card - A.card)) *
                ENNReal.ofReal
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ BU.card * b ^ BT.card)) =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset, ennTerm BU BT R := by
    rfl
  calc
    ν {ω |
        u ∈ ω.1 ∧ v ∈ ω.1 ∧
          (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
                ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v}
        = ν activeEvent := by
          rfl
    _ = ν (activeEvent ∩ fullCube) := hactive_fullCube
    _ =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset,
              let A : Finset V := ({u, v} : Finset V) ∪ BU ∪ BT ∪ R
              ENNReal.ofReal
                (p ^ A.card *
                  (1 - p) ^ ((Finset.univ : Finset V).card - A.card)) *
                ENNReal.ofReal
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ BU.card * b ^ BT.card) := hmeasure_full_partition_atom
    _ =
        ∑ BU ∈ uOnly.powerset,
          ∑ BT ∈ vBlock.powerset,
            ∑ R ∈ outside.powerset, ennTerm BU BT R := hpartition_as_terms
    _ =
      ENNReal.ofReal
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            p ^ 2 *
              (((1 - p) + p * a) ^ uOnly.card *
                ((1 - p) + p * b) ^ vBlock.card)) := by
      rw [hsum_ofReal]
      exact congrArg ENNReal.ofReal hreal_eq
