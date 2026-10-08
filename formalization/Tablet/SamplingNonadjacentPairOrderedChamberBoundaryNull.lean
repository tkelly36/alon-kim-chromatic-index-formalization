import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable
import Tablet.SamplingNonadjacentPairOrderedChamberMass
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open BigOperators
open MeasureTheory Set

set_option maxHeartbeats 1000000

-- [TABLET NODE: SamplingNonadjacentPairOrderedChamberBoundaryNull]
theorem SamplingNonadjacentPairOrderedChamberBoundaryNull
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (u v : V) (uOnly vBlock : Finset V)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (huv : u ≠ v)
    (hu_not : u ∉ uOnly ∪ vBlock)
    (hv_not : v ∉ uOnly ∪ vBlock)
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
    ∀ z : V, z ∈ uOnly ∪ vBlock →
      ν {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧ z ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              (ω.2 z = ω.2 u ∨ ω.2 z = ω.2 v)} = 0 := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  have hpair_volume :
      ∀ {a b : V}, a ≠ b → volume {q : V → ℝ | q a = q b} = 0 := by
    intro a b hab
    let L : (V → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj a : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj b
    let S : Submodule ℝ (V → ℝ) := LinearMap.ker L
    let A : AffineSubspace ℝ (V → ℝ) := S.toAffineSubspace
    have hset : {q : V → ℝ | q a = q b} = A := by
      ext q
      simp [A, S, L, sub_eq_zero]
    rw [hset]
    apply Measure.addHaar_affineSubspace (μ := volume) A
    intro htop
    have hmem :
        (fun x : V => if x = a then (1 : ℝ) else 0) ∈
          (⊤ : AffineSubspace ℝ (V → ℝ)) := by
      simp
    rw [← htop] at hmem
    have hker : L (fun x : V => if x = a then (1 : ℝ) else 0) = 0 := by
      simp [A, S] at hmem
      exact hmem
    have : (1 : ℝ) = 0 := by
      simpa [L, LinearMap.sub_apply, hab, hab.symm] using hker
    norm_num at this
  intro z hz
  have hzu : z ≠ u := by
    intro h
    exact hu_not (by simpa [h] using hz)
  have hzv : z ≠ v := by
    intro h
    exact hv_not (by simpa [h] using hz)
  let E : Set (Finset V × (V → ℝ)) :=
    {ω |
      u ∈ ω.1 ∧ v ∈ ω.1 ∧ z ∈ ω.1 ∧
        (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
          (ω.2 z = ω.2 u ∨ ω.2 z = ω.2 v)}
  let F : Finset V → Set (Finset V × (V → ℝ)) := fun A => {ω | ω.1 = A}
  let C : Set (Finset V × (V → ℝ)) :=
    {ω | ∀ q : V, ω.2 q ∈ Set.Icc (0 : ℝ) 1}
  let D : Set (V → ℝ) := {q | q z = q u ∨ q z = q v}
  have hD_volume : volume D = 0 := by
    have hu0 : volume {q : V → ℝ | q z = q u} = 0 := hpair_volume hzu
    have hv0 : volume {q : V → ℝ | q z = q v} = 0 := hpair_volume hzv
    have hunion :
        volume ({q : V → ℝ | q z = q u} ∪ {q : V → ℝ | q z = q v}) = 0 := by
      exact MeasureTheory.measure_union_null hu0 hv0
    simpa [D, Set.setOf_or] using hunion
  have hboundary_atom_zero :
      ∀ A : Finset V,
        ν ({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) = 0 := by
    intro A
    let CD : Set (V → ℝ) := D ∩ {q | ∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1}
    have hCD_meas : MeasurableSet CD := by
      dsimp [CD, D]
      measurability
    have hCD_cube :
        CD ⊆ {q : V → ℝ | ∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1} := by
      intro q hq
      exact hq.2
    have hfinite_atom : ν {ω | ω.1 = A} ≠ ⊤ := by
      rw [hν_atom A]
      exact ENNReal.ofReal_ne_top
    have hdom :
        ν ({ω | ω.1 = A ∧ ω.2 ∈ CD} ∩
            {ω | ∀ x : V, ω.2 x ∈ Set.Icc (0 : ℝ) 1}) ≤
          ν {ω | ω.1 = A} * volume CD := by
      exact le_of_eq
        (SamplingFiniteProductLowerOrthantEqualityMeasurable
          (ν := ν) (F := fun ω : Finset V × (V → ℝ) => ω.1 = A)
          (p := fun ω : Finset V × (V → ℝ) => ω.2)
          (hp_meas := measurable_snd)
          (M := ν {ω | ω.1 = A}) (C := CD) hCD_meas hCD_cube
          hfinite_atom rfl (hν_rect A))
    have hvol_CD : volume CD = 0 := by
      exact measure_mono_null (by intro q hq; exact hq.1) hD_volume
    have hset :
        ({ω | ω.1 = A ∧ ω.2 ∈ CD} ∩
            {ω | ∀ x : V, ω.2 x ∈ Set.Icc (0 : ℝ) 1}) =
          ({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) := by
      ext ω
      simp [CD, C, and_assoc, and_left_comm, and_comm]
    have hle_zero : ν (({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C)) ≤ 0 := by
      rw [← hset]
      simpa [hvol_CD] using hdom
    exact le_antisymm hle_zero bot_le
  have hatom_diff_zero : ∀ A : Finset V, ν (F A \ (F A ∩ C)) = 0 := by
    intro A
    have hFC_subset : F A ∩ C ⊆ F A := by
      intro ω hω
      exact hω.1
    have hFC_eq : ν (F A ∩ C) = ν (F A) := by
      have hrect_one := hν_rect A (fun _ : V => (1 : ℝ)) (by intro q; simp)
      have hset :
          {ω : Finset V × (V → ℝ) |
              ω.1 = A ∧ ∀ q : V, 0 ≤ ω.2 q ∧ ω.2 q ≤ (fun _ : V => (1 : ℝ)) q} =
            F A ∩ C := by
        ext ω
        simp [F, C, Set.mem_Icc]
      calc
        ν (F A ∩ C) =
            ν {ω : Finset V × (V → ℝ) |
              ω.1 = A ∧ ∀ q : V, 0 ≤ ω.2 q ∧ ω.2 q ≤ (fun _ : V => (1 : ℝ)) q} := by
          rw [hset]
        _ = ν (F A) := by
          simpa using hrect_one
    have hFC_finite : ν (F A ∩ C) ≠ ⊤ := by
      rw [hFC_eq]
      rw [hν_atom A]
      exact ENNReal.ofReal_ne_top
    rw [MeasureTheory.measure_diff hFC_subset
      (show MeasureTheory.NullMeasurableSet (F A ∩ C) ν from by
        exact (by
          dsimp [F, C]
          measurability : MeasurableSet (F A ∩ C)).nullMeasurableSet)
      hFC_finite]
    rw [hFC_eq]
    exact tsub_self _
  have hE_atom_zero : ∀ A : Finset V, ν (E ∩ F A) = 0 := by
    intro A
    have hsubset :
        E ∩ F A ⊆ ({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) ∪ (F A \ (F A ∩ C)) := by
      intro ω hω
      by_cases hωC : ω ∈ C
      · left
        refine ⟨?_, hωC⟩
        exact ⟨hω.2, by simpa [D] using hω.1.2.2.2.2⟩
      · right
        exact ⟨hω.2, by
          intro hFC
          exact hωC hFC.2⟩
    have hunion_zero :
        ν (({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) ∪ (F A \ (F A ∩ C))) = 0 := by
      exact MeasureTheory.measure_union_null (hboundary_atom_zero A) (hatom_diff_zero A)
    exact MeasureTheory.measure_mono_null hsubset hunion_zero
  have hE_cover : E ⊆ ⋃ A : Finset V, E ∩ F A := by
    intro ω hω
    refine Set.mem_iUnion.mpr ⟨ω.1, ?_⟩
    exact ⟨hω, rfl⟩
  have hE_null : ν (⋃ A : Finset V, E ∩ F A) = 0 := by
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro A
    exact hE_atom_zero A
  have htarget_eq :
      {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧ z ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              (ω.2 z = ω.2 u ∨ ω.2 z = ω.2 v)} = E := rfl
  rw [htarget_eq]
  exact MeasureTheory.measure_mono_null hE_cover hE_null
