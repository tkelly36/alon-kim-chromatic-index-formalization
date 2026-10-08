import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingPriorityProjectionVolumeNull
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
  let D : Set (V → ℝ) := {q | q z = q u ∨ q z = q v}
  have hD_volume : volume D = 0 := by
    have hu0 : volume {q : V → ℝ | q z = q u} = 0 := hpair_volume hzu
    have hv0 : volume {q : V → ℝ | q z = q v} = 0 := hpair_volume hzv
    have hunion :
        volume ({q : V → ℝ | q z = q u} ∪ {q : V → ℝ | q z = q v}) = 0 := by
      exact MeasureTheory.measure_union_null hu0 hv0
    simpa [D, Set.setOf_or] using hunion
  have hnull := SamplingPriorityProjectionVolumeNull ν
    (fun A => by rw [hν_atom A]; exact ENNReal.ofReal_ne_top)
    hν_rect D (by dsimp [D]; measurability) hD_volume
  exact measure_mono_null (by
    intro ω hω
    exact hω.2.2.2.2) hnull
