import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingPriorityProjectionVolumeNull
import Tablet.SamplingNonadjacentPairOrderedChamberMass
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open BigOperators
open MeasureTheory Set

-- [TABLET NODE: SamplingNonadjacentPairOrderedChamberDiagonalNull]
theorem SamplingNonadjacentPairOrderedChamberDiagonalNull
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (u v : V)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (huv : u ≠ v)
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
            ω.2 u = ω.2 v} = 0 := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let D : Set (V → ℝ) := {q | q u = q v}
  have hD_volume : volume D = 0 := by
    let L : (V → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj u : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj v
    let S : Submodule ℝ (V → ℝ) := LinearMap.ker L
    let A : AffineSubspace ℝ (V → ℝ) := S.toAffineSubspace
    have hset : D = A := by
      ext q
      simp [D, A, S, L, sub_eq_zero]
    rw [hset]
    apply Measure.addHaar_affineSubspace (μ := volume) A
    intro htop
    have hmem :
        (fun x : V => if x = u then (1 : ℝ) else 0) ∈
          (⊤ : AffineSubspace ℝ (V → ℝ)) := by
      simp
    rw [← htop] at hmem
    have hker : L (fun x : V => if x = u then (1 : ℝ) else 0) = 0 := by
      simp [A, S] at hmem
      exact hmem
    have : (1 : ℝ) = 0 := by
      simpa [L, LinearMap.sub_apply, huv, huv.symm] using hker
    norm_num at this
  have hnull := SamplingPriorityProjectionVolumeNull ν
    (fun A => by rw [hν_atom A]; exact ENNReal.ofReal_ne_top)
    hν_rect D (by dsimp [D]; measurability) hD_volume
  exact measure_mono_null (by
    intro ω hω
    exact hω.2.2.2) hnull
