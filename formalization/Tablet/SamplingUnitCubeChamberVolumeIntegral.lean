import Tablet.RandomIndependentSetSampling
import Tablet.SamplingDisjointCoordinateOutsideSliceVolumeBound
import Tablet.SamplingFiniteProductThreeCoordinateSliceIntegralBound

open BigOperators

-- [TABLET NODE: SamplingUnitCubeChamberVolumeIntegral]
theorem SamplingUnitCubeChamberVolumeIntegral
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b c : V)
    (Sx Sy Sz : Finset V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSxQ : Disjoint Sx ({a, b, c} : Finset V))
    (hSyQ : Disjoint Sy ({a, b, c} : Finset V))
    (hSzQ : Disjoint Sz ({a, b, c} : Finset V))
    (hSxy : Disjoint Sx Sy) (hSxz : Disjoint Sx Sz) (hSyz : Disjoint Sy Sz) :
    MeasureTheory.volume
        {q : V → ℝ |
          q a ≤ q b ∧ q b ≤ q c ∧
            (∀ w : V, w ∈ Sx → q w < q a) ∧
              (∀ w : V, w ∈ Sy → q w < q b) ∧
                (∀ w : V, w ∈ Sz → q w < q c) ∧
                  ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} ≤
    ENNReal.ofReal
      (∫ z in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..z,
          ∫ x in (0 : ℝ)..y,
            x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
-- BODY
  let E : Set (V → ℝ) :=
    {q : V → ℝ |
      q a ≤ q b ∧ q b ≤ q c ∧
        (∀ w : V, w ∈ Sx → q w < q a) ∧
          (∀ w : V, w ∈ Sy → q w < q b) ∧
            (∀ w : V, w ∈ Sz → q w < q c) ∧
              ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1}
  change MeasureTheory.volume E ≤
    ENNReal.ofReal
      (∫ z in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..z,
          ∫ x in (0 : ℝ)..y,
            x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)
  refine
    SamplingFiniteProductThreeCoordinateSliceIntegralBound a b c E
      (fun x y z : ℝ => x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)
      hab hac hbc ?_ ?_ ?_ ?_ ?_
  · dsimp [E]
    measurability
  · fun_prop
  · intro x y z hx0 hxy hyz _hz1
    exact
      mul_nonneg
        (mul_nonneg (pow_nonneg hx0 Sx.card)
          (pow_nonneg (hx0.trans hxy) Sy.card))
        (pow_nonneg ((hx0.trans hxy).trans hyz) Sz.card)
  · intro q hq
    rcases hq with ⟨ha_le_b, hb_le_c, _hSx, _hSy, _hSz, hcube⟩
    exact ⟨hcube a, ha_le_b, hb_le_c, hcube c⟩
  · intro x y z hx0 hxy hyz hz1
    simpa [E, and_assoc] using
      SamplingDisjointCoordinateOutsideSliceVolumeBound a b c Sx Sy Sz
        hab hac hbc hSxQ hSyQ hSzQ hSxy hSxz hSyz x y z hx0 hxy hyz hz1
