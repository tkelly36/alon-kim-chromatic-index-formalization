import Tablet.RandomIndependentSetSampling
import Tablet.SamplingUnitCubeChamberVolumeIntegral
import Tablet.SamplingUnitCubeLowerRectangleChamberDomination

open BigOperators

-- [TABLET NODE: SamplingUnitCubeLowerRectangleChamberBound]
theorem SamplingUnitCubeLowerRectangleChamberBound
    {Ω V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure Ω ⊤)
    (F : Ω → Prop) (p : Ω → V → ℝ)
    (M : ENNReal)
    (a b c : V)
    (Sx Sy Sz : Finset V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSxQ : Disjoint Sx ({a, b, c} : Finset V))
    (hSyQ : Disjoint Sy ({a, b, c} : Finset V))
    (hSzQ : Disjoint Sz ({a, b, c} : Finset V))
    (hSxy : Disjoint Sx Sy) (hSxz : Disjoint Sx Sz) (hSyz : Disjoint Sy Sz)
    (hfinite_atom : ν {ω | F ω} ≠ ⊤)
    (hM : M = ν {ω | F ω})
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            F ω ∧
              ∀ v : V, 0 ≤ p ω v ∧ p ω v ≤ t v} =
            M * ENNReal.ofReal (∏ v : V, t v)) :
    ν ({ω |
        F ω ∧
          p ω a ≤ p ω b ∧ p ω b ≤ p ω c ∧
            (∀ w : V, w ∈ Sx → p ω w < p ω a) ∧
              (∀ w : V, w ∈ Sy → p ω w < p ω b) ∧
                ∀ w : V, w ∈ Sz → p ω w < p ω c} ∩
        {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}) ≤
    M *
        ENNReal.ofReal
          (∫ z in (0 : ℝ)..1,
            ∫ y in (0 : ℝ)..z,
              ∫ x in (0 : ℝ)..y,
                x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
-- BODY
  calc
    ν ({ω |
        F ω ∧
          p ω a ≤ p ω b ∧ p ω b ≤ p ω c ∧
            (∀ w : V, w ∈ Sx → p ω w < p ω a) ∧
              (∀ w : V, w ∈ Sy → p ω w < p ω b) ∧
                ∀ w : V, w ∈ Sz → p ω w < p ω c} ∩
        {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}) ≤
      M *
        MeasureTheory.volume
          {q : V → ℝ |
            q a ≤ q b ∧ q b ≤ q c ∧
              (∀ w : V, w ∈ Sx → q w < q a) ∧
                (∀ w : V, w ∈ Sy → q w < q b) ∧
                  (∀ w : V, w ∈ Sz → q w < q c) ∧
                    ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} := by
        exact
          SamplingUnitCubeLowerRectangleChamberDomination ν F p M a b c Sx Sy Sz
            hab hac hbc hSxQ hSyQ hSzQ hSxy hSxz hSyz hfinite_atom hM
            hlower_rect
    _ ≤ M *
        ENNReal.ofReal
          (∫ z in (0 : ℝ)..1,
            ∫ y in (0 : ℝ)..z,
              ∫ x in (0 : ℝ)..y,
                x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
        calc
          M *
              MeasureTheory.volume
                {q : V → ℝ |
                  q a ≤ q b ∧ q b ≤ q c ∧
                    (∀ w : V, w ∈ Sx → q w < q a) ∧
                      (∀ w : V, w ∈ Sy → q w < q b) ∧
                        (∀ w : V, w ∈ Sz → q w < q c) ∧
                          ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} =
            MeasureTheory.volume
                {q : V → ℝ |
                  q a ≤ q b ∧ q b ≤ q c ∧
                    (∀ w : V, w ∈ Sx → q w < q a) ∧
                      (∀ w : V, w ∈ Sy → q w < q b) ∧
                        (∀ w : V, w ∈ Sz → q w < q c) ∧
                          ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} * M := by
              rw [mul_comm]
          _ ≤
            ENNReal.ofReal
                (∫ z in (0 : ℝ)..1,
                  ∫ y in (0 : ℝ)..z,
                    ∫ x in (0 : ℝ)..y,
                      x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) * M := by
              exact mul_left_mono
                (SamplingUnitCubeChamberVolumeIntegral a b c Sx Sy Sz
                  hab hac hbc hSxQ hSyQ hSzQ hSxy hSxz hSyz)
          _ =
            M *
              ENNReal.ofReal
                (∫ z in (0 : ℝ)..1,
                  ∫ y in (0 : ℝ)..z,
                    ∫ x in (0 : ℝ)..y,
                      x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
              rw [mul_comm]
