import Tablet.RandomIndependentSetSampling
import Tablet.SamplingUnitCubeLowerRectangleChamberBound
import Tablet.SamplingTripleChamberAffineIntegralIdentity

open BigOperators

-- [TABLET NODE: SamplingAbstractLowerRectangleChamberBound]
theorem SamplingAbstractLowerRectangleChamberBound
    {Ω V : Type*} [Fintype V] [DecidableEq V]
    (gamma : ℝ)
    (ν : @MeasureTheory.Measure Ω ⊤)
    (F : Ω → Prop) (p : Ω → V → ℝ)
    (M : ENNReal)
    (a b c : V)
    (Sx Sy Sz : Finset V)
    (hgamma_pos : 0 < gamma)
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
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^ Sx.card *
                    (1 - y / gamma) ^ Sy.card *
                      (1 - z / gamma) ^ Sz.card) := by
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
          ENNReal.ofReal
            (∫ z in (0 : ℝ)..1,
              ∫ y in (0 : ℝ)..z,
                ∫ x in (0 : ℝ)..y,
                  x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
        exact
          SamplingUnitCubeLowerRectangleChamberBound ν F p M a b c Sx Sy Sz
            hab hac hbc hSxQ hSyQ hSzQ hSxy hSxz hSyz hfinite_atom hM
            hlower_rect
    _ =
      M *
          ENNReal.ofReal
            ((1 / gamma ^ 3) *
              ∫ z in (0 : ℝ)..gamma,
                ∫ y in z..gamma,
                  ∫ x in y..gamma,
                    (1 - x / gamma) ^ Sx.card *
                      (1 - y / gamma) ^ Sy.card *
                        (1 - z / gamma) ^ Sz.card) := by
        rw [SamplingTripleChamberAffineIntegralIdentity gamma Sx Sy Sz hgamma_pos]
