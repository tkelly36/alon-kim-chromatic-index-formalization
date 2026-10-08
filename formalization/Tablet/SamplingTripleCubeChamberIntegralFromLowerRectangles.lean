import Tablet.RandomIndependentSetSampling
import Tablet.SamplingAbstractLowerRectangleChamberBound

open BigOperators

-- [TABLET NODE: SamplingTripleCubeChamberIntegralFromLowerRectangles]
theorem SamplingTripleCubeChamberIntegralFromLowerRectangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (gamma : ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (a b c : V)
    (Sx Sy Sz : Finset V)
    (hgamma_pos : 0 < gamma)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSxQ : Disjoint Sx ({a, b, c} : Finset V))
    (hSyQ : Disjoint Sy ({a, b, c} : Finset V))
    (hSzQ : Disjoint Sz ({a, b, c} : Finset V))
    (hSxy : Disjoint Sx Sy) (hSxz : Disjoint Sx Sz) (hSyz : Disjoint Sy Sz)
    (hfinite_atom : ν {ω | ω.1 = A} ≠ ⊤)
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
            ν {ω | ω.1 = A} *
              ENNReal.ofReal (∏ v : V, t v)) :
    ν ({ω |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            (∀ w : V, w ∈ Sx → ω.2 w < ω.2 a) ∧
              (∀ w : V, w ∈ Sy → ω.2 w < ω.2 b) ∧
                ∀ w : V, w ∈ Sz → ω.2 w < ω.2 c} ∩
        {ω | ∀ v : V, ω.2 v ∈ Set.Icc (0 : ℝ) 1}) ≤
    ν {ω | ω.1 = A} *
        ENNReal.ofReal
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^ Sx.card *
                      (1 - y / gamma) ^ Sy.card *
                      (1 - z / gamma) ^ Sz.card) := by
-- BODY
  simpa using
    SamplingAbstractLowerRectangleChamberBound
      (gamma := gamma) (ν := ν) (F := fun ω => ω.1 = A) (p := fun ω => ω.2)
      (M := ν {ω | ω.1 = A}) (a := a) (b := b) (c := c)
      (Sx := Sx) (Sy := Sy) (Sz := Sz) hgamma_pos hab hac hbc
      hSxQ hSyQ hSzQ hSxy hSxz hSyz hfinite_atom rfl hlower_rect
