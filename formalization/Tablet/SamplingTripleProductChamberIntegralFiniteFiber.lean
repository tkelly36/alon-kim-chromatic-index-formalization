import Tablet.SamplingFiniteFiberFullCubeRestrictionBound
import Tablet.SamplingTripleCubeChamberIntegralFromLowerRectangles

open BigOperators

-- [TABLET NODE: SamplingTripleProductChamberIntegralFiniteFiber]
theorem SamplingTripleProductChamberIntegralFiniteFiber
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
    (hcube :
      ν {ω |
        ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
            ν {ω | ω.1 = A} *
              ENNReal.ofReal (∏ v : V, t v)) :
    ν {ω |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            (∀ w : V, w ∈ Sx → ω.2 w < ω.2 a) ∧
              (∀ w : V, w ∈ Sy → ω.2 w < ω.2 b) ∧
                ∀ w : V, w ∈ Sz → ω.2 w < ω.2 c} ≤
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
  classical
  let F : Set (Finset V × (V → ℝ)) := {ω | ω.1 = A}
  let C : Set (Finset V × (V → ℝ)) := {ω | ∀ v : V, ω.2 v ∈ Set.Icc (0 : ℝ) 1}
  let E : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
          (∀ w : V, w ∈ Sx → ω.2 w < ω.2 a) ∧
            (∀ w : V, w ∈ Sy → ω.2 w < ω.2 b) ∧
              ∀ w : V, w ∈ Sz → ω.2 w < ω.2 c}
  let B : ENNReal :=
    ν {ω | ω.1 = A} *
      ENNReal.ofReal
        ((1 / gamma ^ 3) *
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma,
                (1 - x / gamma) ^ Sx.card *
                  (1 - y / gamma) ^ Sy.card *
                    (1 - z / gamma) ^ Sz.card)
  have hE_sub_F : E ⊆ F := by
    intro ω hω
    exact hω.1
  have hone_mem : ∀ v : V, (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro v
    exact ⟨by norm_num, le_rfl⟩
  have hprod_one : (∏ v : V, (1 : ℝ)) = 1 := by
    simp
  have hfull : ν (F ∩ C) = ν F := by
    have hrect_one := hlower_rect (fun _ : V => (1 : ℝ)) hone_mem
    have hrect_one' :
        ν {ω |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ (fun _ : V => (1 : ℝ)) v} =
          ν {ω | ω.1 = A} := by
      simpa [hprod_one] using hrect_one
    simpa [F, C, Set.ext_iff, and_assoc] using hrect_one'
  have hcube_bound : ν (E ∩ C) ≤ B := by
    simpa [E, C, B] using
      SamplingTripleCubeChamberIntegralFromLowerRectangles
        (gamma := gamma) (ν := ν) (A := A) (a := a) (b := b) (c := c)
        (Sx := Sx) (Sy := Sy) (Sz := Sz) hgamma_pos hab hac hbc
        hSxQ hSyQ hSzQ hSxy hSxz hSyz hfinite_atom hlower_rect
  simpa [E, F, C, B] using
    SamplingFiniteFiberFullCubeRestrictionBound (ν := ν) (F := F) (C := C)
      (E := E) (B := B) hE_sub_F hfinite_atom hfull hcube_bound
