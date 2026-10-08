import Tablet.SamplingTripleProductChamberIntegralFiniteFiber
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open BigOperators

-- [TABLET NODE: SamplingTripleProductChamberIntegral]
theorem SamplingTripleProductChamberIntegral
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
  by_cases hfinite_atom : ν {ω | ω.1 = A} ≠ ⊤
  · exact
      SamplingTripleProductChamberIntegralFiniteFiber
        (gamma := gamma) (ν := ν) (A := A) (a := a) (b := b) (c := c)
        (Sx := Sx) (Sy := Sy) (Sz := Sz) hgamma_pos hab hac hbc
        hSxQ hSyQ hSzQ hSxy hSxz hSyz hfinite_atom hcube hlower_rect
  · have htop_atom : ν {ω | ω.1 = A} = ⊤ := by
      by_contra hne
      exact hfinite_atom hne
    have hpow_pos (u : ℝ) (hu : u < gamma) :
        0 < 1 - u / gamma := by
      have hdiv_lt : u / gamma < 1 := by
        rw [div_lt_one hgamma_pos]
        exact hu
      linarith
    have hinner_cont :
        Continuous fun zy : ℝ × ℝ =>
          ∫ x in zy.2..gamma,
            (1 - x / gamma) ^ Sx.card *
              (1 - zy.2 / gamma) ^ Sy.card *
                (1 - zy.1 / gamma) ^ Sz.card := by
      have hcont :
          Continuous fun zy : ℝ × ℝ =>
            ∫ x in gamma..zy.2,
              (1 - x / gamma) ^ Sx.card *
                (1 - zy.2 / gamma) ^ Sy.card *
                  (1 - zy.1 / gamma) ^ Sz.card := by
        let f : (ℝ × ℝ) → ℝ → ℝ := fun zy x =>
          (1 - x / gamma) ^ Sx.card *
            (1 - zy.2 / gamma) ^ Sy.card *
              (1 - zy.1 / gamma) ^ Sz.card
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := f) (a₀ := gamma)
          (s := fun zy : ℝ × ℝ => zy.2)
          (by
            dsimp [f, Function.uncurry]
            fun_prop)
          (by fun_prop)
      convert hcont.neg using 1
      ext zy
      rw [intervalIntegral.integral_symm]
    have hmid_cont :
        Continuous fun z : ℝ =>
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card := by
      have hcont :
          Continuous fun z : ℝ =>
            ∫ y in gamma..z,
              ∫ x in y..gamma,
                (1 - x / gamma) ^ Sx.card *
                  (1 - y / gamma) ^ Sy.card *
                    (1 - z / gamma) ^ Sz.card := by
        let f : ℝ → ℝ → ℝ := fun z y =>
          ∫ x in y..gamma,
            (1 - x / gamma) ^ Sx.card *
              (1 - y / gamma) ^ Sy.card *
                (1 - z / gamma) ^ Sz.card
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := f) (a₀ := gamma)
          (s := fun z : ℝ => z)
          (by
            dsimp [f, Function.uncurry]
            simpa using hinner_cont)
          (by fun_prop)
      convert hcont.neg using 1
      ext z
      rw [intervalIntegral.integral_symm]
    have hinner_pos (z y : ℝ) (hy : y < gamma) (hzy : z < y) :
        0 <
          ∫ x in y..gamma,
            (1 - x / gamma) ^ Sx.card *
              (1 - y / gamma) ^ Sy.card *
                (1 - z / gamma) ^ Sz.card := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hy
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · intro x hx
        have hxpos : 0 < 1 - x / gamma := hpow_pos x hx.2
        have hypos : 0 < 1 - y / gamma := hpow_pos y hy
        have hzpos : 0 < 1 - z / gamma := hpow_pos z (by linarith)
        positivity
    have hmid_pos (z : ℝ) (hz : z < gamma) :
        0 <
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hz
      · exact (hinner_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      · intro y hy
        exact hinner_pos z y hy.2 hy.1
    have hfactor_pos :
        0 <
          (1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^ Sx.card *
                    (1 - y / gamma) ^ Sy.card *
                      (1 - z / gamma) ^ Sz.card := by
      have houter_pos :
          0 <
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^ Sx.card *
                    (1 - y / gamma) ^ Sy.card *
                      (1 - z / gamma) ^ Sz.card := by
        refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hgamma_pos
        · exact hmid_cont.intervalIntegrable _ _
        · intro z hz
          exact hmid_pos z hz.2
      positivity
    have hfactor_ne :
        ENNReal.ofReal
            ((1 / gamma ^ 3) *
              ∫ z in (0 : ℝ)..gamma,
                ∫ y in z..gamma,
                  ∫ x in y..gamma,
                    (1 - x / gamma) ^ Sx.card *
                      (1 - y / gamma) ^ Sy.card *
                        (1 - z / gamma) ^ Sz.card) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hfactor_pos).ne'
    rw [htop_atom, ENNReal.top_mul hfactor_ne]
    exact le_top
