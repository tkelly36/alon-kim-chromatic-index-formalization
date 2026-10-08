import Tablet.RandomIndependentSetSampling
import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable

open BigOperators

-- [TABLET NODE: SamplingUnitCubeLowerRectangleChamberDomination]
theorem SamplingUnitCubeLowerRectangleChamberDomination
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
      MeasureTheory.volume
        {q : V → ℝ |
          q a ≤ q b ∧ q b ≤ q c ∧
            (∀ w : V, w ∈ Sx → q w < q a) ∧
              (∀ w : V, w ∈ Sy → q w < q b) ∧
                (∀ w : V, w ∈ Sz → q w < q c) ∧
                  ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} := by
-- BODY
  letI : MeasurableSpace Ω := ⊤
  let C : Set (V → ℝ) :=
    {q : V → ℝ |
      q a ≤ q b ∧ q b ≤ q c ∧
        (∀ w : V, w ∈ Sx → q w < q a) ∧
          (∀ w : V, w ∈ Sy → q w < q b) ∧
            (∀ w : V, w ∈ Sz → q w < q c) ∧
              ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1}
  have hC_meas : MeasurableSet C := by
    dsimp [C]
    measurability
  have hC_cube : C ⊆ {q : V → ℝ | ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} := by
    intro q hq
    rcases hq with ⟨_, _, _, _, _, hcube⟩
    exact hcube
  have hdom :=
    (SamplingFiniteProductLowerOrthantEqualityMeasurable ν F p measurable_from_top
      M C hC_meas hC_cube hfinite_atom hM hlower_rect).le
  have hset :
      ({ω |
          F ω ∧
            p ω a ≤ p ω b ∧ p ω b ≤ p ω c ∧
              (∀ w : V, w ∈ Sx → p ω w < p ω a) ∧
                (∀ w : V, w ∈ Sy → p ω w < p ω b) ∧
                  ∀ w : V, w ∈ Sz → p ω w < p ω c} ∩
        {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}) =
      ({ω | F ω ∧ p ω ∈ C} ∩
        {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}) := by
    ext ω
    simp [C, and_assoc, and_left_comm, and_comm]
  rw [hset]
  simpa [C, and_assoc, and_left_comm, and_comm] using hdom
