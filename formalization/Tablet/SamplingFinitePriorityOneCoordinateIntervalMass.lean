import Tablet.SamplingFinitePriorityCutProductFormula

open BigOperators

-- [TABLET NODE: SamplingFinitePriorityOneCoordinateIntervalMass]
theorem SamplingFinitePriorityOneCoordinateIntervalMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (A : Finset V) (z : V) (a b : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hν_atom : ∀ A0 : Finset V,
      ν {ω | ω.1 = A0} =
        ENNReal.ofReal
          (p ^ A0.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A0.card)))
    (hν_rect : ∀ A0 : Finset V, ∀ s : V → ℝ,
      (∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A0 ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} =
          ν {ω | ω.1 = A0} * ENNReal.ofReal (∏ v : V, s v)) :
    ν {ω |
        ω.1 = A ∧
          (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
            a < ω.2 z ∧ ω.2 z ≤ b} =
      ENNReal.ofReal
        (p ^ A.card *
          (1 - p) ^ ((Finset.univ : Finset V).card - A.card) * (b - a)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let tb : V → ℝ := fun v => if v = z then b else 1
  let ta : V → ℝ := fun v => if v = z then a else 1
  have hb0 : 0 ≤ b := ha0.trans hab
  have htb0 : ∀ v : V, v ∈ ({z} : Finset V) ∪ (∅ : Finset V) → 0 ≤ tb v := by
    intro v hv
    have hvz : v = z := by simpa using hv
    simp [tb, hvz, hb0]
  have htb1 : ∀ v : V, v ∈ ({z} : Finset V) ∪ (∅ : Finset V) → tb v ≤ 1 := by
    intro v hv
    have hvz : v = z := by simpa using hv
    simp [tb, hvz, hb1]
  have hta0 : ∀ v : V, v ∈ ({z} : Finset V) ∪ (∅ : Finset V) → 0 ≤ ta v := by
    intro v hv
    have hvz : v = z := by simpa using hv
    simp [ta, hvz, ha0]
  have hta1 : ∀ v : V, v ∈ ({z} : Finset V) ∪ (∅ : Finset V) → ta v ≤ 1 := by
    intro v hv
    have hvz : v = z := by simpa using hv
    simp [ta, hvz, hab.trans hb1]
  let Eb : Set (Finset V × (V → ℝ)) :=
    {ω | ω.1 = A ∧ (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧ ω.2 z ≤ b}
  let Ea : Set (Finset V × (V → ℝ)) :=
    {ω | ω.1 = A ∧ (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧ ω.2 z ≤ a}
  have hEb : ν Eb =
      ENNReal.ofReal
        (p ^ A.card * (1 - p) ^ ((Finset.univ : Finset V).card - A.card) * b) := by
    have h := SamplingFinitePriorityCutProductFormula (ν := ν) (p := p) (A := A)
      (L := ({z} : Finset V)) (U := ∅) (t := tb) hp0 hp1 (by simp)
      htb0 htb1 hν_atom hν_rect
    have hset :
        {ω : Finset V × (V → ℝ) |
          ω.1 = A ∧
            (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
              (∀ v : V, v ∈ ({z} : Finset V) → ω.2 v ≤ tb v) ∧
                ∀ v : V, v ∈ (∅ : Finset V) → tb v < ω.2 v} = Eb := by
      ext ω
      simp [Eb, tb]
    rw [← hset]
    simpa [tb] using h
  have hEa : ν Ea =
      ENNReal.ofReal
        (p ^ A.card * (1 - p) ^ ((Finset.univ : Finset V).card - A.card) * a) := by
    have h := SamplingFinitePriorityCutProductFormula (ν := ν) (p := p) (A := A)
      (L := ({z} : Finset V)) (U := ∅) (t := ta) hp0 hp1 (by simp)
      hta0 hta1 hν_atom hν_rect
    have hset :
        {ω : Finset V × (V → ℝ) |
          ω.1 = A ∧
            (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
              (∀ v : V, v ∈ ({z} : Finset V) → ω.2 v ≤ ta v) ∧
                ∀ v : V, v ∈ (∅ : Finset V) → ta v < ω.2 v} = Ea := by
      ext ω
      simp [Ea, ta]
    rw [← hset]
    simpa [ta] using h
  have hsubset : Ea ⊆ Eb := by
    intro ω hω
    exact ⟨hω.1, hω.2.1, hω.2.2.trans hab⟩
  have hEa_ne_top : ν Ea ≠ ⊤ := by
    rw [hEa]
    exact ENNReal.ofReal_ne_top
  have hdiff :
      {ω : Finset V × (V → ℝ) |
        ω.1 = A ∧
          (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
            a < ω.2 z ∧ ω.2 z ≤ b} =
        Eb \ Ea := by
    ext ω
    constructor
    · intro hω
      exact
        ⟨⟨hω.1, hω.2.1, hω.2.2.2⟩, by
          intro ha
          exact not_le_of_gt hω.2.2.1 ha.2.2⟩
    · intro hω
      refine ⟨hω.1.1, hω.1.2.1, ?_, hω.1.2.2⟩
      by_contra hnot
      exact hω.2 ⟨hω.1.1, hω.1.2.1, le_of_not_gt hnot⟩
  rw [hdiff]
  rw [MeasureTheory.measure_diff hsubset
    (show MeasureTheory.NullMeasurableSet Ea ν from by
      exact (by
        dsimp [Ea]
        measurability : MeasurableSet Ea).nullMeasurableSet)
    hEa_ne_top]
  rw [hEb, hEa]
  have atom_nonneg :
      0 ≤ p ^ A.card * (1 - p) ^ ((Finset.univ : Finset V).card - A.card) := by
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  rw [← ENNReal.ofReal_sub _ (mul_nonneg atom_nonneg ha0)]
  congr 1
  ring
