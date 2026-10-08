import Tablet.SamplingOneVertexPriorityRectangle

open BigOperators

-- [TABLET NODE: SamplingOneVertexPrioritySliceExact]
theorem SamplingOneVertexPrioritySliceExact {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (v : V) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hab : a ≤ b)
    (hfinite_atom : ν {ω | ω.1 = A} ≠ ⊤)
    (hrect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ u : V, t u ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧
            ∀ u : V, 0 ≤ ω.2 u ∧ ω.2 u ≤ t u} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ u : V, t u)) :
    ν {ω |
      ω.1 = A ∧
        a < ω.2 v ∧
          ω.2 v ≤ b ∧
            ∀ u : V, 0 ≤ ω.2 u ∧
              ω.2 u ≤ if u = v then b else if u ∈ A ∧ G.Adj v u then a else 1} =
      ν {ω | ω.1 = A} *
          ENNReal.ofReal
            (b * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) -
        ν {ω | ω.1 = A} *
          ENNReal.ofReal
            (a * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
-- BODY
  classical
  let Rb : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        ∀ u : V, 0 ≤ ω.2 u ∧
          ω.2 u ≤ if u = v then b else if u ∈ A ∧ G.Adj v u then a else 1}
  let Ra : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        ∀ u : V, 0 ≤ ω.2 u ∧
          ω.2 u ≤ if u = v then a else if u ∈ A ∧ G.Adj v u then a else 1}
  have hRa_subset_Rb : Ra ⊆ Rb := by
    intro ω hω
    rcases hω with ⟨hA, hcoord⟩
    refine ⟨hA, ?_⟩
    intro u
    specialize hcoord u
    rcases hcoord with ⟨h0, hle⟩
    refine ⟨h0, ?_⟩
    by_cases huv : u = v
    · simp [huv] at hle ⊢
      exact hle.trans hab
    · simp [huv] at hle ⊢
      exact hle
  have hslice_eq : {ω |
      ω.1 = A ∧
        a < ω.2 v ∧
          ω.2 v ≤ b ∧
            ∀ u : V, 0 ≤ ω.2 u ∧
              ω.2 u ≤ if u = v then b else if u ∈ A ∧ G.Adj v u then a else 1} =
      Rb \ Ra := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hA, hav, _hbv, hcoord⟩
      refine ⟨⟨hA, hcoord⟩, ?_⟩
      intro hRa
      have hva : ω.2 v ≤ a := by
        simpa using (hRa.2 v).2
      exact not_le_of_gt hav hva
    · intro hω
      rcases hω with ⟨hRb, hnotRa⟩
      rcases hRb with ⟨hA, hcoord⟩
      have hbv : ω.2 v ≤ b := by
        simpa using (hcoord v).2
      have hav : a < ω.2 v := by
        by_contra hle_not
        have hva : ω.2 v ≤ a := le_of_not_gt hle_not
        apply hnotRa
        refine ⟨hA, ?_⟩
        intro u
        specialize hcoord u
        rcases hcoord with ⟨h0, hle⟩
        refine ⟨h0, ?_⟩
        by_cases huv : u = v
        · simpa [huv] using hva
        · simpa [huv] using hle
      exact ⟨hA, hav, hbv, hcoord⟩
  have hRb :
      ν Rb =
        ν {ω | ω.1 = A} *
          ENNReal.ofReal
            (b * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
    simpa [Rb] using
      SamplingOneVertexPriorityRectangle G ν A v a b ha0 ha1 hb0 hb1 hrect
  have hRa :
      ν Ra =
        ν {ω | ω.1 = A} *
          ENNReal.ofReal
            (a * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
    simpa [Ra] using
      SamplingOneVertexPriorityRectangle G ν A v a a ha0 ha1 ha0 ha1 hrect
  have hRa_ne_top : ν Ra ≠ ⊤ := by
    rw [hRa]
    exact ENNReal.mul_ne_top hfinite_atom ENNReal.ofReal_ne_top
  have hnull_Ra : @MeasureTheory.NullMeasurableSet (Finset V × (V → ℝ)) ⊤ Ra ν := by
    simp
  rw [hslice_eq]
  rw [@MeasureTheory.measure_diff (Finset V × (V → ℝ)) ⊤ ν Rb Ra hRa_subset_Rb
    hnull_Ra hRa_ne_top]
  rw [hRb, hRa]
