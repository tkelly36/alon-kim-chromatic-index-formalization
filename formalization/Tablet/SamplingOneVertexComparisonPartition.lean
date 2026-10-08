import Tablet.SamplingOneVertexOutputMembership

open BigOperators

set_option maxHeartbeats 800000

-- [TABLET NODE: SamplingOneVertexComparisonPartition]
theorem SamplingOneVertexComparisonPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (v : V)
    (hνuniv : ν Set.univ = 1)
    (hcube : ∀ A : Finset V,
      ν {ω | ω.1 = A ∧ ∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hcompare : ∀ A : Finset V, v ∈ A →
      ν {ω |
        ω.1 = A ∧
          (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
            ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
        ν {ω | ω.1 = A} *
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1,
              a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))) :
    ν {ω |
        v ∈
          (Finset.univ.filter fun u : V =>
            u ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u)} =
      ∑ A : Finset V,
        if v ∈ A then
          ν {ω | ω.1 = A} *
            ENNReal.ofReal
              (∫ a in (0 : ℝ)..1,
                a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
        else 0 := by
-- BODY
  classical
  let T : Finset (Finset V) := Finset.univ.filter fun A : Finset V => v ∈ A
  let raw : Finset V → Set (Finset V × (V → ℝ)) := fun A =>
    {ω | ω.1 = A ∧ ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v}
  let cube : Finset V → Set (Finset V × (V → ℝ)) := fun A =>
    {ω | ω.1 = A ∧ ∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1}
  let comp : Finset V → Set (Finset V × (V → ℝ)) := fun A =>
    {ω |
      ω.1 = A ∧
        (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v}
  have hcube_subset (A : Finset V) : cube A ⊆ {ω | ω.1 = A} := by
    intro ω hω
    exact hω.1
  have hcomp_subset_raw (A : Finset V) : comp A ⊆ raw A := by
    intro ω hω
    exact ⟨hω.1, hω.2.2⟩
  have hraw_diff_subset (A : Finset V) : raw A \ comp A ⊆ {ω | ω.1 = A} \ cube A := by
    intro ω hω
    rcases hω with ⟨hrawω, hnotcomp⟩
    refine ⟨hrawω.1, ?_⟩
    intro hcubeω
    exact hnotcomp ⟨hrawω.1, hcubeω.2, hrawω.2⟩
  have hatom_finite (A : Finset V) : ν {ω | ω.1 = A} ≠ ⊤ := by
    have hle : ν {ω : Finset V × (V → ℝ) | ω.1 = A} ≤ ν Set.univ := by
      exact MeasureTheory.measure_mono (by intro ω _hω; trivial)
    rw [hνuniv] at hle
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hcube_finite (A : Finset V) : ν (cube A) ≠ ⊤ := by
    rw [hcube A]
    exact hatom_finite A
  have hcube_diff_null (A : Finset V) : ν ({ω | ω.1 = A} \ cube A) = 0 := by
    rw [MeasureTheory.measure_diff (hcube_subset A) (by simp [cube]) (hcube_finite A)]
    rw [hcube A]
    exact tsub_self _
  have hraw_eq_comp (A : Finset V) : ν (raw A) = ν (comp A) := by
    exact (MeasureTheory.measure_eq_measure_of_null_diff (hcomp_subset_raw A)
      (MeasureTheory.measure_mono_null (hraw_diff_subset A) (hcube_diff_null A))).symm
  have hunion :
      {ω |
        v ∈
          (Finset.univ.filter fun u : V =>
            u ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u)} =
        ⋃ A ∈ T, raw A := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hvout
      have hvraw :
          v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v := by
        simpa using (SamplingOneVertexOutputMembership G ω.1 ω.2 v).1 hvout
      refine ⟨ω.1, ?_, ?_⟩
      · simp [T, hvraw.1]
      · exact ⟨rfl, hvraw.2⟩
    · rintro ⟨A, hAT, hωA⟩
      have hvA : v ∈ A := by
        simpa [T] using hAT
      have hvraw :
          v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v := by
        rcases hωA with ⟨hω1, hcompω⟩
        subst hω1
        exact ⟨hvA, hcompω⟩
      exact (SamplingOneVertexOutputMembership G ω.1 ω.2 v).2 hvraw
  rw [hunion]
  rw [MeasureTheory.measure_biUnion_finset]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A _hA
    by_cases hvA : v ∈ A
    · simp only [hvA, ↓reduceIte]
      rw [hraw_eq_comp A]
      simpa [comp] using hcompare A hvA
    · simp [hvA]
  · intro A _hAT B _hBT hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hωA hωB
    exact hne (hωA.1.symm.trans hωB.1)
  · intro A _hAT
    exact trivial
