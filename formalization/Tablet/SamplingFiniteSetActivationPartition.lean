import Tablet.SamplingOneVertexOutputMembership

open BigOperators

-- [TABLET NODE: SamplingFiniteSetActivationPartition]
theorem SamplingFiniteSetActivationPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (Q : Finset V) :
    (ν {ω |
        Q ⊆
          (Finset.univ.filter fun z : V =>
            z ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
      ∑ A : Finset V,
        if Q ⊆ A then
          ν {ω |
            ω.1 = A ∧
              ∀ q : V, q ∈ Q →
                ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
        else 0) ∧
        (∀ A : Finset V, ∀ π : V → ℝ,
          Q ⊆
              (Finset.univ.filter fun z : V =>
                z ∈ A ∧
                  ∀ w : V, w ∈ A → G.Adj z w → π w < π z) ↔
            Q ⊆ A ∧
              ∀ q : V, q ∈ Q →
                ∀ w : V, w ∈ A → G.Adj q w → π w < π q) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  have hpoint (A : Finset V) (π : V → ℝ) :
      Q ⊆ (Finset.univ.filter fun z : V => z ∈ A ∧
        ∀ w : V, w ∈ A → G.Adj z w → π w < π z) ↔
      Q ⊆ A ∧ ∀ q : V, q ∈ Q → ∀ w : V, w ∈ A → G.Adj q w → π w < π q := by
    simp only [Finset.subset_iff, SamplingOneVertexOutputMembership]
    exact ⟨fun h => ⟨fun q hq => (h hq).1, fun q hq => (h hq).2⟩,
      fun ⟨hA, hπ⟩ q hq => ⟨hA hq, hπ q hq⟩⟩
  refine ⟨?_, hpoint⟩
  let E : Finset V → Set (Finset V × (V → ℝ)) := fun A =>
    {ω | ω.1 = A ∧ ∀ q : V, q ∈ Q →
      ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
  let T := (Finset.univ : Finset (Finset V)).filter (Q ⊆ ·)
  have hmeas (A : Finset V) : MeasurableSet (E A) := by
    dsimp [E]
    measurability
  have hcover : {ω : Finset V × (V → ℝ) | Q ⊆
      (Finset.univ.filter fun z => z ∈ ω.1 ∧
        ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
      ⋃ A ∈ T, E A := by
    ext ω
    simp only [Set.mem_setOf_eq, hpoint, Set.mem_iUnion,
      T, Finset.mem_filter, Finset.mem_univ, true_and, E]
    constructor
    · rintro ⟨hQ, hπ⟩
      exact ⟨ω.1, hQ, rfl, hπ⟩
    · rintro ⟨A, hQ, hA, hπ⟩
      subst A
      exact ⟨hQ, hπ⟩
  rw [hcover, MeasureTheory.measure_biUnion_finset]
  · exact Finset.sum_filter _ _
  · intro A _ B _ hne
    rw [Function.onFun, Set.disjoint_left]
    exact fun ω hA hB => hne (hA.1.symm.trans hB.1)
  · exact fun A _ => hmeas A
