import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingFiniteSetPushForwardEvent]
theorem SamplingFiniteSetPushForwardEvent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : Finset V → ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S)
    (hpush : ∀ S : Finset V,
      ENNReal.ofReal (μ S) =
        ν {ω |
          S =
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)})
    (Q : Finset V) :
    ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) =
        ν {ω |
          Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let out : Finset V × (V → ℝ) → Finset V := fun ω =>
    Finset.univ.filter fun z => z ∈ ω.1 ∧
      ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z
  have hmem (z : V) : MeasurableSet {ω | z ∈ out ω} := by
    simp only [out, Finset.mem_filter, Finset.mem_univ, true_and]
    measurability
  have hfiber (S : Finset V) : MeasurableSet {ω | S = out ω} := by
    have heq : {ω | S = out ω} =
        ⋂ z : V, if z ∈ S then {ω | z ∈ out ω} else {ω | z ∈ out ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h z
        by_cases hz : z ∈ S <;> simp [hz, ← h]
      · intro h
        ext z
        specialize h z
        by_cases hz : z ∈ S <;> simpa [hz] using h
    rw [heq]
    exact MeasurableSet.iInter fun z => by
      split_ifs
      · exact hmem z
      · exact (hmem z).compl
  let T := (Finset.univ : Finset (Finset V)).filter (Q ⊆ ·)
  have hcover : {ω | Q ⊆ out ω} = ⋃ S ∈ T, {ω | S = out ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, T, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨out ω, h, rfl⟩, fun ⟨S, hS, h⟩ => h ▸ hS⟩
  change ENNReal.ofReal _ = ν {ω | Q ⊆ out ω}
  rw [hcover, MeasureTheory.measure_biUnion_finset]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · simp only [T, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp_all [out]
    · intro S _
      split_ifs
      · exact hμ_nonneg S
      · exact le_rfl
  · intro S _ U _ hne
    rw [Function.onFun, Set.disjoint_left]
    exact fun ω hS hU => hne (hS.trans hU.symm)
  · exact fun S _ => hfiber S
