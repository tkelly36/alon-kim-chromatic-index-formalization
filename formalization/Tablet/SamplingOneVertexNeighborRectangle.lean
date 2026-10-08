import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingOneVertexNeighborRectangle]
theorem SamplingOneVertexNeighborRectangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (v : V) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hrect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ u : V, t u ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧
            ∀ u : V, 0 ≤ ω.2 u ∧ ω.2 u ≤ t u} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ u : V, t u)) :
    ν {ω |
      ω.1 = A ∧
        ∀ u : V, 0 ≤ ω.2 u ∧
          ω.2 u ≤ if u ∈ A ∧ G.Adj v u then a else 1} =
      ν {ω | ω.1 = A} *
        ENNReal.ofReal
          (a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
-- BODY
  let t : V → ℝ := fun u => if u ∈ A ∧ G.Adj v u then a else 1
  have ht : ∀ u : V, t u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u
    by_cases h : u ∈ A ∧ G.Adj v u
    · simp [t, h, ha0, ha1]
    · simp [t, h]
  have hprod :
      (∏ u : V, t u) =
        a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card) := by
    dsimp [t]
    rw [← Finset.prod_filter]
    simp
  change
    ν {ω | ω.1 = A ∧ ∀ u : V, 0 ≤ ω.2 u ∧ ω.2 u ≤ t u} =
      ν {ω | ω.1 = A} *
        ENNReal.ofReal
          (a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
  rw [hrect A t ht]
  rw [hprod]
