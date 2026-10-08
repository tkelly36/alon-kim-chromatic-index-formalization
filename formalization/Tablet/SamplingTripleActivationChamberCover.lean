import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTripleActivationChamberCover]
theorem SamplingTripleActivationChamberCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (a b c : V) :
    let Q : Finset V := {a, b, c}
    let orders : Finset (V × V × V) :=
      {((a, b, c) : V × V × V), (a, c, b), (b, a, c),
        (b, c, a), (c, a, b), (c, b, a)}
    let chamber : V × V × V → Set (Finset V × (V → ℝ)) := fun t =>
      {ω |
        ω.1 = A ∧
          ω.2 t.1 ≤ ω.2 t.2.1 ∧ ω.2 t.2.1 ≤ ω.2 t.2.2 ∧
            ∀ q : V, q ∈ ({t.1, t.2.1, t.2.2} : Finset V) →
              ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
    ν {ω |
        ω.1 = A ∧
          ∀ q : V, q ∈ Q →
            ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ≤
      (∑ t ∈ orders, ν (chamber t)) := by
-- BODY
  classical
  intro Q orders chamber
  have hQabc : Q = ({a, b, c} : Finset V) := rfl
  let E : Set (Finset V × (V → ℝ)) :=
    {ω |
      ω.1 = A ∧
        ∀ q : V, q ∈ Q →
          ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
  have hcover : E ⊆ ⋃ t ∈ orders, chamber t := by
    intro ω hω
    rcases hω with ⟨hωA, hbeats⟩
    have hbeats_abc :
        ∀ q : V, q ∈ ({a, b, c} : Finset V) →
          ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q := by
      simpa [hQabc] using hbeats
    by_cases hab_le : ω.2 a ≤ ω.2 b
    · by_cases hbc_le : ω.2 b ≤ ω.2 c
      · refine Set.mem_iUnion.2 ⟨(a, b, c), ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        · simp [orders]
        · dsimp [chamber]
          exact ⟨hωA, hab_le, hbc_le, hbeats_abc⟩
      · have hcb_le : ω.2 c ≤ ω.2 b := le_of_not_ge hbc_le
        by_cases hac_le : ω.2 a ≤ ω.2 c
        · refine Set.mem_iUnion.2 ⟨(a, c, b), ?_⟩
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · simp [orders]
          · dsimp [chamber]
            exact
              ⟨hωA, hac_le, hcb_le, by
                intro q hq
                exact hbeats_abc q (by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
                  rcases hq with rfl | rfl | rfl <;> simp)⟩
        · have hca_le : ω.2 c ≤ ω.2 a := le_of_not_ge hac_le
          refine Set.mem_iUnion.2 ⟨(c, a, b), ?_⟩
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · simp [orders]
          · dsimp [chamber]
            exact
              ⟨hωA, hca_le, hab_le, by
                intro q hq
                exact hbeats_abc q (by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
                  rcases hq with rfl | rfl | rfl <;> simp)⟩
    · have hba_le : ω.2 b ≤ ω.2 a := le_of_not_ge hab_le
      by_cases hac_le : ω.2 a ≤ ω.2 c
      · refine Set.mem_iUnion.2 ⟨(b, a, c), ?_⟩
        refine Set.mem_iUnion.2 ⟨?_, ?_⟩
        · simp [orders]
        · dsimp [chamber]
          exact
            ⟨hωA, hba_le, hac_le, by
              intro q hq
              exact hbeats_abc q (by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
                rcases hq with rfl | rfl | rfl <;> simp)⟩
      · have hca_le : ω.2 c ≤ ω.2 a := le_of_not_ge hac_le
        by_cases hbc_le : ω.2 b ≤ ω.2 c
        · refine Set.mem_iUnion.2 ⟨(b, c, a), ?_⟩
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · simp [orders]
          · dsimp [chamber]
            exact
              ⟨hωA, hbc_le, hca_le, by
                intro q hq
                exact hbeats_abc q (by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
                  rcases hq with rfl | rfl | rfl <;> simp)⟩
        · have hcb_le : ω.2 c ≤ ω.2 b := le_of_not_ge hbc_le
          refine Set.mem_iUnion.2 ⟨(c, b, a), ?_⟩
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · simp [orders]
          · dsimp [chamber]
            exact
              ⟨hωA, hcb_le, hba_le, by
                intro q hq
                exact hbeats_abc q (by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
                  rcases hq with rfl | rfl | rfl <;> simp)⟩
  calc
    ν E ≤ ν (⋃ t ∈ orders, chamber t) := MeasureTheory.measure_mono hcover
    _ ≤ ∑ t ∈ orders, ν (chamber t) :=
      MeasureTheory.measure_biUnion_finset_le orders chamber
