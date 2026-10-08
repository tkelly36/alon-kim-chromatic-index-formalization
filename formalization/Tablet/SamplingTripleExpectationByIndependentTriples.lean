import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTripleExpectationByIndependentTriples]
theorem SamplingTripleExpectationByIndependentTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Finset V → ℝ) (X : Finset V)
    (hind :
      ∀ S : Finset V, μ S ≠ 0 →
        ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v) :
    let J3 : Finset (Finset V) :=
      (Finset.univ.filter fun Q : Finset V =>
        Q.card = 3 ∧ Q ⊆ X ∧
          ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b)
    (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) =
      ∑ Q : Finset V, if Q ∈ J3 then
        ∑ S : Finset V, if Q ⊆ S then μ S else 0
      else 0 := by
-- BODY
  classical
  let J3 : Finset (Finset V) :=
    Finset.univ.filter fun Q : Finset V =>
      Q.card = 3 ∧ Q ⊆ X ∧
        ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b
  have htriple_count :
      ∀ S : Finset V,
        μ S * (Nat.choose (S ∩ X).card 3 : ℝ) =
          μ S * ∑ Q : Finset V, if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0 := by
    intro S
    by_cases hzero : μ S = 0
    · simp [hzero]
    · have hfilter_eq :
          J3.filter (fun Q : Finset V => Q ⊆ S) = (S ∩ X).powersetCard 3 := by
        ext Q
        constructor
        · intro hQ
          have hQJ3 : Q ∈ J3 := (Finset.mem_filter.mp hQ).1
          have hQS : Q ⊆ S := (Finset.mem_filter.mp hQ).2
          have hQ_card : Q.card = 3 := by
            simpa [J3] using (Finset.mem_filter.mp hQJ3).2.1
          have hQX : Q ⊆ X := by
            simpa [J3] using (Finset.mem_filter.mp hQJ3).2.2.1
          exact Finset.mem_powersetCard.mpr
            ⟨fun z hz => by simp [hQS hz, hQX hz], hQ_card⟩
        · intro hQ
          have hQsub : Q ⊆ S ∩ X := (Finset.mem_powersetCard.mp hQ).1
          have hQ_card : Q.card = 3 := (Finset.mem_powersetCard.mp hQ).2
          have hQS : Q ⊆ S := fun z hz => by
            exact (Finset.mem_inter.mp (hQsub hz)).1
          have hQX : Q ⊆ X := fun z hz => by
            exact (Finset.mem_inter.mp (hQsub hz)).2
          have hindQ :
              ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b := by
            intro a ha b hb hab
            exact hind S hzero (hQS ha) (hQS hb) hab
          exact Finset.mem_filter.mpr
            ⟨by
              simp only [J3, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hQ_card, hQX, by
                intro a ha b hb hab
                exact hindQ ha hb hab⟩,
              hQS⟩
      have hsum_ones :
          (∑ Q : Finset V, if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0) =
            ((J3.filter (fun Q : Finset V => Q ⊆ S)).card : ℝ) := by
        let T : Finset (Finset V) :=
          (Finset.univ : Finset (Finset V)).filter
            (fun Q : Finset V => Q ∈ J3 ∧ Q ⊆ S)
        have hT_eq : T = J3.filter (fun Q : Finset V => Q ⊆ S) := by
          ext Q
          simp [T]
        calc
          (∑ Q : Finset V, if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0)
              = Finset.sum T (fun _Q : Finset V => (1 : ℝ)) := by
                dsimp [T]
                rw [Finset.sum_filter]
          _ = (T.card : ℝ) := by
                simp
          _ = ((J3.filter (fun Q : Finset V => Q ⊆ S)).card : ℝ) := by
                rw [hT_eq]
      rw [hsum_ones, hfilter_eq, Finset.card_powersetCard]
  calc
    (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ))
        = ∑ S : Finset V,
            μ S * ∑ Q : Finset V, if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro S _hS
          exact htriple_count S
    _ = ∑ Q : Finset V, ∑ S : Finset V,
            μ S * if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0 := by
          calc
            (∑ S : Finset V,
                μ S * ∑ Q : Finset V, if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0)
                = ∑ S : Finset V, ∑ Q : Finset V,
                    μ S * if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro S _hS
                  rw [Finset.mul_sum]
            _ = ∑ Q : Finset V, ∑ S : Finset V,
                    μ S * if Q ∈ J3 ∧ Q ⊆ S then (1 : ℝ) else 0 := by
                  rw [Finset.sum_comm]
    _ = ∑ Q : Finset V, if Q ∈ J3 then
          ∑ S : Finset V, if Q ⊆ S then μ S else 0
        else 0 := by
          apply Finset.sum_congr rfl
          intro Q _hQ
          by_cases hQJ3 : Q ∈ J3
          · rw [if_pos hQJ3]
            apply Finset.sum_congr rfl
            intro S _hS
            by_cases hQS : Q ⊆ S
            · simp [hQJ3, hQS]
            · simp [hQJ3, hQS]
          · rw [if_neg hQJ3]
            simp [hQJ3]
