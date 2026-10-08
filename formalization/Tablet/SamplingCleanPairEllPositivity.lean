import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingCleanPairEllPositivity]
theorem SamplingCleanPairEllPositivity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ)
    (hregular : ∀ v : V, G.degree v = Delta)
    (r : V) (X Q P : Finset V)
    (hXnbr : ∀ x : V, x ∈ X → G.Adj r x)
    (hclean :
      ∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
        ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w)
    (hQX : Q ⊆ X)
    (hQind :
      ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b)
    (hPcard : P.card = 2) (hPQ : P ⊆ Q)
    (ell : Finset V → ℝ)
    (hell :
      ∀ P : Finset V,
        P.card = 2 → P ⊆ X →
          (∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b) →
            ∃ u : V, ∃ v : V,
              u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                ell P =
                  ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) /
                    (Delta : ℝ)) :
    0 ≤ ell P ∧ 0 < 1 - ell P ∧ 0 < 2 - ell P := by
-- BODY
  classical
  have hPX : P ⊆ X := fun x hx => hQX (hPQ hx)
  have hPind :
      ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hQind (hPQ ha) (hPQ hb) hab
  rcases hell P hPcard hPX hPind with
    ⟨u, v, huP, hvP, huv, hellP⟩
  have huX : u ∈ X := hPX huP
  have hvX : v ∈ X := hPX hvP
  have hur_adj : G.Adj r u := hXnbr u huX
  have hvr_adj : G.Adj r v := hXnbr v hvX
  have hur_mem : u ∈ G.neighborFinset r := by
    simpa [SimpleGraph.mem_neighborFinset] using hur_adj
  have hvr_mem : v ∈ G.neighborFinset r := by
    simpa [SimpleGraph.mem_neighborFinset] using hvr_adj
  have hpair_sub : ({u, v} : Finset V) ⊆ G.neighborFinset r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hur_mem
    · exact hvr_mem
  have hDelta_two : 2 ≤ Delta := by
    have hcard_le : ({u, v} : Finset V).card ≤ (G.neighborFinset r).card :=
      Finset.card_le_card hpair_sub
    have hpair_card : ({u, v} : Finset V).card = 2 := by
      simp [huv]
    rw [hpair_card, SimpleGraph.card_neighborFinset_eq_degree, hregular r] at hcard_le
    exact hcard_le
  let C : Finset V := G.neighborFinset u ∩ G.neighborFinset v
  let T : Finset V := insert r (G.neighborFinset r \ ({u, v} : Finset V))
  have hCsub : C ⊆ T := by
    intro w hwC
    have huw_adj : G.Adj u w := by
      simpa [C, SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hwC).1
    have hvw_adj : G.Adj v w := by
      simpa [C, SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hwC).2
    by_cases hwr : w = r
    · simp [T, hwr]
    · have hrw_adj : G.Adj r w := by
        by_contra hnot
        exact (hclean u huX v hvX huv) ⟨w, huw_adj, hvw_adj, hwr, hnot⟩
      have hwr_ne_u : w ≠ u := (G.ne_of_adj huw_adj).symm
      have hwr_ne_v : w ≠ v := (G.ne_of_adj hvw_adj).symm
      have hw_nei : w ∈ G.neighborFinset r := by
        simpa [SimpleGraph.mem_neighborFinset] using hrw_adj
      have hw_not_pair : w ∉ ({u, v} : Finset V) := by
        simp [hwr_ne_u, hwr_ne_v]
      simp [T, hw_nei, hw_not_pair]
  have hT_card : T.card = Delta - 1 := by
    have hr_not_nei : r ∉ G.neighborFinset r := by
      simp [SimpleGraph.mem_neighborFinset]
    have hr_not_diff : r ∉ G.neighborFinset r \ ({u, v} : Finset V) := by
      simp [hr_not_nei]
    have hdiff :
        (G.neighborFinset r \ ({u, v} : Finset V)).card = Delta - 2 := by
      rw [Finset.card_sdiff_of_subset hpair_sub]
      simp [SimpleGraph.card_neighborFinset_eq_degree, hregular r, huv]
    dsimp [T]
    rw [Finset.card_insert_of_notMem hr_not_diff, hdiff]
    omega
  have hC_card_le : C.card ≤ Delta - 1 := by
    calc
      C.card ≤ T.card := Finset.card_le_card hCsub
      _ = Delta - 1 := hT_card
  have hC_card_lt : C.card < Delta := by
    omega
  have hDelta_pos_nat : 0 < Delta := lt_of_lt_of_le (by decide : 0 < 2) hDelta_two
  have hDelta_pos : 0 < (Delta : ℝ) := by
    exact_mod_cast hDelta_pos_nat
  have hell_nonneg : 0 ≤ ell P := by
    rw [hellP]
    exact div_nonneg (by positivity) (le_of_lt hDelta_pos)
  have hell_lt_one : ell P < 1 := by
    rw [hellP]
    have hcast_lt : ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) < (Delta : ℝ) := by
      exact_mod_cast hC_card_lt
    have hdiv := div_lt_div_of_pos_right hcast_lt hDelta_pos
    simpa [C, div_self (ne_of_gt hDelta_pos)] using hdiv
  refine ⟨hell_nonneg, ?_, ?_⟩ <;> linarith
