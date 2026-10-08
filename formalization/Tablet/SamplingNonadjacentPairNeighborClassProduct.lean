import Tablet.Preamble

open BigOperators

universe u

-- [TABLET NODE: SamplingNonadjacentPairNeighborClassProduct]
theorem SamplingNonadjacentPairNeighborClassProduct :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, (∀ z : V, G.degree z = Delta) →
          ∀ u v : V, u ≠ v → ¬ G.Adj u v →
            ∀ x y : ℝ,
              (∏ _w ∈ (G.neighborFinset u \ G.neighborFinset v),
                  (1 - x / (Delta : ℝ))) *
                (∏ _w ∈ G.neighborFinset v, (1 - y / (Delta : ℝ))) =
                  (1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta := by
-- BODY
  classical
  intro V _ _ G _ Delta hregular u v huv hnonadj x y
  have hu_degree_card : (G.neighborFinset u).card = Delta := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hregular u
  have hv_degree_card : (G.neighborFinset v).card = Delta := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hregular v
  have hu_only_card :
      (G.neighborFinset u \ G.neighborFinset v).card =
        Delta - (G.neighborFinset u ∩ G.neighborFinset v).card := by
    rw [← hu_degree_card, ← Finset.card_sdiff_add_card_inter (G.neighborFinset u)
      (G.neighborFinset v)]
    exact (Nat.add_sub_cancel_right
      (G.neighborFinset u \ G.neighborFinset v).card
      (G.neighborFinset u ∩ G.neighborFinset v).card).symm
  simp [Finset.prod_const, hu_only_card, hv_degree_card]
