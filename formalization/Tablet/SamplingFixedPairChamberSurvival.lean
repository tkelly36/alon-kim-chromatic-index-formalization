import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingFixedPairChamberSurvival]
theorem SamplingFixedPairChamberSurvival :
    ∀ Delta : ℕ, ∀ gamma : ℝ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              (∀ a : V, a ∈ X → ∀ b : V, b ∈ X → a ≠ b →
                ¬ ∃ w : V, G.Adj a w ∧ G.Adj b w ∧ w ≠ r ∧ ¬ G.Adj r w) →
              ∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v → ¬ G.Adj u v →
                (∑ S : Finset V, if ({u, v} : Finset V) ⊆ S then μ S else 0) =
                  (2 / (Delta : ℝ)^2) *
                    ∫ x in (0 : ℝ)..gamma,
                      ∫ y in x..gamma,
                        (1 - x / (Delta : ℝ)) ^
                            (Delta -
                              (G.neighborFinset u ∩ G.neighborFinset v).card) *
                          (1 - y / (Delta : ℝ)) ^ Delta := by
-- BODY
  classical
  intro Delta gamma V _ _ G _ hregular μ hsampling r X _hX _hclean u _huX v _hvX huv hnonadj
  exact hsampling.2.1.2.2 hregular u v huv hnonadj
