import Tablet.IndependentPairCount

-- [TABLET NODE: IndependentPairCountLeChooseNeighborCard]
theorem IndependentPairCountLeChooseNeighborCard :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj], ∀ v : V,
        IndependentPairCount G v ≤ Nat.choose (G.neighborFinset v).card 2 := by
-- BODY
  classical
  intro V _ _ G _ v
  unfold IndependentPairCount
  let indepPairs : Finset (Finset V) :=
    (Finset.univ.filter (fun S =>
      S.card = 2 ∧ S ⊆ G.neighborFinset v ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬G.Adj x y))
  have hsub : indepPairs ⊆ (G.neighborFinset v).powersetCard 2 := by
    intro S hS
    dsimp [indepPairs] at hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.mem_powersetCard.mpr ⟨hS.2.1, hS.1⟩
  calc
    indepPairs.card ≤ ((G.neighborFinset v).powersetCard 2).card :=
      Finset.card_le_card hsub
    _ = Nat.choose (G.neighborFinset v).card 2 := by
      rw [Finset.card_powersetCard]
