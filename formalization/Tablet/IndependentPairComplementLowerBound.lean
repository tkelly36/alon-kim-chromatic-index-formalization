import Tablet.IndependentPairCount
import Mathlib.Data.Finset.Powerset

set_option maxHeartbeats 400000

-- [TABLET NODE: IndependentPairComplementLowerBound]
theorem IndependentPairComplementLowerBound :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] → ∀ v : V, ∀ B : ℕ,
        let N : Finset V := G.neighborFinset v
        let adjacentPairs : Finset (Finset V) :=
          (N.powersetCard 2).filter (fun S =>
            ∃ x, x ∈ S ∧ ∃ y, y ∈ S ∧ x ≠ y ∧ G.Adj x y)
        adjacentPairs.card ≤ B →
          Nat.choose N.card 2 - B ≤ IndependentPairCount G v := by
-- BODY
  classical
  intro V _ _ G _ v B N adjacentPairs hbad
  let indepPairs : Finset (Finset V) :=
    (N.powersetCard 2).filter (fun S =>
      ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
  have hdef_sets :
      ((Finset.univ : Finset (Finset V)).filter (fun S =>
        S.card = 2 ∧ S ⊆ G.neighborFinset v ∧
          ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)) = indepPairs := by
    apply Finset.ext
    intro S
    simp [indepPairs, N, and_assoc, and_comm]
  have hdef : IndependentPairCount G v = indepPairs.card := by
    unfold IndependentPairCount
    rw [hdef_sets]
  have hpartition : (N.powersetCard 2).filter (fun S =>
        ¬ (∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)) = adjacentPairs := by
    apply Finset.ext
    intro S
    simp [adjacentPairs]
  have hcard_total : (N.powersetCard 2).card = indepPairs.card + adjacentPairs.card := by
    calc
      (N.powersetCard 2).card
          = ((N.powersetCard 2).filter (fun S =>
              ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)).card +
            ((N.powersetCard 2).filter (fun S =>
              ¬ (∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y))).card := by
              rw [Finset.card_filter_add_card_filter_not]
      _ = indepPairs.card + adjacentPairs.card := by rw [hpartition]
  have hchoose : Nat.choose N.card 2 = indepPairs.card + adjacentPairs.card := by
    rw [← hcard_total, Finset.card_powersetCard]
  have hle : Nat.choose N.card 2 - B ≤ indepPairs.card := by
    rw [hchoose]
    omega
  simpa [hdef] using hle
