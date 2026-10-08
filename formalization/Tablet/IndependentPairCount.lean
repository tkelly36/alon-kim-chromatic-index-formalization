import Tablet.Preamble

-- [TABLET NODE: IndependentPairCount]
noncomputable def IndependentPairCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
-- BODY
  ((Finset.univ : Finset (Finset V)).filter (fun S =>
    S.card = 2 ∧ S ⊆ G.neighborFinset v ∧
      ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)).card
