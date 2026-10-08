import Tablet.Preamble

-- [TABLET NODE: IndependentTripleCount]
noncomputable def IndependentTripleCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
-- BODY
  ((Finset.univ : Finset (Finset V)).filter (fun S =>
    S.card = 3 ∧ S ⊆ G.neighborFinset v ∧
      ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)).card
