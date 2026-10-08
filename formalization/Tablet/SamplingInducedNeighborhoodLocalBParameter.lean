import Tablet.LocalBParameter

-- [TABLET NODE: SamplingInducedNeighborhoodLocalBParameter]
noncomputable def SamplingInducedNeighborhoodLocalBParameter {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Delta : ℕ) (r : V) (X : Finset V) : ℝ :=
-- BODY
  let J2 : Finset (Finset V) :=
    (Finset.univ.filter fun P : Finset V =>
      P.card = 2 ∧ P ⊆ X ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
  let J3 : Finset (Finset V) :=
    (Finset.univ.filter fun P : Finset V =>
      P.card = 3 ∧ P ⊆ X ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
  (X.card : ℝ) / (Delta : ℝ) - (J2.card : ℝ) / (Delta : ℝ)^2 +
    (J3.card : ℝ) / (Delta : ℝ)^3
