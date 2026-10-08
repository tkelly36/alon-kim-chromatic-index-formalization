import Tablet.RandomIndependentSetSampling

-- [TABLET NODE: SamplingOneVertexOutputMembership]
theorem SamplingOneVertexOutputMembership {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (π : V → ℝ) (v : V) :
    v ∈
        (Finset.univ.filter fun u : V =>
          u ∈ A ∧ ∀ w : V, w ∈ A → G.Adj u w → π w < π u) ↔
      v ∈ A ∧ ∀ w : V, w ∈ A → G.Adj v w → π w < π v := by
-- BODY
  simp
