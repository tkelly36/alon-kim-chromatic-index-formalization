import Tablet.MultiHypergraph

-- [TABLET NODE: NibbleResidualDegree]
noncomputable def NibbleResidualDegree {V E K : Type*} [Fintype E]
    (H : MultiHypergraph V E) (I : K → Finset E) (x : V) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter fun e => x ∈ H.edge e ∧ ∀ a, e ∉ I a).card
