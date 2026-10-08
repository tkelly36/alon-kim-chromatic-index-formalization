import Tablet.MultiHypergraph

-- [TABLET NODE: UniformHypergraph]
def UniformHypergraph {V E : Type*} (H : MultiHypergraph V E) (k : ℕ) : Prop :=
-- BODY
  ∀ e : E, (H.edge e).card = k
