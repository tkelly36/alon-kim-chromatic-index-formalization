import Tablet.MultiHypergraph

-- [TABLET NODE: SubhypergraphOf]
def SubhypergraphOf {V E F : Type*} (H' : MultiHypergraph V F)
    (H : MultiHypergraph V E) : Prop :=
-- BODY
  ∃ i : F → E, Function.Injective i ∧ ∀ f : F, H'.edge f = H.edge (i f)
