import Tablet.MultiHypergraph

-- [TABLET NODE: KUniformFreshEdgeHypergraph]
def KUniformFreshEdgeHypergraph (k : ℕ) {V E : Type*} [DecidableEq V]
    (H : MultiHypergraph V E) (v : V) :
    MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
-- BODY
  { edge := fun e =>
      match e with
      | Sum.inl old => (H.edge old).image Sum.inl
      | Sum.inr _ => {Sum.inl v} ∪ (Finset.univ : Finset (Fin (k - 1))).image Sum.inr }
