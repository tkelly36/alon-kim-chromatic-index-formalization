import Tablet.MultiHypergraph

-- [TABLET NODE: KUniformSplitEdgeHypergraph]
def KUniformSplitEdgeHypergraph (k : ℕ) {V E : Type*} [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (g : E) (v : V) (hv : v ∈ H.edge g) (x1 : Fin (k - 1)) :
    MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
-- BODY
  { edge := fun e =>
      match e with
      | Sum.inl old =>
          if old = g then
            ((H.edge g).erase v).image Sum.inl ∪ {Sum.inr x1}
          else
            (H.edge old).image Sum.inl
      | Sum.inr _ =>
          {Sum.inl v} ∪ (Finset.univ : Finset (Fin (k - 1))).image Sum.inr }
