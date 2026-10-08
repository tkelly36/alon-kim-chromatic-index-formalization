import Tablet.MultiHypergraph

-- [TABLET NODE: HypergraphDegree]
def HypergraphDegree {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) (v : V) : ℕ :=
-- BODY
  ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).card
