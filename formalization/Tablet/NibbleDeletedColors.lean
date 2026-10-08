import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: NibbleDeletedColors]
noncomputable def NibbleDeletedColors {V E K : Type*} [DecidableEq V] [DecidableEq K]
    (H : MultiHypergraph V E) (M : E → Finset K) (I : K → Finset E)
    (e : E) : Finset K := by
-- BODY
  classical
  exact (M e).filter fun a => ∃ f ∈ I a, (LineGraphOfHypergraph H).Adj e f
