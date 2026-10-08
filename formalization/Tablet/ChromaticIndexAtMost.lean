import Tablet.ProperEdgeColoring

-- [TABLET NODE: ChromaticIndexAtMost]
def ChromaticIndexAtMost {V E : Type*} [DecidableEq V] (H : MultiHypergraph V E)
    (q : ℕ) : Prop :=
-- BODY
  ∃ c : E → Fin q, ProperEdgeColoring H c
