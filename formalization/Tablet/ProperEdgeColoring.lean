import Tablet.MultiHypergraph

-- [TABLET NODE: ProperEdgeColoring]
def ProperEdgeColoring {V E Color : Type*} [DecidableEq V] (H : MultiHypergraph V E)
    (c : E → Color) : Prop :=
-- BODY
  ∀ ⦃e f : E⦄, e ≠ f → (H.edge e ∩ H.edge f).Nonempty → c e ≠ c f
