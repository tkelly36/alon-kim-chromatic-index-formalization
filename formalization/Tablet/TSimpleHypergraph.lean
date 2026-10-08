import Tablet.MultiHypergraph

-- [TABLET NODE: TSimpleHypergraph]
def TSimpleHypergraph {V E : Type*} [DecidableEq V] (H : MultiHypergraph V E)
    (t : ℕ) : Prop :=
-- BODY
  ∀ ⦃e f : E⦄, e ≠ f → ((H.edge e) ∩ (H.edge f)).card ≤ t
