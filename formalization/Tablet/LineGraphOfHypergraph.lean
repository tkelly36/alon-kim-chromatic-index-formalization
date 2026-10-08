import Tablet.MultiHypergraph

-- [TABLET NODE: LineGraphOfHypergraph]
def LineGraphOfHypergraph {V E : Type*} [DecidableEq V] (H : MultiHypergraph V E) :
    SimpleGraph E where
-- BODY
  Adj e f := e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty
  symm := by
    intro e f h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩
