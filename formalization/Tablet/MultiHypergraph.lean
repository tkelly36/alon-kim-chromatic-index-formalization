import Tablet.Preamble

-- [TABLET NODE: MultiHypergraph]
structure MultiHypergraph (V E : Type*) where
-- BODY
  edge : E → Finset V
