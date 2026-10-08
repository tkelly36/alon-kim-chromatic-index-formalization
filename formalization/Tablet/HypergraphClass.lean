import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

-- [TABLET NODE: HypergraphClass]
def HypergraphClass {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (k t D : ℕ) : Set (MultiHypergraph V E) :=
-- BODY
  {H | UniformHypergraph H k ∧ TSimpleHypergraph H t ∧ MaxDegreeAtMost H D}
