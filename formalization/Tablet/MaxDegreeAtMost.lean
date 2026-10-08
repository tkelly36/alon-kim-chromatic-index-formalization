import Tablet.HypergraphDegree

-- [TABLET NODE: MaxDegreeAtMost]
def MaxDegreeAtMost {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) (D : ℕ) : Prop :=
-- BODY
  ∀ v : V, HypergraphDegree H v ≤ D
