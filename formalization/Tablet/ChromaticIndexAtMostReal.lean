import Tablet.ChromaticIndexAtMost

-- [TABLET NODE: ChromaticIndexAtMostReal]
def ChromaticIndexAtMostReal {V E : Type*} [DecidableEq V] (H : MultiHypergraph V E)
    (x : ℝ) : Prop :=
-- BODY
  ∃ q : ℕ, (q : ℝ) ≤ x ∧ ChromaticIndexAtMost H q
