import Tablet.MaxDegreeAtMost

-- [TABLET NODE: RealDegreeFloorBound]
theorem RealDegreeFloorBound {V E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) {r : ℝ}
    (hd : ∀ v, (HypergraphDegree H v : ℝ) ≤ r) :
    MaxDegreeAtMost H ⌊r⌋₊ := by
-- BODY
  intro v
  exact Nat.le_floor (hd v)
