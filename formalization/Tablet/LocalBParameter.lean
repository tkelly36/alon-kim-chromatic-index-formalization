import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount

-- [TABLET NODE: LocalBParameter]
noncomputable def LocalBParameter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℕ) (v : V) : ℝ :=
-- BODY
  (G.degree v : ℝ) / (M : ℝ) - (IndependentPairCount G v : ℝ) / (M : ℝ)^2 +
    (IndependentTripleCount G v : ℝ) / (M : ℝ)^3
