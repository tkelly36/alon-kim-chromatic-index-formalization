import Tablet.LocalBParameter

-- [TABLET NODE: LocalBParameterReal]
noncomputable def LocalBParameterReal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℝ) (v : V) : ℝ :=
-- BODY
  (G.degree v : ℝ) / M - (IndependentPairCount G v : ℝ) / M^2 +
    (IndependentTripleCount G v : ℝ) / M^3
