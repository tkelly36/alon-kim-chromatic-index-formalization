import Tablet.LocalBParameterReal

-- [TABLET NODE: LocalBParameterRealNatCast]
theorem LocalBParameterRealNatCast {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℕ) (v : V) :
    LocalBParameterReal G (M : ℝ) v = LocalBParameter G M v := by
-- BODY
  rfl
