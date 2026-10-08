import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: NibbleCompletionData]
structure NibbleCompletionData {V E K : Type*} [DecidableEq V] [DecidableEq K]
    (H : MultiHypergraph V E) (M : E → Finset K) (Delta : ℕ) where
-- BODY
  size : K → ℕ
  graph : (a : K) → SimpleGraph (Fin (size a))
  embed : (a : K) → {e : E // a ∈ M e} → Fin (size a)
  injective : ∀ a, Function.Injective (embed a)
  induced : ∀ a e f, (graph a).Adj (embed a e) (embed a f) ↔
    (LineGraphOfHypergraph H).Adj e.val f.val
  regular : ∀ a v, ((graph a).neighborSet v).ncard = Delta
