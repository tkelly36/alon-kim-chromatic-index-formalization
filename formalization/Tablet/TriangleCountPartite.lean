import Tablet.Preamble
import Tablet.KPartiteTriangleCount

-- [TABLET NODE: TriangleCountPartite]
theorem TriangleCountPartite :
    (∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
        (∃ part : V → Fin 3, ∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
        (((Finset.univ : Finset (Finset V)).filter
            (fun s =>
              s.card = 3 ∧
                ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)).card : ℝ)
          ≤ ((G.edgeFinset.card : ℝ) / 3) ^ ((3 : ℝ) / 2)) := by
-- BODY
  intro V hV hdecV G hdecG hpart
  simpa using
    (KPartiteTriangleCount 3 (by norm_num) (V := V) G hpart)
