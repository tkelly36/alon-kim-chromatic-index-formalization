import Tablet.NibbleCompletionData

-- [TABLET NODE: NibbleCompletedSelection]
noncomputable def NibbleCompletedSelection {V E K : Type*} [DecidableEq V] [DecidableEq K]
    {H : MultiHypergraph V E} {M : E → Finset K} {Delta : ℕ}
    (Q : NibbleCompletionData H M Delta)
    (ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ) (a : K) :
    Finset (Fin (Q.size a)) := by
-- BODY
  classical
  exact Finset.univ.filter fun v => (ω ⟨a, v⟩).1 = 1 ∧
    ∀ u, (ω ⟨a, u⟩).1 = 1 → (Q.graph a).Adj v u →
      (ω ⟨a, u⟩).2 < (ω ⟨a, v⟩).2
