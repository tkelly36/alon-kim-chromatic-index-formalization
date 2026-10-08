import Tablet.NibbleCompletedSelection

-- [TABLET NODE: NibbleSelectedEdges]
noncomputable def NibbleSelectedEdges {V E K : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq K] {H : MultiHypergraph V E} {M : E → Finset K} {Delta : ℕ}
    (Q : NibbleCompletionData H M Delta)
    (ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ) (a : K) : Finset E := by
-- BODY
  classical
  exact Finset.univ.filter fun e =>
    ∃ h : a ∈ M e, Q.embed a ⟨e, h⟩ ∈ NibbleCompletedSelection Q ω a
