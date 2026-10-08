import Tablet.NibbleSelectedEdges
import Tablet.NibbleResidualDegree
import Tablet.NibbleDeletedColors

-- [TABLET NODE: NibbleBadEvent]
noncomputable def NibbleBadEvent {V E K : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq K] {H : MultiHypergraph V E}
    {M : E → Finset K} {Delta : ℕ} (Q : NibbleCompletionData H M Delta)
    (d z : ℝ) :
    ({x : V // x ∈ (Finset.univ : Finset E).biUnion H.edge} ⊕ E) →
      Set ((Sigma fun a => Fin (Q.size a)) → ℝ × ℝ) :=
-- BODY
  fun j => match j with
  | Sum.inl x => {ω | d < (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x.val : ℝ)}
  | Sum.inr e => {ω | z ≤ ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ)}
