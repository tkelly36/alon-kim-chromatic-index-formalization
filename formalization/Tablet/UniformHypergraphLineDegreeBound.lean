import Tablet.LineGraphOfHypergraph
import Tablet.UniformHypergraph
import Tablet.MaxDegreeAtMost

-- [TABLET NODE: UniformHypergraphLineDegreeBound]
theorem UniformHypergraphLineDegreeBound {V E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) [DecidableRel (LineGraphOfHypergraph H).Adj] {k n : ℕ}
    (hu : UniformHypergraph H k) (hd : MaxDegreeAtMost H n) (e : E) :
    (LineGraphOfHypergraph H).degree e ≤ k * (n - 1) := by
-- BODY
  classical
  let S : V → Finset E := fun v => (Finset.univ.filter (fun f => v ∈ H.edge f)).erase e
  have hsub : (LineGraphOfHypergraph H).neighborFinset e ⊆
      (H.edge e).biUnion S := by
    intro f hf
    have ha := (SimpleGraph.mem_neighborFinset _ _ _).mp hf
    obtain ⟨v, hv⟩ := ha.2
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_inter.mp hv).1,
      Finset.mem_erase.mpr ⟨ha.1.symm, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_inter.mp hv).2⟩⟩⟩
  calc
    (LineGraphOfHypergraph H).degree e =
        ((LineGraphOfHypergraph H).neighborFinset e).card := by simp
    _ ≤ ((H.edge e).biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ H.edge e, (S v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ H.edge e, (n - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      dsimp [S]
      rw [Finset.card_erase_of_mem (by simp [hv])]
      exact Nat.sub_le_sub_right (hd v) 1
    _ = k * (n - 1) := by simp [hu e]
