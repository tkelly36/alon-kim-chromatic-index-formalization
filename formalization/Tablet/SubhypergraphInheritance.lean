import Tablet.SubhypergraphOf
import Tablet.UniformHypergraph
import Tablet.TSimpleHypergraph
import Tablet.HypergraphDegree

-- [TABLET NODE: SubhypergraphInheritance]
theorem SubhypergraphInheritance {V E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] [DecidableEq V]
    (H' : MultiHypergraph V F) (H : MultiHypergraph V E)
    (hsub : SubhypergraphOf H' H) :
    (∀ k, UniformHypergraph H k → UniformHypergraph H' k) ∧
    (∀ t, TSimpleHypergraph H t → TSimpleHypergraph H' t) ∧
    (∀ v, HypergraphDegree H' v ≤ HypergraphDegree H v) := by
-- BODY
  obtain ⟨i, hi, hedge⟩ := hsub
  refine ⟨?_, ?_, ?_⟩
  · intro k hk f
    change (H'.edge f).card = k
    rw [hedge]
    exact hk (i f)
  · intro t ht e f hef
    change (H'.edge e ∩ H'.edge f).card ≤ t
    rw [hedge, hedge]
    exact ht (fun h => hef (hi h))
  · intro v
    unfold HypergraphDegree
    apply Finset.card_le_card_of_injOn i
    · intro f hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hedge f) ▸ (Finset.mem_filter.mp hf).2⟩
    · intro e he f hf h
      exact hi h
