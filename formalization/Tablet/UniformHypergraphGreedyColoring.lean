import Tablet.FiniteGraphGreedyColoring
import Tablet.UniformHypergraphLineDegreeBound
import Tablet.ChromaticIndexAtMost

-- [TABLET NODE: UniformHypergraphGreedyColoring]
theorem UniformHypergraphGreedyColoring {V E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hu : UniformHypergraph H k) (hd : MaxDegreeAtMost H n) :
    ChromaticIndexAtMost H (k * n) := by
-- BODY
  classical
  obtain ⟨c, hc⟩ := FiniteGraphGreedyColoring (LineGraphOfHypergraph H)
    (Nat.mul_pos hk hn) (fun e => lt_of_le_of_lt
      (UniformHypergraphLineDegreeBound H hu hd e)
      (Nat.mul_lt_mul_of_pos_left (by omega : n - 1 < n) hk))
  exact ⟨c, fun _ _ hne hmeet => hc _ _ ⟨hne, hmeet⟩⟩
