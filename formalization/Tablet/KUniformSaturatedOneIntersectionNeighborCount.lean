import Tablet.KUniformSaturatedEdgeIntersectionSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

set_option maxHeartbeats 500000

-- [TABLET NODE: KUniformSaturatedOneIntersectionNeighborCount]
theorem KUniformSaturatedOneIntersectionNeighborCount :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          ∀ f : E,
            UniformHypergraph H k →
            (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
            (∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
              (H.edge g ∩ H.edge f).card = 1) →
            ((Finset.univ : Finset E).filter
              (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := by
-- BODY
  classical
  intro k D V E _ _ _ H f hunif hsat hone
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)
  have hsum : (∑ g ∈ N, (H.edge f ∩ H.edge g).card) = k * (D - 1) :=
    KUniformSaturatedEdgeIntersectionSum k D H f hunif hsat
  have hNsum : (∑ g ∈ N, (H.edge f ∩ H.edge g).card) = N.card := by
    calc
      (∑ g ∈ N, (H.edge f ∩ H.edge g).card) = ∑ g ∈ N, 1 := by
        apply Finset.sum_congr rfl
        intro g hg
        have hmem : g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty := by
          simpa [N] using hg
        rw [Finset.inter_comm]
        exact hone g hmem.1 hmem.2
      _ = N.card := by simp
  have hN : N.card = k * (D - 1) := hNsum.symm.trans hsum
  have harith : k * (D - 1) = k * D - k := by
    rw [Nat.mul_sub_left_distrib]
    simp
  simpa [N, harith] using hN
