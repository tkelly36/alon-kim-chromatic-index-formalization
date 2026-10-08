import Tablet.KUniformSaturatedEdgeIntersectionSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

set_option maxHeartbeats 700000

-- [TABLET NODE: KUniformNeighborOneIntersectionFromSaturation]
theorem KUniformNeighborOneIntersectionFromSaturation :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          ∀ f : E,
            UniformHypergraph H k →
            (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
            ((Finset.univ : Finset E).filter
              (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k →
            ∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
              (H.edge g ∩ H.edge f).card = 1 := by
-- BODY
  classical
  intro k D V E _ _ _ H f hunif hsat hneighbor_card g hgf hnon
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
  let m : E → ℕ := fun e => (H.edge f ∩ H.edge e).card
  have hsum_m :
      (∑ e ∈ N, m e) = k * (D - 1) :=
    KUniformSaturatedEdgeIntersectionSum k D H f hunif hsat
  have hN_card : N.card = k * (D - 1) := by
    have harith : k * D - k = k * (D - 1) := by
      rw [Nat.mul_sub_left_distrib]
      simp
    simpa [N, harith] using hneighbor_card
  have hN_g : g ∈ N := by
    simp [N, hgf, hnon]
  have hone_le : ∀ e ∈ N, 1 ≤ m e := by
    intro e he
    have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
      simpa [N] using he
    rcases hmem.2 with ⟨x, hx⟩
    rcases Finset.mem_inter.mp hx with ⟨hxe, hxf⟩
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxf, hxe⟩⟩
  by_contra hnot
  have htwo : 2 ≤ m g := by
    have hmg : m g = (H.edge g ∩ H.edge f).card := by
      dsimp [m]
      rw [Finset.inter_comm]
    have hnot_m : m g ≠ 1 := by
      intro hm
      exact hnot (by simpa [hmg] using hm)
    have hg_one : 1 ≤ m g := hone_le g hN_g
    omega
  have hsum_erase :
      (∑ e ∈ N, m e) = m g + ∑ e ∈ N.erase g, m e := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hN_g]
    rw [Finset.sdiff_singleton_eq_erase]
  have herase_le :
      (N.erase g).card ≤ ∑ e ∈ N.erase g, m e := by
    calc
      (N.erase g).card = ∑ e ∈ N.erase g, 1 := by simp
      _ ≤ ∑ e ∈ N.erase g, m e := by
            exact Finset.sum_le_sum fun e he => hone_le e (Finset.mem_of_mem_erase he)
  have hcard_erase : N.card = (N.erase g).card + 1 := by
    rw [Finset.card_erase_of_mem hN_g]
    omega
  have hextra : N.card + 1 ≤ ∑ e ∈ N, m e := by
    rw [hsum_erase, hcard_erase]
    omega
  omega
