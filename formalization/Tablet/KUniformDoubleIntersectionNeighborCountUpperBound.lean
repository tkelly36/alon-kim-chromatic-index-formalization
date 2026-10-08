import Tablet.KUniformSaturatedEdgeIntersectionSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.LineGraphOfHypergraph
import Tablet.UniformHypergraph

set_option maxHeartbeats 700000

-- [TABLET NODE: KUniformDoubleIntersectionNeighborCountUpperBound]
theorem KUniformDoubleIntersectionNeighborCountUpperBound :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E, ∀ f g : E, ∀ u v : V,
          [DecidableRel (LineGraphOfHypergraph H).Adj] →
          UniformHypergraph H k →
          (∀ x : V, x ∈ H.edge f → HypergraphDegree H x = D) →
          g ≠ f → u ≠ v → u ∈ H.edge f → v ∈ H.edge f → u ∈ H.edge g →
            v ∈ H.edge g →
          ((Finset.univ : Finset E).filter
            (fun e => (LineGraphOfHypergraph H).Adj f e)).card ≤
              k * (D - 1) - 1 := by
-- BODY
  classical
  intro k D V E _ _ _ H f g u v _ hunif hsat hgf huv huf hvf hug hvg
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
  have hbelow_eq (e : E) :
      (H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e = H.edge f ∩ H.edge e := by
    ext x
    simp [Finset.bipartiteBelow, Finset.mem_inter]
  have hsum_inter :
      (∑ e ∈ N, ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card)
        = k * (D - 1) := by
    simp_rw [hbelow_eq]
    exact KUniformSaturatedEdgeIntersectionSum k D H f hunif hsat
  have hN_g : g ∈ N := by
    have hnon : (H.edge g ∩ H.edge f).Nonempty :=
      ⟨u, Finset.mem_inter.mpr ⟨hug, huf⟩⟩
    simp [N, hgf, hnon]
  have htwo_g :
      2 ≤ ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) g).card := by
    rw [hbelow_eq g]
    have hu : u ∈ H.edge f ∩ H.edge g := Finset.mem_inter.mpr ⟨huf, hug⟩
    have hv : v ∈ H.edge f ∩ H.edge g := Finset.mem_inter.mpr ⟨hvf, hvg⟩
    have hpair_sub : ({u, v} : Finset V) ⊆ H.edge f ∩ H.edge g := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    calc
      2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
      _ ≤ (H.edge f ∩ H.edge g).card := Finset.card_le_card hpair_sub
  have hone_each : ∀ e ∈ N,
      1 ≤ ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
    intro e he
    have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
      simpa [N] using he
    rw [hbelow_eq e]
    rcases hmem.2 with ⟨x, hx⟩
    rcases Finset.mem_inter.mp hx with ⟨hxe, hxf⟩
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxf, hxe⟩⟩
  have hcard_le_sum :
      N.card ≤ ∑ e ∈ N, ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
    calc
      N.card = ∑ e ∈ N, 1 := by simp
      _ ≤ ∑ e ∈ N, ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
        exact Finset.sum_le_sum fun e he => hone_each e he
  have hextra :
      N.card + 1 ≤ ∑ e ∈ N, ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
    have hsum_erase :
        (∑ e ∈ N, ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card)
          =
        ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) g).card +
          ∑ e ∈ N.erase g,
            ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hN_g]
      rw [Finset.sdiff_singleton_eq_erase]
    have hcard_erase :
        N.card = (N.erase g).card + 1 := by
      have hpos : 0 < N.card := Finset.card_pos.mpr ⟨g, hN_g⟩
      rw [Finset.card_erase_of_mem hN_g]
      omega
    have herase_le :
        (N.erase g).card ≤
          ∑ e ∈ N.erase g,
            ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
      calc
        (N.erase g).card = ∑ e ∈ N.erase g, 1 := by simp
        _ ≤ ∑ e ∈ N.erase g,
            ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card := by
          exact Finset.sum_le_sum fun e he =>
            hone_each e (Finset.mem_of_mem_erase he)
    rw [hsum_erase, hcard_erase]
    have hsum_lower :
        2 + (N.erase g).card ≤
          ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) g).card +
            ∑ e ∈ N.erase g,
              ((H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e).card :=
      Nat.add_le_add htwo_g herase_le
    have hrewrite : (N.erase g).card + 1 + 1 = 2 + (N.erase g).card := by
      omega
    rw [hrewrite]
    exact hsum_lower
  have hN_lt : N.card < k * (D - 1) := by
    rw [← hsum_inter]
    exact Nat.lt_of_succ_le hextra
  have hneighbor_eq :
      ((Finset.univ : Finset E).filter
        (fun e => (LineGraphOfHypergraph H).Adj f e)) = N := by
    ext e
    constructor
    · intro he
      rcases (by simpa [LineGraphOfHypergraph] using he) with ⟨hfe, hnon⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ e,
          ⟨by intro hef; exact hfe (by simp [hef]), by
            simpa [Finset.inter_comm] using hnon⟩⟩
    · intro he
      have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
        simpa [N] using he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ e,
          by
            simp [LineGraphOfHypergraph]
            exact ⟨by intro hfe; exact hmem.1 hfe.symm,
              by simpa [Finset.inter_comm] using hmem.2⟩⟩
  rw [hneighbor_eq]
  exact Nat.le_sub_one_of_lt hN_lt
