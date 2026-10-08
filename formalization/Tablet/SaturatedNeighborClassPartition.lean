import Tablet.MaxDegreeAtMost
import Tablet.UniformHypergraph

open scoped BigOperators

-- [TABLET NODE: SaturatedNeighborClassPartition]
theorem SaturatedNeighborClassPartition
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (e : E) (k D : ℕ)
    (hu : UniformHypergraph H k) (hd : MaxDegreeAtMost H D)
    (hN : (Finset.univ.filter (fun g : E =>
      g ≠ e ∧ (H.edge g ∩ H.edge e).Nonempty)).card = k * (D - 1)) :
    let C := fun v : V => Finset.univ.filter (fun g : E => g ≠ e ∧ v ∈ H.edge g)
    (∀ v ∈ H.edge e, (C v).card = D - 1) ∧
    (∀ v ∈ H.edge e, ∀ w ∈ H.edge e, v ≠ w → Disjoint (C v) (C w)) ∧
    (H.edge e).biUnion C = Finset.univ.filter (fun g : E =>
      g ≠ e ∧ (H.edge g ∩ H.edge e).Nonempty) ∧
    (∀ g : E, g ≠ e → (H.edge g ∩ H.edge e).card ≤ 1) := by
-- BODY
  classical
  dsimp only
  let C := fun v : V => Finset.univ.filter (fun g : E => g ≠ e ∧ v ∈ H.edge g)
  let N := Finset.univ.filter (fun g : E => g ≠ e ∧ (H.edge g ∩ H.edge e).Nonempty)
  have hC (v : V) (hv : v ∈ H.edge e) : (C v).card ≤ D - 1 := by
    have hm : e ∈ Finset.univ.filter (fun g => v ∈ H.edge g) := by simp [hv]
    have hc : C v = (Finset.univ.filter (fun g => v ∈ H.edge g)).erase e := by
      ext g
      simp [C]
    rw [hc, Finset.card_erase_of_mem hm]
    exact Nat.sub_le_sub_right (hd v) 1
  have hdouble : (∑ v ∈ H.edge e, (C v).card) =
      ∑ g ∈ N, (H.edge g ∩ H.edge e).card := by
    have hc (v : V) (hv : v ∈ H.edge e) :
        C v = N.filter (fun g => v ∈ H.edge g) := by
      ext g
      simp only [C, N, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨⟨h.1, ⟨v, Finset.mem_inter.mpr ⟨h.2, hv⟩⟩⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    calc
      _ = ∑ v ∈ H.edge e, (N.filter (fun g => v ∈ H.edge g)).card :=
        Finset.sum_congr rfl (fun v hv => congrArg Finset.card (hc v hv))
      _ = ∑ g ∈ N, ((H.edge e).filter (fun v => v ∈ H.edge g)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm
      _ = _ := by simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
  have hlo (g : E) (hg : g ∈ N) : 1 ≤ (H.edge g ∩ H.edge e).card :=
    Finset.card_pos.mpr (Finset.mem_filter.mp hg).2.2
  have hupper : (∑ v ∈ H.edge e, (C v).card) ≤ k * (D - 1) := by
    calc
      _ ≤ ∑ v ∈ H.edge e, (D - 1) := Finset.sum_le_sum hC
      _ = _ := by simp [hu e]
  have hlower : k * (D - 1) ≤ ∑ g ∈ N, (H.edge g ∩ H.edge e).card := by
    calc
      _ = ∑ g ∈ N, 1 := by simpa [N] using hN.symm
      _ ≤ _ := Finset.sum_le_sum hlo
  have htotal : (∑ v ∈ H.edge e, (C v).card) = k * (D - 1) := by omega
  have hCsat (v : V) (hv : v ∈ H.edge e) : (C v).card = D - 1 := by
    apply (Finset.sum_eq_sum_iff_of_le hC).mp _ v hv
    simpa [hu e] using htotal
  have hone (g : E) (hg : g ∈ N) : (H.edge g ∩ H.edge e).card = 1 := by
    symm
    apply (Finset.sum_eq_sum_iff_of_le hlo).mp _ g hg
    simpa [N, hN] using (hdouble.symm.trans htotal).symm
  have hs (g : E) (hg : g ≠ e) : (H.edge g ∩ H.edge e).card ≤ 1 := by
    by_cases hn : (H.edge g ∩ H.edge e).Nonempty
    · exact (hone g (by simp [N, hg, hn])).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  refine ⟨hCsat, ?_, ?_, hs⟩
  · intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro g hgv hgw
    obtain ⟨hge, hvg⟩ := (Finset.mem_filter.mp hgv).2
    have hwg := (Finset.mem_filter.mp hgw).2.2
    exact hvw ((Finset.card_le_one.mp (hs g hge)) v
      (Finset.mem_inter.mpr ⟨hvg, hv⟩) w (Finset.mem_inter.mpr ⟨hwg, hw⟩))
  · ext g
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, hge, hvg⟩
      exact ⟨hge, v, Finset.mem_inter.mpr ⟨hvg, hv⟩⟩
    · rintro ⟨hge, v, hv⟩
      exact ⟨v, (Finset.mem_inter.mp hv).2, hge, (Finset.mem_inter.mp hv).1⟩
