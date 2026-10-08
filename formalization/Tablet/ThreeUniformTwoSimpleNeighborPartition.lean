import Tablet.UniformHypergraph
import Tablet.TSimpleHypergraph
import Mathlib.Data.Finset.Powerset

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleNeighborPartition]
theorem ThreeUniformTwoSimpleNeighborPartition
    {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (f : E) (N : Finset E) (A : Finset V)
    (hu : UniformHypergraph H 3) (hs : TSimpleHypergraph H 2)
    (hA : Disjoint A (H.edge f)) (hAc : A.card ≤ 3)
    (hroot : ∀ e ∈ N, (H.edge e ∩ H.edge f).card = 1)
    (hmem : ∀ e, e ∈ N ↔ e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hN : N.card = 3 * (D - 1)) :
    let V1 := N.filter (fun e => (H.edge e ∩ A).card = 0)
    let V2 := N.filter (fun e => (H.edge e ∩ A).card = 2)
    let V3 := N.filter (fun e => (H.edge e ∩ A).card = 1)
    let S := ∑ e ∈ N, (H.edge e ∩ A).card
    V1.card + V2.card + V3.card = N.card ∧
      S = 2 * V2.card + V3.card ∧ V2.card ≤ 9 ∧
      (V1.card : ℝ) ≤ 3 * (D : ℝ) + 6 - (S : ℝ) ∧
      (∑ u ∈ H.edge f, ∑ y ∈ A,
        ((Finset.univ : Finset E).filter
          (fun e => u ∈ H.edge e ∧ y ∈ H.edge e)).card) = S := by
-- BODY
  classical
  dsimp only
  have hdis (e : E) : Disjoint (H.edge e ∩ H.edge f) (H.edge e ∩ A) := by
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hA.symm)
  have htwo (e : E) (he : e ∈ N) : (H.edge e ∩ A).card ≤ 2 := by
    have hsub : (H.edge e ∩ H.edge f) ∪ (H.edge e ∩ A) ⊆ H.edge e := by
      exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (hdis e), hroot e he, hu e] at hc
    omega
  have hpartition :
      (N.filter (fun e => (H.edge e ∩ A).card = 0)).card +
      (N.filter (fun e => (H.edge e ∩ A).card = 2)).card +
      (N.filter (fun e => (H.edge e ∩ A).card = 1)).card = N.card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have ht := htwo e he
    interval_cases h : (H.edge e ∩ A).card <;> simp [h]
  have hsum : (∑ e ∈ N, (H.edge e ∩ A).card) =
      2 * (N.filter (fun e => (H.edge e ∩ A).card = 2)).card +
      (N.filter (fun e => (H.edge e ∩ A).card = 1)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have ht := htwo e he
    interval_cases h : (H.edge e ∩ A).card <;> simp [h]
  have hnine : (N.filter (fun e => (H.edge e ∩ A).card = 2)).card ≤ 9 := by
    have hinj : Set.InjOn (fun e => (H.edge e ∩ H.edge f, H.edge e ∩ A))
        ↑(N.filter (fun e => (H.edge e ∩ A).card = 2)) := by
      intro e he g hg hpair
      have heN := (Finset.mem_filter.mp he).1
      have heA := (Finset.mem_filter.mp he).2
      have hcover : (H.edge e ∩ H.edge f) ∪ (H.edge e ∩ A) = H.edge e := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
        · rw [Finset.card_union_of_disjoint (hdis e), hroot e heN, heA, hu e]
      have hsub : H.edge e ⊆ H.edge g := by
        rw [← hcover, Prod.mk.inj hpair |>.1, Prod.mk.inj hpair |>.2]
        exact Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
      by_contra hne
      have hc := hs hne
      rw [Finset.inter_eq_left.mpr hsub, hu e] at hc
      omega
    have hc := Finset.card_le_card_of_injOn
      (fun e => (H.edge e ∩ H.edge f, H.edge e ∩ A))
      (s := N.filter (fun e => (H.edge e ∩ A).card = 2))
      (t := (H.edge f).powersetCard 1 ×ˢ A.powersetCard 2)
      (by
        intro e he
        rcases Finset.mem_filter.mp he with ⟨heN, heA⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hroot e heN⟩,
           Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, heA⟩⟩) hinj
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      hu f] at hc
    have hchoose : A.card.choose 2 ≤ 3 := by
      interval_cases h : A.card <;> norm_num [h]
    norm_num at hc
    omega
  refine ⟨hpartition, hsum, hnine, ?_, ?_⟩
  · have hnat : (N.filter (fun e => (H.edge e ∩ A).card = 0)).card +
        (∑ e ∈ N, (H.edge e ∩ A).card) ≤ 3 * D + 6 := by
      rw [hN] at hpartition
      omega
    have hreal : ((N.filter (fun e => (H.edge e ∩ A).card = 0)).card : ℝ) +
        ((∑ e ∈ N, (H.edge e ∩ A).card) : ℝ) ≤ 3 * (D : ℝ) + 6 := by
      exact_mod_cast hnat
    apply (le_sub_iff_add_le).mpr
    simpa only [Nat.cast_sum] using hreal
  · calc
      _ = ∑ e : E, (H.edge e ∩ H.edge f).card * (H.edge e ∩ A).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        calc
          _ = ∑ e : E, ∑ u ∈ H.edge f, ∑ y ∈ A,
              if u ∈ H.edge e ∧ y ∈ H.edge e then 1 else 0 := by
            simp_rw [Finset.sum_comm (s := A) (t := Finset.univ)]
            rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro e he
            simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
            simp [Finset.inter_comm]
      _ = ∑ e ∈ N, (H.edge e ∩ H.edge f).card * (H.edge e ∩ A).card := by
        symm
        apply Finset.sum_subset (Finset.subset_univ N)
        intro e he heN
        by_cases hef : e = f
        · subst e
          rw [Finset.disjoint_iff_inter_eq_empty.mp hA.symm]
          simp
        · have hn : ¬ (H.edge e ∩ H.edge f).Nonempty := by
            intro hn
            exact heN ((hmem e).mpr ⟨hef, hn⟩)
          rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hroot e he, one_mul]
