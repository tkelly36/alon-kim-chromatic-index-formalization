import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.SaturatedNeighborClassPartition
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformT2OrientedIncidenceBound]
theorem ThreeUniformT2OrientedIncidenceBound
    (D : ℕ) {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E) (S : ThreeUniformThreeSimpleLocalSetup D F f) :
    2 * S.WXb - (D : ℝ) * S.V1.card ≤ ∑ g ∈ S.V2, S.crossDegree g := by
-- BODY
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let N := Finset.univ.filter (fun g : E => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  let a (v x : V) : ℝ := ((Finset.univ.filter
    (fun g : E => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let c (g : E) : ℝ := ∑ x ∈ F.edge g ∩ S.Xb,
    ∑ v ∈ F.edge f \ F.edge g, a v x
  have ha (v x : V) : 0 ≤ a v x := Nat.cast_nonneg _
  have hu : UniformHypergraph F 3 := S.class_mem.1
  have hpart := SaturatedNeighborClassPartition F f 3 D hu S.class_mem.2.2
    S.saturated_neighbors
  have hsmall := hpart.2.2.2
  have hXb (x : V) (hx : x ∈ S.Xb) : x ∈ S.X ∧ x ∉ F.edge f := by
    have h : x ∈ S.X := by rw [← S.X_partition]; exact Finset.mem_union_right _ hx
    exact ⟨h, (Finset.mem_filter.mp (S.X_eq ▸ h)).2.1⟩
  have hXs (x : V) (hx : x ∈ S.Xs) : x ∉ F.edge f := by
    have h : x ∈ S.X := by rw [← S.X_partition]; exact Finset.mem_union_left _ hx
    exact (Finset.mem_filter.mp (S.X_eq ▸ h)).2.1
  have hrow (g : E) (hg : g ∈ N) : ∃ u ∈ F.edge f,
      u ∈ F.edge g ∧ ∀ v ∈ F.edge f, v ∈ F.edge g ↔ v = u := by
    obtain ⟨hne, u, hu'⟩ := (Finset.mem_filter.mp hg).2
    obtain ⟨hug, huf⟩ := Finset.mem_inter.mp hu'
    refine ⟨u, huf, hug, fun v hv => ⟨fun hvg => ?_, fun h => h ▸ hug⟩⟩
    exact Finset.card_le_one.mp (hsmall g hne) _
      (Finset.mem_inter.mpr ⟨hvg, hv⟩) _ hu'
  have horient (x : V) :
      2 * (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, a v x) =
      ∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => v ≠ u), a u x * a v x := by
    rw [FiniteUnorderedPairProductSum]
    have hsym : (∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => v < u),
        a u x * a v x) =
        ∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => u < v), a u x * a v x := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu'
      apply Finset.sum_congr rfl
      intro v hv
      simp only [mul_comm]
    have hsplit : (∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => v ≠ u),
        a u x * a v x) =
        (∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => u < v), a u x * a v x) +
        ∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => v < u), a u x * a v x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu'
      simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      rcases lt_trichotomy u v with h | h | h <;>
        simp [ne_of_lt, ne_of_gt, not_lt_of_gt, *]
    rw [hsplit, hsym]
    ring
  have hcount (x u : V) (hx : x ∈ S.Xb) (hu' : u ∈ F.edge f) :
      a u x = ∑ g ∈ N, if u ∈ F.edge g ∧ x ∈ F.edge g then (1 : ℝ) else 0 := by
    have heq : Finset.univ.filter (fun g : E => u ∈ F.edge g ∧ x ∈ F.edge g) =
        N.filter (fun g => u ∈ F.edge g ∧ x ∈ F.edge g) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, N]
      constructor
      · intro h
        refine ⟨⟨?_, u, Finset.mem_inter.mpr ⟨h.1, hu'⟩⟩, h⟩
        intro he
        exact (hXb x hx).2 (he ▸ h.2)
      · exact fun h => h.2
    change ((Finset.univ.filter (fun g : E => u ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ) = _
    rw [heq]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter,
      Nat.cast_ite, Nat.cast_zero]
  have htotal : 2 * S.WXb = ∑ g ∈ N, c g := by
    rw [S.WXb_is_weight_of_Xb, Finset.mul_sum]
    change (∑ x ∈ S.Xb, 2 * (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, a v x)) = _
    simp_rw [horient]
    have hex (x : V) (hx : x ∈ S.Xb) :
        (∑ u ∈ F.edge f, ∑ v ∈ (F.edge f).filter (fun v => v ≠ u), a u x * a v x) =
        ∑ g ∈ N, if x ∈ F.edge g then ∑ v ∈ F.edge f \ F.edge g, a v x else 0 := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun u hu' => congrArg
        (fun z : ℝ => z * ∑ v ∈ (F.edge f).filter (fun v => v ≠ u), a v x)
        (hcount x u hx hu'))]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      obtain ⟨u, huf, hug, hur⟩ := hrow g hg
      by_cases hxg : x ∈ F.edge g
      · rw [if_pos hxg, Finset.sum_eq_single u]
        · simp only [hug, hxg, and_self, if_true, one_mul]
          congr 1
          ext v
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          exact and_congr_right (fun hv => not_congr (hur v hv).symm)
        · intro v hv hne
          simp [hxg, (hur v hv).mp.mt hne]
        · exact fun h => (h huf).elim
      · simp [hxg]
    rw [Finset.sum_congr rfl hex, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    change _ = ∑ x ∈ F.edge g ∩ S.Xb, _
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  have hV1 (g : E) (hg : g ∈ S.V1) : c g ≤ D := by
    have hgN : g ∈ N := by
      have := Finset.mem_filter.mp (S.V1_eq ▸ hg)
      exact this.1
    obtain ⟨u, huf, hug, hur⟩ := hrow g hgN
    obtain ⟨y, hy⟩ := (Finset.mem_filter.mp (S.V1_eq ▸ hg)).2
    obtain ⟨hyg, hys⟩ := Finset.mem_inter.mp hy
    have hcard : (F.edge g ∩ S.Xb).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx z hz
      obtain ⟨hxg, hxb⟩ := Finset.mem_inter.mp hx
      obtain ⟨hzg, hzb⟩ := Finset.mem_inter.mp hz
      by_contra hxz
      have hyu : y ≠ u := fun h => hXs y hys (h ▸ huf)
      have hxu : x ≠ u := fun h => (hXb x hxb).2 (h ▸ huf)
      have hzu : z ≠ u := fun h => (hXb z hzb).2 (h ▸ huf)
      have hyx : y ≠ x := fun h => Finset.disjoint_left.mp S.Xs_disjoint_Xb hys (h ▸ hxb)
      have hyz : y ≠ z := fun h => Finset.disjoint_left.mp S.Xs_disjoint_Xb hys (h ▸ hzb)
      have hsub : ({y, x, z, u} : Finset V) ⊆ F.edge g := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      have hh := Finset.card_le_card hsub
      rw [hu g] at hh
      simp [hyx, hyz, hyu, hxz, hxu, hzu] at hh
    have hcol (x : V) (hx : x ∈ F.edge g ∩ S.Xb) :
        (∑ v ∈ F.edge f \ F.edge g, a v x) ≤ D := by
      calc
        _ ≤ ∑ v ∈ F.edge f, a v x := Finset.sum_le_sum_of_subset_of_nonneg
          Finset.sdiff_subset (fun v _ _ => ha v x)
        _ = S.vertexDegreeIntoF x := (S.vertexDegreeIntoF_eq x).symm
        _ ≤ D := S.column_bound x (hXb x (Finset.mem_inter.mp hx).2).1
    calc
      c g ≤ ∑ x ∈ F.edge g ∩ S.Xb, (D : ℝ) := Finset.sum_le_sum hcol
      _ = ((F.edge g ∩ S.Xb).card : ℝ) * D := by simp
      _ ≤ 1 * (D : ℝ) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
      _ = D := one_mul _
  have hV2 (g : E) (hg : g ∈ S.V2) : c g = S.crossDegree g := by
    have heq : F.edge g ∩ S.Xb = F.edge g \ F.edge f := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1,
          (hXb x (Finset.mem_inter.mp hx).2).2⟩
      · rw [Finset.card_sdiff, hu g, (S.V2_edge_shape g hg).2,
          Finset.inter_comm, (S.V2_edge_shape g hg).1]
    rw [S.crossDegree_eq]
    change (∑ x ∈ F.edge g ∩ S.Xb, _) = _
    rw [heq]
  have hsplit : (∑ g ∈ N, c g) = (∑ g ∈ S.V1, c g) + ∑ g ∈ S.V2, c g := by
    change (∑ g ∈ Finset.univ.filter (fun g : E =>
      g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty), c g) = _
    rw [← S.V_partition, Finset.sum_union S.V1_disjoint_V2]
  have hbound : (∑ g ∈ S.V1, c g) ≤ (D : ℝ) * S.V1.card := by
    calc
      _ ≤ ∑ g ∈ S.V1, (D : ℝ) := Finset.sum_le_sum hV1
      _ = _ := by simp [mul_comm]
  rw [htotal, hsplit, Finset.sum_congr rfl hV2]
  linarith
