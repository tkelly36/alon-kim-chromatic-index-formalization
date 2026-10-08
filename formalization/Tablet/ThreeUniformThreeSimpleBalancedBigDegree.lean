import Tablet.TablePairStability
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleBalancedBigDegree]
theorem ThreeUniformThreeSimpleBalancedBigDegree :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
      ∀ F : MultiHypergraph V E, ∀ f : E,
        ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
          ∀ delta : ℝ,
            0 ≤ delta →
            S.Xb.card = 6 →
            S.WXb ≥ (2 - delta) * (D : ℝ) ^ (2 : ℕ) →
            ∀ g : E, g ∈ S.V2 →
              |S.crossDegree g - (4 / 3 : ℝ) * (D : ℝ)| ≤
                Real.sqrt ((8 / 3 : ℝ) * delta) * (D : ℝ) := by
-- BODY
  classical
  intro D V E _ _ _ _ F f S delta hdelta hSix hweight g hg
  let ev : Fin 3 ≃ F.edge f := (Finset.equivFinOfCardEq (S.class_mem.1 f)).symm
  let ex : Fin 6 ≃ S.Xb := (Finset.equivFinOfCardEq hSix).symm
  let v : Fin 3 → V := fun i => (ev i).val
  let x : Fin 6 → V := fun j => (ex j).val
  have hv (i) : v i ∈ F.edge f := (ev i).property
  have hx (j) : x j ∈ S.Xb := (ex j).property
  have hvinj : Function.Injective v := fun i j h => ev.injective (Subtype.ext h)
  have hvcover (y) (hy : y ∈ F.edge f) : ∃ i, v i = y :=
    ⟨ev.symm ⟨y, hy⟩, congrArg Subtype.val (ev.apply_symm_apply _)⟩
  have hxcover (y) (hy : y ∈ S.Xb) : ∃ j, x j = y :=
    ⟨ex.symm ⟨y, hy⟩, congrArg Subtype.val (ex.apply_symm_apply _)⟩
  have hvsum (q : V → ℝ) : (∑ i, q (v i)) = ∑ y ∈ F.edge f, q y :=
    (ev.sum_comp (fun y => q y.val)).trans (Finset.sum_coe_sort _ _)
  have hxsum (q : V → ℝ) : (∑ j, q (x j)) = ∑ y ∈ S.Xb, q y :=
    (ex.sum_comp (fun y => q y.val)).trans (Finset.sum_coe_sort _ _)
  let d : V → V → ℝ := fun a b =>
    (((Finset.univ : Finset E).filter (fun e => a ∈ F.edge e ∧ b ∈ F.edge e)).card : ℝ)
  let A : Fin 3 → Fin 6 → ℝ := fun i j => d (v i) (x j)
  have hbX : S.Xb ⊆ S.X := by rw [S.Xb_eq]; exact Finset.sdiff_subset
  have hbnot (y) (hy : y ∈ S.Xb) : y ∉ F.edge f := by
    have hh := hbX hy
    rw [S.X_eq] at hh
    exact (Finset.mem_filter.mp hh).2.1
  have hcol (j) : (∑ i, A i j) ≤ (D : ℝ) := by
    change (∑ i, d (v i) (x j)) ≤ _
    rw [hvsum (fun b => d b (x j))]
    change (∑ b ∈ F.edge f, _) ≤ _
    rw [← S.vertexDegreeIntoF_eq]
    exact S.column_bound _ (hbX (hx j))
  have hpairs (y : V) :
      (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ z ∈ p, d z y) =
      ∑ i : Fin 3, ∑ k : Fin 3, if i < k then d (v i) y * d (v k) y else 0 := by
    let emb : Fin 3 ↪ V := ⟨v, hvinj⟩
    have hm : Finset.univ.map emb = F.edge f := by
      ext z
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => hi ▸ hv i, hvcover z⟩
    have hfilt : Finset.univ.filter (fun p : Finset V => p.card = 2 ∧ p ⊆ F.edge f) =
        (F.edge f).powersetCard 2 := by
      ext p
      simp [Finset.mem_powersetCard, and_comm]
    rw [hfilt, ← hm, Finset.powersetCard_map, Finset.sum_map]
    simp only [Finset.mapEmbedding_apply, RelEmbedding.coe_toEmbedding, Finset.prod_map]
    change (∑ p ∈ Finset.univ.powersetCard 2, ∏ i ∈ p, d (v i) y) = _
    have hfilt3 : Finset.univ.filter (fun p : Finset (Fin 3) => p.card = 2 ∧ p ⊆ Finset.univ) =
        (Finset.univ : Finset (Fin 3)).powersetCard 2 := by
      ext p
      simp [Finset.mem_powersetCard]
    rw [← hfilt3]
    simpa [Finset.sum_filter] using
      FiniteUnorderedPairProductSum (Finset.univ : Finset (Fin 3)) (fun i => d (v i) y)
  have htable : (∑ j : Fin 6, ∑ i : Fin 3, ∑ k : Fin 3,
      if i < k then A i j * A k j else 0) = S.WXb := by
    rw [S.WXb_is_weight_of_Xb]
    change (∑ j, ∑ i, ∑ k, if i < k then d (v i) (x j) * d (v k) (x j) else 0) = _
    rw [hxsum (fun y => ∑ i : Fin 3, ∑ k : Fin 3,
      if i < k then d (v i) y * d (v k) y else 0)]
    exact Finset.sum_congr rfl (fun y _ => (hpairs y).symm)
  obtain ⟨hgf, hgb⟩ := S.V2_edge_shape g hg
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hgf
  have hag : a ∈ F.edge g := Finset.mem_inter.mp (ha.symm ▸ Finset.mem_singleton_self a) |>.1
  have haf : a ∈ F.edge f := Finset.mem_inter.mp (ha.symm ▸ Finset.mem_singleton_self a) |>.2
  obtain ⟨i0, hi0⟩ := hvcover a haf
  have hdiff : F.edge g \ F.edge f = F.edge g ∩ S.Xb := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz).1, hbnot z (Finset.mem_inter.mp hz).2⟩
    · rw [Finset.card_sdiff, S.class_mem.1 g, Finset.inter_comm, hgf, hgb]
  obtain ⟨y, z, hyz, hyzset⟩ := Finset.card_eq_two.mp hgb
  have hyb : y ∈ S.Xb := (Finset.mem_inter.mp (hyzset.symm ▸ (by simp : y ∈ ({y,z} : Finset V)))).2
  have hzb : z ∈ S.Xb := (Finset.mem_inter.mp (hyzset.symm ▸ (by simp : z ∈ ({y,z} : Finset V)))).2
  obtain ⟨j1, hj1⟩ := hxcover y hyb
  obtain ⟨j2, hj2⟩ := hxcover z hzb
  have hj12 : j1 ≠ j2 := by intro he; exact hyz (hj1.symm.trans ((congrArg x he).trans hj2))
  have hrow (q : V → ℝ) :
      (∑ i : Fin 3, if i = i0 then 0 else q (v i)) = ∑ b ∈ F.edge f \ F.edge g, q b := by
    have heq (i) : i = i0 ↔ v i = a := by rw [← hi0]; exact hvinj.eq_iff.symm
    simp_rw [heq]
    rw [hvsum (fun b => if b = a then 0 else q b)]
    have hfilter : F.edge f \ F.edge g = (F.edge f).filter (fun b => b ≠ a) := by
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨hb, hbg⟩
        exact ⟨hb, fun he => hbg (he ▸ hag)⟩
      · rintro ⟨hb, hba⟩
        refine ⟨hb, fun hbg => hba ?_⟩
        exact Finset.mem_singleton.mp (ha ▸ Finset.mem_inter.mpr ⟨hbg, hb⟩)
    rw [hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b = a <;> simp [h]
  have hcross : (∑ i : Fin 3, if i = i0 then 0 else A i j1 + A i j2) = S.crossDegree g := by
    change (∑ i, if i = i0 then 0 else d (v i) (x j1) + d (v i) (x j2)) = _
    rw [hj1, hj2, hrow (fun b => d b y + d b z), S.crossDegree_eq, hdiff, hyzset]
    simp only [Finset.sum_pair hyz, Finset.sum_add_distrib]
    rfl
  by_contra hfail
  have hlt := lt_of_not_ge hfail
  let eta := |S.crossDegree g - (4 / 3 : ℝ) * D|
  have heta : 0 < eta := lt_of_le_of_lt (by positivity) hlt
  have hD : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by have := S.D_large; omega)
  have hstab := TablePairStability (by norm_num : 2 ≤ 3) (D : ℝ) eta A hD heta
    (fun i j => Nat.cast_nonneg _) hcol
    ⟨j1, j2, hj12, i0, by rw [hcross]; norm_num; exact le_rfl⟩
  rw [htable] at hstab
  norm_num at hstab
  have hsqrt := Real.sq_sqrt (show 0 ≤ (8 / 3 : ℝ) * delta by positivity)
  have hsquare : (Real.sqrt ((8 / 3 : ℝ) * delta) * (D : ℝ)) ^ 2 < eta ^ 2 :=
    pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
  rw [mul_pow, hsqrt] at hsquare
  nlinarith
