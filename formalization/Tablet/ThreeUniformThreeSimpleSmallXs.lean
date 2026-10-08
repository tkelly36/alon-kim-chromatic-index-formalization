import Tablet.TablePairFillingBound
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleSmallXs]
theorem ThreeUniformThreeSimpleSmallXs :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
      ∀ F : MultiHypergraph V E, ∀ f : E,
        ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
          S.P ≤ 1.031 * (D : ℝ) ^ (2 : ℕ) - 9 * (D : ℝ) →
          ∀ delta : ℝ,
            0 ≤ delta →
            S.P ≤ (1 + delta) * (D : ℝ) ^ (2 : ℕ) - 9 * (D : ℝ) →
            S.totalXs ≤ (8 / 5 : ℝ) * delta * (D : ℝ) ∧
              S.WXs ≤ (2 / 75 : ℝ) * delta * (D : ℝ) ^ (2 : ℕ) := by
-- BODY
  classical
  intro D V E _ _ _ _ F f S hcut delta hdelta hP
  have hD : (0 : ℝ) < D := by
    exact_mod_cast (show 0 < D by have := S.D_large; omega)
  let d : V → V → ℝ := fun v x =>
    (((Finset.univ : Finset E).filter (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let weight : Finset V → ℝ := fun Y => ∑ x ∈ Y,
    ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, d v x
  have hdeg (x) : 0 ≤ S.vertexDegreeIntoF x := by
    rw [S.vertexDegreeIntoF_eq]
    positivity
  have hs : 0 ≤ S.totalXs := by
    rw [S.totalXs_eq_sum]
    exact Finset.sum_nonneg (fun x _ => hdeg x)
  have hws : weight S.Xs = S.WXs := S.WXs_is_weight_of_Xs.symm
  have hwb : weight S.Xb = S.WXb := S.WXb_is_weight_of_Xb.symm
  have filling (Y : Finset V) (C T : ℝ) (q : ℕ) (r : ℝ)
      (hC : 0 < C) (hT : 0 < T) (hq : q = Nat.floor (T / C))
      (hr : r = T - (q : ℝ) * C)
      (hcol : ∀ x ∈ Y, S.vertexDegreeIntoF x ≤ C)
      (htot : (∑ x ∈ Y, S.vertexDegreeIntoF x) ≤ T) :
      weight Y ≤ (1 / 3 : ℝ) * ((q : ℝ) * C ^ 2 + r ^ 2) := by
    let ev : Fin 3 ≃ F.edge f := (Finset.equivFinOfCardEq (S.class_mem.1 f)).symm
    let ex : Fin Y.card ≃ Y := (Finset.equivFin Y).symm
    let v : Fin 3 → V := fun i => (ev i).val
    let x : Fin Y.card → V := fun j => (ex j).val
    have hv (i) : v i ∈ F.edge f := (ev i).property
    have hvcover (y) (hy : y ∈ F.edge f) : ∃ i, v i = y :=
      ⟨ev.symm ⟨y, hy⟩, congrArg Subtype.val (ev.apply_symm_apply _)⟩
    have hvsum (a : V → ℝ) : (∑ i, a (v i)) = ∑ y ∈ F.edge f, a y :=
      (ev.sum_comp (fun y => a y.val)).trans (Finset.sum_coe_sort _ _)
    have hxsum (a : V → ℝ) : (∑ j, a (x j)) = ∑ y ∈ Y, a y :=
      (ex.sum_comp (fun y => a y.val)).trans (Finset.sum_coe_sort _ _)
    have hcolumn (j) : (∑ i, d (v i) (x j)) = S.vertexDegreeIntoF (x j) := by
      rw [hvsum (fun y => d y (x j)), S.vertexDegreeIntoF_eq]
    have hpairs (y : V) :
        (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
          (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ z ∈ p, d z y) =
        ∑ i : Fin 3, ∑ k : Fin 3, if i < k then d (v i) y * d (v k) y else 0 := by
      let emb : Fin 3 ↪ V := ⟨v, fun i j h => ev.injective (Subtype.ext h)⟩
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
    have h := TablePairFillingBound (by norm_num : 2 ≤ 3) C T q r
      (fun i j => d (v i) (x j)) hC hT hq hr
      (fun _ _ => Nat.cast_nonneg _)
      (fun j => by rw [hcolumn]; exact hcol _ (ex j).property)
      (by rw [Finset.sum_comm]; simp_rw [hcolumn]; rw [hxsum]; exact htot)
    have hw : weight Y = ∑ j, ∑ i : Fin 3, ∑ k : Fin 3,
        if i < k then d (v i) (x j) * d (v k) (x j) else 0 := by
      dsimp [weight]
      simp_rw [hpairs]
      exact (hxsum _).symm
    rw [hw]
    norm_num at h ⊢
    exact h
  by_cases hz : S.totalXs = 0
  · have hzero (x) (hx : x ∈ S.Xs) : S.vertexDegreeIntoF x = 0 := by
      have hle := Finset.single_le_sum (fun y (_ : y ∈ S.Xs) => hdeg y) hx
      rw [← S.totalXs_eq_sum, hz] at hle
      exact le_antisymm hle (hdeg x)
    have hd0 (x) (hx : x ∈ S.Xs) (v) (hv : v ∈ F.edge f) : d v x = 0 := by
      have hle := Finset.single_le_sum (fun y (_ : y ∈ F.edge f) =>
        show 0 ≤ d y x from Nat.cast_nonneg _) hv
      change d v x ≤ ∑ y ∈ F.edge f, d y x at hle
      have he : (∑ y ∈ F.edge f, d y x) = 0 :=
        (S.vertexDegreeIntoF_eq x).symm.trans (hzero x hx)
      rw [he] at hle
      exact le_antisymm hle (Nat.cast_nonneg _)
    have hw0 : S.WXs = 0 := by
      rw [← hws]
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨hcard, hsub⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < p.card by omega)
      exact Finset.prod_eq_zero hv (hd0 x hx v (hsub hv))
    rw [hz, hw0]
    constructor <;> positivity
  have hspos : 0 < S.totalXs := lt_of_le_of_ne hs (Ne.symm hz)
  have hsmall : S.WXs ≤ (1 / 3 : ℝ) * S.totalXs ^ 2 := by
    have h := filling S.Xs S.totalXs S.totalXs 1 0 hspos hspos
      (by simp [ne_of_gt hspos]) (by ring)
      (fun x hx => by
        rw [S.totalXs_eq_sum]
        exact Finset.single_le_sum (fun y _ => hdeg y) hx)
      (by rw [S.totalXs_eq_sum])
    simpa [hws] using h
  have hbig : S.WXb ≤ (1 / 3 : ℝ) * (5 * (D : ℝ) ^ 2 + ((D : ℝ) - S.totalXs) ^ 2) := by
    have ht : 0 < 6 * (D : ℝ) - S.totalXs := by linarith [S.Xs_total_cutoff]
    have hfloor : 5 = Nat.floor ((6 * (D : ℝ) - S.totalXs) / D) := by
      symm
      apply (Nat.floor_eq_iff (by positivity : 0 ≤ (6 * (D : ℝ) - S.totalXs) / D)).mpr
      constructor
      · rw [le_div_iff₀ hD]; norm_num; linarith [S.Xs_total_cutoff]
      · rw [div_lt_iff₀ hD]; norm_num; linarith
    have h := filling S.Xb D (6 * (D : ℝ) - S.totalXs) 5
      ((D : ℝ) - S.totalXs) hD ht hfloor (by norm_num; ring)
      (fun x hx => S.column_bound x (by rw [S.Xb_eq] at hx; exact (Finset.mem_sdiff.mp hx).1))
      (by rw [← S.totalXb_eq_sum, S.Xb_total_eq, S.totalX_value]; linarith)
    simpa [hwb] using h
  have hquad : (2 / 3 : ℝ) * S.totalXs * D - (2 / 3 : ℝ) * S.totalXs ^ 2 ≤
      delta * (D : ℝ) ^ 2 := by
    nlinarith [S.pair_identity, S.Y_nonnegative, S.W_split]
  have hfixed : (2 / 3 : ℝ) * S.totalXs * D - (2 / 3 : ℝ) * S.totalXs ^ 2 ≤
      (0.031 : ℝ) * (D : ℝ) ^ 2 := by
    nlinarith [S.pair_identity, S.Y_nonnegative, S.W_split]
  have habs : S.totalXs ≤ (0.049 : ℝ) * D := by
    by_contra hn
    have hprod := mul_nonneg
      (show 0 ≤ S.totalXs - (0.049 : ℝ) * D by linarith)
      (show 0 ≤ (0.951 : ℝ) * D - S.totalXs by linarith [S.Xs_total_cutoff])
    nlinarith [sq_pos_of_pos hD]
  have hlinear : S.totalXs ≤ (8 / 5 : ℝ) * delta * D := by
    have hprod := mul_nonneg hs (sub_nonneg.mpr habs)
    have hscaled : S.totalXs * D ≤ (8 / 5 : ℝ) * delta * D * D := by
      nlinarith [mul_nonneg hs hD.le]
    exact (mul_le_mul_iff_left₀ hD).mp hscaled
  refine ⟨hlinear, ?_⟩
  have hsq := mul_le_mul_of_nonneg_left habs hs
  have hlast := mul_le_mul_of_nonneg_left hlinear
    (show 0 ≤ (0.049 : ℝ) * D by positivity)
  nlinarith [mul_nonneg hdelta (sq_nonneg (D : ℝ))]
