import Tablet.TablePairFillingBound
import Tablet.ThreeUniformSaturatedEdgeStructure
import Tablet.ThreeUniformThreeSimplePairLowerBound
import Tablet.ThreeUniformThreeSimplePairUpperCutoff
import Tablet.ThreeUniformThreeSimpleSmallXs
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleBigPartSize]
theorem ThreeUniformThreeSimpleBigPartSize :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
      ∀ F : MultiHypergraph V E, ∀ f : E,
        ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
          ∀ delta : ℝ,
            0 ≤ delta →
            delta ≤ 0.031 →
            S.P = (1 + delta) * (D : ℝ) ^ (2 : ℕ) - 9 * (D : ℝ) →
            S.Xb.card = 6 := by
-- BODY
  classical
  intro D V E _ _ _ _ F f S delta hdelta hdelta31 hP
  have hD100 : (100 : ℝ) ≤ D := by exact_mod_cast S.D_large
  have hD : (0 : ℝ) < D := by linarith
  have hdeg (x) : 0 ≤ S.vertexDegreeIntoF x := by
    rw [S.vertexDegreeIntoF_eq]
    positivity
  have hs : 0 ≤ S.totalXs := by
    rw [S.totalXs_eq_sum]
    exact Finset.sum_nonneg (fun x _ => hdeg x)
  have hbsub : S.Xb ⊆ S.X := by
    rw [S.Xb_eq]
    exact Finset.sdiff_subset
  have hbigTotal : 5 * (D : ℝ) < S.totalXb := by
    rw [S.Xb_total_eq, S.totalX_value]
    linarith [S.Xs_total_cutoff]
  have hcap : S.totalXb ≤ S.Xb.card * (D : ℝ) := by
    rw [S.totalXb_eq_sum]
    calc
      _ ≤ ∑ x ∈ S.Xb, (D : ℝ) := Finset.sum_le_sum (fun x hx => S.column_bound x (hbsub hx))
      _ = _ := by simp
  have hcard6 : 6 ≤ S.Xb.card := by
    by_contra hn
    have hn' : (S.Xb.card : ℝ) ≤ 5 := by exact_mod_cast (show S.Xb.card ≤ 5 by omega)
    nlinarith
  by_contra hn
  have hcard7 : 7 ≤ S.Xb.card := by omega
  have hne : S.Xb.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx, hmin⟩ := S.Xb.exists_min_image S.vertexDegreeIntoF hne
  let m := S.vertexDegreeIntoF x
  have hm0 : 0 ≤ m := hdeg x
  have hcut : S.P ≤ 1.031 * (D : ℝ) ^ 2 - 9 * D := by
    rw [hP]
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta31) (sq_nonneg (D : ℝ))]
  have hsmall := (ThreeUniformThreeSimpleSmallXs D F f S hcut delta hdelta hP.le).1
  have hs49 : S.totalXs ≤ (0.0496 : ℝ) * D := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta31) hD.le]
  have hmlow : (0.45 : ℝ) * D < m := by
    have := S.Xs_maximal_under_cutoff x hx
    dsimp [m]
    linarith
  have hminsum : (S.Xb.card : ℝ) * m ≤ S.totalXb := by
    rw [S.totalXb_eq_sum]
    calc
      _ = ∑ y ∈ S.Xb, m := by simp
      _ ≤ _ := Finset.sum_le_sum (fun y hy => hmin y hy)
  have hmup : m ≤ (6 / 7 : ℝ) * D := by
    have hc : (7 : ℝ) ≤ S.Xb.card := by exact_mod_cast hcard7
    have ht : S.totalXb ≤ 6 * ((D : ℝ) - 1) := by
      rw [S.Xb_total_eq, S.totalX_value]
      linarith
    nlinarith
  let d : V → V → ℝ := fun v x =>
    (((Finset.univ : Finset E).filter (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let weight : Finset V → ℝ := fun Y => ∑ x ∈ Y,
    ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, d v x
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
  have hxX : x ∈ S.X := hbsub hx
  have hr0 : 0 ≤ (D : ℝ) - 6 - m := by linarith
  have hrD : (D : ℝ) - 6 - m < D := by linarith
  have ht : 0 < 6 * ((D : ℝ) - 1) - m := by linarith
  have hfloor : 5 = Nat.floor ((6 * ((D : ℝ) - 1) - m) / D) := by
    symm
    apply (Nat.floor_eq_iff (by positivity : 0 ≤ (6 * ((D : ℝ) - 1) - m) / D)).mpr
    constructor
    · rw [le_div_iff₀ hD]; norm_num; linarith
    · rw [div_lt_iff₀ hD]; norm_num; linarith
  have heraseTotal : (∑ y ∈ S.X.erase x, S.vertexDegreeIntoF y) =
      6 * ((D : ℝ) - 1) - m := by
    have h := Finset.sum_erase_add S.X S.vertexDegreeIntoF hxX
    rw [← S.totalX_eq_sum, S.totalX_value] at h
    dsimp [m]
    linarith
  have herase := filling (S.X.erase x) D (6 * ((D : ℝ) - 1) - m) 5
    ((D : ℝ) - 6 - m) hD ht hfloor (by norm_num; ring)
    (fun y hy => S.column_bound y (Finset.mem_of_mem_erase hy)) heraseTotal.le
  have hmpos : 0 < m := by linarith
  have hsingle := filling {x} m m 1 0 hmpos hmpos
    (by simp [ne_of_gt hmpos]) (by ring)
    (by intro y hy; simpa using le_of_eq (congrArg S.vertexDegreeIntoF (Finset.mem_singleton.mp hy)))
    (by simp [m])
  have hweight : weight S.X = S.W := by
    rw [← S.X_partition]
    dsimp [weight]
    rw [Finset.sum_union S.Xs_disjoint_Xb]
    exact (congrArg₂ (· + ·) S.WXs_is_weight_of_Xs.symm S.WXb_is_weight_of_Xb.symm).trans S.W_split.symm
  have hsplit : weight (S.X.erase x) + weight {x} = S.W := by
    rw [← hweight]
    dsimp [weight]
    simpa using Finset.sum_erase_add S.X
      (fun y => ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, d v y) hxX
  have hrem : ((D : ℝ) - 6 - m) ^ 2 ≤ ((D : ℝ) - m) ^ 2 := by nlinarith
  have hwupper : S.W ≤ 2 * (D : ℝ) ^ 2 - (2 / 3 : ℝ) * m * (D - m) := by
    norm_num at herase hsingle
    nlinarith only [herase, hsingle, hsplit, hrem]
  have hprod : (0.45 : ℝ) * D * (D / 7) ≤ m * (D - m) := by
    apply mul_le_mul hmlow.le
    · linarith
    · positivity
    · linarith
  have hwlower : (2 - delta) * (D : ℝ) ^ 2 ≤ S.W := by
    nlinarith only [hP, S.pair_identity, S.Y_nonnegative, hD]
  have hdeltaprod := mul_nonneg (sub_nonneg.mpr hdelta31) (sq_nonneg (D : ℝ))
  nlinarith only [hwlower, hwupper, hprod, hdeltaprod, sq_pos_of_pos hD]
