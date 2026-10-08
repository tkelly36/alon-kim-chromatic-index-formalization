import Tablet.TablePairFillingBound
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformIncidencePairFillingBound]
theorem ThreeUniformIncidencePairFillingBound
    {D : ℕ} {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {F : MultiHypergraph V E} {f : E} (S : ThreeUniformThreeSimpleLocalSetup D F f)
    (Y : Finset V) (C T : ℝ) (q : ℕ) (r : ℝ)
    (hC : 0 < C) (hT : 0 < T) (hq : q = Nat.floor (T / C))
    (hr : r = T - (q : ℝ) * C)
    (hcol : ∀ x ∈ Y, S.vertexDegreeIntoF x ≤ C)
    (htot : (∑ x ∈ Y, S.vertexDegreeIntoF x) ≤ T) :
    (∑ x ∈ Y, ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f),
      ∏ v ∈ p, (((Finset.univ : Finset E).filter
        (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)) ≤
      (1 / 3 : ℝ) * ((q : ℝ) * C ^ 2 + r ^ 2) := by
-- BODY
  classical
  let d : V → V → ℝ := fun v x =>
    (((Finset.univ : Finset E).filter (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let weight : Finset V → ℝ := fun Y => ∑ x ∈ Y,
    ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, d v x
  change weight Y ≤ _
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
