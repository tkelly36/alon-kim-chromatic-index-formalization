import Tablet.SaturatedEdgeStructure
import Tablet.SaturatedLineGraphPairBound
import Tablet.ThreeUniformTwoSimpleSmallPairsBound
import Tablet.ThreeUniformTwoSimpleDegreeToBigBound
import Tablet.ThreeUniformTwoSimpleTripleBound
import Tablet.LocalBParameter
import Mathlib.LinearAlgebra.Matrix.Permanent
import Tablet.FiniteSortedPaddedSlots
import Tablet.FiniteUnorderedPairProductSum

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleSaturatedMatrixCertificate]
theorem ThreeUniformTwoSimpleSaturatedMatrixCertificate
    (D : ℕ) (hD : 0 < D)
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E)
    (hH : H ∈ HypergraphClass (V := V) (E := E) 3 2 D) (f : E)
    (hdeg : ∀ y ∈ H.edge f, HypergraphDegree H y = D)
    (hN : ((Finset.univ : Finset E).filter
      (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)).card = 3 * (D - 1)) :
    let B : ℝ := D + 18 * (D : ℝ) ^ ((2 : ℝ) / 3)
    let r : ℝ := 1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)
    ∃ (n : ℕ) (hn : 3 ≤ n) (A : Matrix (Fin 3) (Fin n) ℝ),
      (∃ (v : Fin 3 → V) (x : Fin n → Option V),
        Function.Injective v ∧ (∀ y, y ∈ H.edge f ↔ ∃ i, v i = y) ∧
        (∀ j k y, x j = some y → x k = some y → j = k) ∧
        (∀ y, (∃ j, x j = some y) ↔
          y ∉ H.edge f ∧
          (D : ℝ) ^ ((2 : ℝ) / 3) ≤
            ∑ i : Fin 3, (((Finset.univ : Finset E).filter
              (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)) ∧
        (∀ i j, A i j = (x j).elim 0 (fun y =>
          (((Finset.univ : Finset E).filter
            (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ) / B))) ∧
      (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) ∧
      (∀ j, (∑ i : Fin 3, A i j) ≤ 1) ∧
      (∀ j k : Fin n, (j : ℕ) ≤ (k : ℕ) →
        (∑ i : Fin 3, A i k) ≤ ∑ i : Fin 3, A i j) ∧
      (∑ j : Fin n, ∑ i : Fin 3, A i j) ≤ 3 ∧
      @LocalBParameter E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) f ≤
        1 - (2 : ℝ) / 9 + (2 : ℝ) / 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) +
          8 / (9 * (D : ℝ)) +
          r ^ 2 / 9 * (∑ j : Fin n, ∑ i : Fin 3, ∑ i' : Fin 3,
            if i < i' then A i j * A i' j else 0) +
          r ^ 3 / 27 * Matrix.permanent (fun i j : Fin 3 => A i (Fin.castLE hn j)) -
          r / 27 * (∑ i : Fin 3, ∑ j : Fin 3, A i (Fin.castLE hn j)) := by
-- BODY
  classical
  let ev : Fin 3 ≃ H.edge f := (Finset.equivFinOfCardEq (hH.1 f)).symm
  let v : Fin 3 → V := fun i => (ev i).val
  have hv (i) : v i ∈ H.edge f := (ev i).property
  have hvinj : Function.Injective v := fun i j h => ev.injective (Subtype.ext h)
  have hcover (y) (hy : y ∈ H.edge f) : ∃ i, v i = y :=
    ⟨ev.symm ⟨y, hy⟩, congrArg Subtype.val (ev.apply_symm_apply _)⟩
  have hrootSum (g : V → ℝ) : (∑ i, g (v i)) = ∑ y ∈ H.edge f, g y := by
    exact (ev.sum_comp (fun y => g y.val)).trans (Finset.sum_coe_sort _ _)
  let a : Fin 3 → V → ℝ := fun i y =>
    (((Finset.univ : Finset E).filter
      (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)
  have ha0 (i y) : 0 ≤ a i y := Nat.cast_nonneg _
  let X := (Finset.univ : Finset V).filter (fun y => y ∉ H.edge f ∧
    ((Finset.univ : Finset E).filter
      (fun e => (H.edge e ∩ H.edge f).Nonempty ∧ y ∈ H.edge e)).Nonempty)
  have hX (y) : y ∈ X ↔ y ∉ H.edge f ∧
      ∃ e : E, e ≠ f ∧ y ∈ H.edge e ∧ (H.edge e ∩ H.edge f).Nonempty := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, Finset.nonempty_def]
    constructor
    · rintro ⟨hy, e, he, hye⟩
      exact ⟨hy, e, fun hef => hy (hef ▸ hye), hye, he⟩
    · rintro ⟨hy, e, _, hye, he⟩
      exact ⟨hy, e, he, hye⟩
  obtain ⟨hinter, hcolNat, hrowNat⟩ := SaturatedEdgeStructure D H hH f hN
  have hone (e : E) (he : e ≠ f) (hn : (H.edge e ∩ H.edge f).Nonempty) :
      (H.edge e ∩ H.edge f).card = 1 :=
    Nat.le_antisymm (hinter e he) (Finset.card_pos.mpr hn)
  have hcol (y) (hy : y ∈ X) : (∑ i, a i y) ≤ (D : ℝ) := by
    change (∑ i, (((Finset.univ : Finset E).filter
      (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)) ≤ _
    rw [hrootSum (fun z => (((Finset.univ : Finset E).filter
      (fun e => z ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ))]
    exact_mod_cast hcolNat y hy
  have hrow (i) : (∑ y ∈ X, a i y) = 2 * ((D : ℝ) - 1) := by
    have heq (y) (hy : y ∈ X) :
        (Finset.univ.filter (fun e : E => v i ∈ H.edge e ∧ y ∈ H.edge e)) =
        (Finset.univ.filter (fun e : E => e ≠ f ∧ v i ∈ H.edge e ∧ y ∈ H.edge e)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨fun hef => ((hX y).mp hy).1 (hef ▸ h.2), h⟩, fun h => h.2⟩
    have hh := hrowNat (v i) (hv i)
    have hh' : (∑ y ∈ X, a i y) = (2 * (D - 1) : ℕ) := by
      calc
        _ = ∑ y ∈ X, (((Finset.univ : Finset E).filter
            (fun e => e ≠ f ∧ v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [a]
          rw [heq y hy]
        _ = _ := by exact_mod_cast hh
    rw [hh', Nat.cast_mul, Nat.cast_sub (by omega)]
    norm_num
  let Xs := X.filter (fun y => (∑ i, a i y) < (D : ℝ) ^ ((2 : ℝ) / 3))
  let Xb := X \ Xs
  have hbX : Xb ⊆ X := Finset.sdiff_subset
  have hbig (i) : (∑ y ∈ Xb, a i y) ≤
      (D : ℝ) + 18 * (D : ℝ) ^ ((2 : ℝ) / 3) :=
    ThreeUniformTwoSimpleDegreeToBigBound D H hH f v hv hcover
      (fun i => hdeg _ (hv i)) hN X Xs Xb a hX (fun _ _ => rfl)
      hone hcol hrow rfl rfl i
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hthreshold : (0 : ℝ) < (D : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hDreal _
  have hbigmem (y) : y ∈ Xb ↔ y ∉ H.edge f ∧
      (D : ℝ) ^ ((2 : ℝ) / 3) ≤ ∑ i, a i y := by
    simp only [Xb, Xs, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hy, hs⟩
      exact ⟨((hX y).mp hy).1, le_of_not_gt (fun h => hs ⟨hy, h⟩)⟩
    · rintro ⟨hyf, ht⟩
      have hp : 0 < ∑ i, a i y := lt_of_lt_of_le hthreshold ht
      obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt
        (show (∑ _i : Fin 3, (0 : ℝ)) < ∑ i, a i y by simpa using hp)
      have hic : 0 < (Finset.univ.filter
          (fun e : E => v i ∈ H.edge e ∧ y ∈ H.edge e)).card := by
        exact_mod_cast (show (0 : ℝ) < (((Finset.univ : Finset E).filter
          (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ) from hi)
      obtain ⟨e, he⟩ := Finset.card_pos.mp hic
      obtain ⟨hie, hye⟩ := (Finset.mem_filter.mp he).2
      have hyX : y ∈ X := (hX y).mpr ⟨hyf, e, fun hef => hyf (hef ▸ hye),
        hye, v i, Finset.mem_inter.mpr ⟨hie, hv i⟩⟩
      exact ⟨hyX, fun h => (not_lt_of_ge ht) h.2⟩
  obtain ⟨x, hxinj, hxcover, hxmono, hxsum, hxdummy, hxtop⟩ :=
    FiniteSortedPaddedSlots Xb (fun y => ∑ i, a i y)
      (fun y _ => Finset.sum_nonneg (fun i _ => ha0 i y))
  let n := max 3 Xb.card
  have hn : 3 ≤ n := le_max_left _ _
  let B : ℝ := D + 18 * (D : ℝ) ^ ((2 : ℝ) / 3)
  have hB : 0 < B := by dsimp [B]; positivity
  have hDB : (D : ℝ) ≤ B := le_add_of_nonneg_right (by positivity)
  let d : Fin 3 → Fin n → ℝ := fun i j => (x j).elim 0 (a i)
  let A : Matrix (Fin 3) (Fin n) ℝ := fun i j => d i j / B
  have hd0 (i j) : 0 ≤ d i j := by
    cases hx : x j <;> simp [d, hx, ha0]
  have hdcol (j) : (∑ i, d i j) = (x j).elim 0 (fun y => ∑ i, a i y) := by
    cases hx : x j <;> simp [d, hx]
  have hdle (j) : (∑ i, d i j) ≤ (D : ℝ) := by
    rw [hdcol]
    cases hx : x j with
    | none => simp [le_of_lt hDreal]
    | some y => exact hcol y (hbX ((hxcover y).mp ⟨j, hx⟩))
  have hdsum (i) : (∑ j, d i j) = ∑ y ∈ Xb, a i y := hxsum (a i)
  have hAcol (j) : (∑ i, A i j) ≤ 1 := by
    simp only [A, ← Finset.sum_div]
    exact (div_le_one hB).mpr ((hdle j).trans hDB)
  have hAsum : (∑ j, ∑ i, A i j) ≤ 3 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [A, ← Finset.sum_div, hdsum]
        exact (div_le_one hB).mpr (hbig i)
      _ = 3 := by simp
  have htriple := ThreeUniformTwoSimpleTripleBound D H hH f v hv hcover
    (fun i => hdeg _ (hv i)) hN X Xs Xb (fun j => x (Fin.castLE hn j)) a
    hX hone hcol hrow (fun _ _ => rfl) rfl rfl hbX
    (fun j y hj => (hxcover y).mp ⟨Fin.castLE hn j, hj⟩)
    (fun j k y hj hk => Fin.ext (congrArg (fun q : Fin n => q.val) (hxinj _ _ y hj hk)))
    hxdummy
    (by simpa only [← hdcol] using hxmono (Fin.castLE hn 0) (Fin.castLE hn 1) (by change (0 : ℕ) ≤ 1; decide))
    (by simpa only [← hdcol] using hxmono (Fin.castLE hn 1) (Fin.castLE hn 2) (by change (1 : ℕ) ≤ 2; decide))
    (by simpa only [← hdcol] using hxtop)
  let w : Finset V → ℝ := fun Y => ∑ y ∈ Y, ∑ i : Fin 3, ∑ k : Fin 3,
    if i < k then a i y * a k y else 0
  have hpairsum (y : V) :
      (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ H.edge f), ∏ z ∈ p,
        (((Finset.univ : Finset E).filter
          (fun e => z ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)) =
      ∑ i : Fin 3, ∑ k : Fin 3, if i < k then a i y * a k y else 0 := by
    let emb : Fin 3 ↪ V := ⟨v, hvinj⟩
    have hm : Finset.univ.map emb = H.edge f := by
      ext z
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact ⟨fun ⟨i, hi⟩ => hi ▸ hv i, hcover z⟩
    have hfilt :
        Finset.univ.filter (fun p : Finset V => p.card = 2 ∧ p ⊆ H.edge f) = (H.edge f).powersetCard 2 := by
      ext p
      simp [Finset.mem_powersetCard, and_comm]
    rw [hfilt, ← hm, Finset.powersetCard_map, Finset.sum_map]
    simp only [Finset.mapEmbedding_apply, RelEmbedding.coe_toEmbedding, Finset.prod_map]
    change (∑ p ∈ Finset.univ.powersetCard 2, ∏ i ∈ p, a i y) = _
    have hfilt3 : Finset.univ.filter (fun p : Finset (Fin 3) => p.card = 2 ∧ p ⊆ Finset.univ) =
        (Finset.univ : Finset (Fin 3)).powersetCard 2 := by
      ext p
      simp [Finset.mem_powersetCard]
    rw [← hfilt3]
    simpa [Finset.sum_filter] using
      FiniteUnorderedPairProductSum (Finset.univ : Finset (Fin 3)) (fun i => a i y)
  let P : ℝ := @IndependentPairCount E _ _ (LineGraphOfHypergraph H)
    (Classical.decRel (LineGraphOfHypergraph H).Adj) f
  have hpair : 3 * (D : ℝ)^2 - 6 * D + 3 - w X ≤ P := by
    have hp := SaturatedLineGraphPairBound D H f hH.1 hH.2.2 hN
    have hpR := (Int.cast_le (R := ℝ)).mpr hp
    push_cast at hpR
    simpa only [hpairsum] using hpR
  have hsmall := (ThreeUniformTwoSimpleSmallPairsBound D _ P rfl H hH f v hv hcover
    hN X Xs Xb a w hX hone hcol hrow ha0 rfl rfl (fun _ _ => rfl) hpair).2
  let Q := ∑ j : Fin n, ∑ i : Fin 3, ∑ k : Fin 3,
    if i < k then A i j * A k j else 0
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => A i (Fin.castLE hn j)
  let L := ∑ i : Fin 3, ∑ j : Fin 3, M i j
  have hdA (i j) : d i j = B * A i j := by
    dsimp [A]
    field_simp
  have hQ : w Xb = B ^ 2 * Q := by
    rw [show w Xb = ∑ y ∈ Xb, ∑ i : Fin 3, ∑ k : Fin 3,
      if i < k then a i y * a k y else 0 from rfl, ← hxsum]
    have hs (j : Fin n) :
        (x j).elim 0 (fun y => ∑ i : Fin 3, ∑ k : Fin 3,
          if i < k then a i y * a k y else 0) =
        ∑ i : Fin 3, ∑ k : Fin 3, if i < k then d i j * d k j else 0 := by
      cases hx : x j <;> simp [d, hx]
    simp_rw [hs, hdA]
    dsimp [Q]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  have hperm : (∑ p : Equiv.Perm (Fin 3),
      d 0 (Fin.castLE hn (p 0)) * d 1 (Fin.castLE hn (p 1)) *
        d 2 (Fin.castLE hn (p 2))) = B ^ 3 * Matrix.permanent M := by
    have hbase : (∑ p : Equiv.Perm (Fin 3),
        M 0 (p 0) * M 1 (p 1) * M 2 (p 2)) = Matrix.permanent M := by
      rw [← Matrix.permanent_transpose M]
      simp only [Matrix.permanent, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro p _
      simp [Fin.prod_univ_succ, mul_assoc]
    rw [← hbase, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp only [hdA, M]
    ring
  have hL : (∑ i : Fin 3, ∑ j : Fin 3, d i (Fin.castLE hn j)) = B * L := by
    simp only [hdA, L, M, Finset.mul_sum]
  change (@IndependentTripleCount E _ _ (LineGraphOfHypergraph H)
    (Classical.decRel (LineGraphOfHypergraph H).Adj) f : ℝ) ≤
    (∑ p : Equiv.Perm (Fin 3), d 0 (Fin.castLE hn (p 0)) *
      d 1 (Fin.castLE hn (p 1)) * d 2 (Fin.castLE hn (p 2))) +
    (3 * (D : ℝ) ^ 3 + 6 * (D : ℝ) ^ 2) -
    (D : ℝ) ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3, d i (Fin.castLE hn j)) at htriple
  rw [hperm, hL] at htriple
  rw [hQ] at hsmall
  refine ⟨n, hn, A, ⟨v, x, hvinj, ?_, hxinj, ?_, ?_⟩, ?_, hAcol, ?_, hAsum, ?_⟩
  · intro y
    exact ⟨hcover y, fun ⟨i, hi⟩ => hi ▸ hv i⟩
  · intro y
    exact (hxcover y).trans (hbigmem y)
  · intro i j
    cases hx : x j <;> simp [A, d, hx, a, B]
  · intro i j
    have h0 : 0 ≤ A i j := div_nonneg (hd0 i j) hB.le
    refine ⟨h0, le_trans ?_ (hAcol j)⟩
    exact Finset.single_le_sum (fun k _ => div_nonneg (hd0 k j) hB.le) (Finset.mem_univ i)
  · intro j k hjk
    simp only [A, ← Finset.sum_div, hdcol]
    exact div_le_div_of_nonneg_right (hxmono j k hjk) hB.le
  · have hneighbor : (LineGraphOfHypergraph H).neighborFinset f =
        Finset.univ.filter (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty) := by
      ext e
      simp only [SimpleGraph.mem_neighborFinset, LineGraphOfHypergraph,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.inter_comm]
      exact and_congr ne_comm Iff.rfl
    have hdegree : (LineGraphOfHypergraph H).degree f ≤ 3 * D := by
      rw [SimpleGraph.degree, hneighbor, hN]
      omega
    have hdegreeR : ((LineGraphOfHypergraph H).degree f : ℝ) / (3 * D) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast hdegree
    have hbound : @LocalBParameter E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) f ≤
        1 - (3 * (D : ℝ)^2 - 6 * D + 3 - B^2 * Q - 2 * (D : ℝ)^((5 : ℝ)/3)) /
          (3 * D)^2 +
        (B^3 * Matrix.permanent M + (3 * (D : ℝ)^3 + 6 * (D : ℝ)^2) -
          (D : ℝ)^2 * (B * L)) / (3 * D)^3 := by
      unfold LocalBParameter
      push_cast
      exact add_le_add
        (sub_le_sub hdegreeR (div_le_div_of_nonneg_right hsmall (by positivity)))
        (div_le_div_of_nonneg_right htriple (by positivity))
    have hBnorm : B = (D : ℝ) * (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) := by
      dsimp [B]
      rw [show (2 : ℝ) / 3 = 1 + -1 / 3 by norm_num,
        Real.rpow_add hDreal, Real.rpow_one]
      ring
    have hpow5 : (D : ℝ) ^ ((5 : ℝ) / 3) =
        (D : ℝ)^2 * (D : ℝ) ^ (-(1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hDreal]
      norm_num
    have halgebra :
        1 - (3 * (D : ℝ)^2 - 6 * D + 3 - B^2 * Q - 2 * (D : ℝ)^((5 : ℝ)/3)) /
          (3 * D)^2 +
        (B^3 * Matrix.permanent M + (3 * (D : ℝ)^3 + 6 * (D : ℝ)^2) -
          (D : ℝ)^2 * (B * L)) / (3 * D)^3 =
        1 - (2 : ℝ) / 9 + (2 : ℝ) / 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) +
          8 / (9 * (D : ℝ)) +
          (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 / 9 * Q +
          (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 / 27 * Matrix.permanent M -
          (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) / 27 * L - 1 / (3 * (D : ℝ)^2) := by
      rw [hBnorm, hpow5]
      field_simp
      <;> ring
    rw [halgebra] at hbound
    exact hbound.trans (sub_le_self _ (by positivity))
