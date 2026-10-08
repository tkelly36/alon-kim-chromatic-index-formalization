import Tablet.Preamble
import Tablet.ExtremalBParameterSaturation
import Tablet.SaturatedEdgeStructure

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleDegreeToBigBound]
theorem ThreeUniformTwoSimpleDegreeToBigBound :
    ∀ D : ℕ,
      ∀ {V E : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
          ∀ f : E, ∀ v : Fin 3 → V,
            (∀ i : Fin 3, v i ∈ H.edge f) →
            (∀ y : V, y ∈ H.edge f → ∃ i : Fin 3, v i = y) →
            (∀ i : Fin 3, HypergraphDegree H (v i) = D) →
            (((Finset.univ : Finset E).filter
                (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)).card =
              3 * (D - 1)) →
            ∀ X Xs Xb : Finset V, ∀ a : Fin 3 → V → ℝ,
              (∀ x : V, x ∈ X ↔
                x ∉ H.edge f ∧ ∃ e : E, e ≠ f ∧ x ∈ H.edge e ∧
                  (H.edge e ∩ H.edge f).Nonempty) →
              (∀ i x, a i x =
                (((Finset.univ : Finset E).filter
                  (fun e => v i ∈ H.edge e ∧ x ∈ H.edge e)).card : ℝ)) →
              (∀ e : E, e ≠ f → (H.edge e ∩ H.edge f).Nonempty →
                (H.edge e ∩ H.edge f).card = 1) →
              (∀ x ∈ X, (∑ i : Fin 3, a i x) ≤ (D : ℝ)) →
              (∀ i : Fin 3, (∑ x ∈ X, a i x) = 2 * ((D : ℝ) - 1)) →
              Xs = X.filter (fun x =>
                (∑ i : Fin 3, a i x) < (D : ℝ) ^ ((2 : ℝ) / 3)) →
              Xb = X \ Xs →
              ∀ i : Fin 3, (∑ x ∈ Xb, a i x) ≤
                (D : ℝ) + 18 * (D : ℝ) ^ ((2 : ℝ) / 3) := by
-- BODY
  classical
  intro D V E _ _ _ _ H hH f v hv hcover hdeg hneighbor X Xs Xb a hX ha
    hone hcol hrow hXs hXb
  have ha0 (i : Fin 3) (x : V) : 0 ≤ a i x := by
    rw [ha]
    positivity
  have hD : (1 : ℝ) ≤ D := by
    have := Finset.sum_nonneg (fun x (_ : x ∈ X) => ha0 0 x)
    rw [hrow] at this
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hbX : Xb ⊆ X := by rw [hXb]; exact Finset.sdiff_subset
  have hbnot (x : V) (hx : x ∈ Xb) : x ∉ H.edge f := (hX x).mp (hbX hx) |>.1
  have hthreshold (x : V) (hx : x ∈ Xb) :
      (D : ℝ) ^ ((2 : ℝ) / 3) ≤ ∑ i : Fin 3, a i x := by
    have hn := (Finset.mem_sdiff.mp (hXb ▸ hx)).2
    rw [hXs, Finset.mem_filter] at hn
    exact le_of_not_gt (fun h => hn ⟨hbX hx, h⟩)
  have htotal : (∑ x ∈ X, ∑ i : Fin 3, a i x) = 6 * ((D : ℝ) - 1) := by
    rw [Finset.sum_comm]
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hmass : (Xb.card : ℝ) * (D : ℝ) ^ ((2 : ℝ) / 3) ≤
      6 * ((D : ℝ) - 1) := by
    calc
      _ = ∑ x ∈ Xb, (D : ℝ) ^ ((2 : ℝ) / 3) := by simp
      _ ≤ ∑ x ∈ Xb, ∑ i : Fin 3, a i x := Finset.sum_le_sum hthreshold
      _ ≤ ∑ x ∈ X, ∑ i : Fin 3, a i x :=
        Finset.sum_le_sum_of_subset_of_nonneg hbX
          (fun x _ _ => Finset.sum_nonneg (fun i _ => ha0 i x))
      _ = _ := htotal
  have hpow : (D : ℝ) ^ ((1 : ℝ) / 3) * (D : ℝ) ^ ((2 : ℝ) / 3) = D := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hbcard : (Xb.card : ℝ) ≤ 6 * (D : ℝ) ^ ((1 : ℝ) / 3) := by
    nlinarith [Real.rpow_pos_of_pos hDpos ((2 : ℝ) / 3)]
  intro i
  let S := Finset.univ.filter (fun e : E => e ≠ f ∧ v i ∈ H.edge e)
  let T := S.filter (fun e => (H.edge e ∩ Xb).card = 2)
  have hSmem (e : E) : e ∈ S ↔ e ≠ f ∧ v i ∈ H.edge e := by simp [S]
  have hScard : S.card = D - 1 := by
    have heq : S = (Finset.univ.filter (fun e : E => v i ∈ H.edge e)).erase f := by
      ext e
      simp [S]
    rw [heq, Finset.card_erase_of_mem (by simp [hv i])]
    exact congrArg (fun n : ℕ => n - 1) (hdeg i)
  have hnotbig : v i ∉ Xb := fun h => hbnot _ h (hv i)
  have hcaple (e : E) (he : e ∈ S) : (H.edge e ∩ Xb).card ≤ 2 := by
    have hsub : insert (v i) (H.edge e ∩ Xb) ⊆ H.edge e := by
      simp only [Finset.insert_subset_iff]
      exact ⟨(hSmem e).mp he |>.2, Finset.inter_subset_left⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hnotbig]), hH.1 e] at hc
    omega
  have hrecover (e : E) (he : e ∈ T) :
      H.edge e = insert (v i) (H.edge e ∩ Xb) := by
    have heS := (Finset.mem_filter.mp he).1
    apply (Finset.eq_of_subset_of_card_le
      (show insert (v i) (H.edge e ∩ Xb) ⊆ H.edge e from
        Finset.insert_subset_iff.mpr ⟨(hSmem e).mp heS |>.2,
          Finset.inter_subset_left⟩) ?_).symm
    rw [Finset.card_insert_of_notMem (by simp [hnotbig]),
      (Finset.mem_filter.mp he).2, hH.1 e]
  have hTcard : T.card ≤ Xb.card.choose 2 := by
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card_of_injOn (fun e => H.edge e ∩ Xb)
    · intro e he
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_right, (Finset.mem_filter.mp he).2⟩
    · intro e he g hg heq
      change H.edge e ∩ Xb = H.edge g ∩ Xb at heq
      by_contra hne
      have hedge : H.edge e = H.edge g := by rw [hrecover e he, hrecover g hg, heq]
      have hc := hH.2.1 hne
      rw [hedge, Finset.inter_self, hH.1 g] at hc
      omega
  have hinc : (∑ x ∈ Xb, a i x) =
      ((∑ e ∈ S, (H.edge e ∩ Xb).card : ℕ) : ℝ) := by
    have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun x e => x ∈ H.edge e) (s := Xb) (t := S)
    have hleft (x : V) (hx : x ∈ Xb) :
        S.bipartiteAbove (fun x e => x ∈ H.edge e) x =
          Finset.univ.filter (fun e => v i ∈ H.edge e ∧ x ∈ H.edge e) := by
      ext e
      simp only [Finset.bipartiteAbove, Finset.mem_filter, hSmem, Finset.mem_univ,
        true_and]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · intro h
        exact ⟨⟨fun hef => hbnot x hx (hef ▸ h.2), h.1⟩, h.2⟩
    have hright (e : E) : Xb.bipartiteBelow (fun x e => x ∈ H.edge e) e =
        H.edge e ∩ Xb := by ext x; simp [Finset.bipartiteBelow, and_comm]
    simp_rw [hright] at hdouble
    rw [← hdouble, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hleft x hx, ha]
  have hincle : (∑ e ∈ S, (H.edge e ∩ Xb).card) ≤ S.card + T.card := by
    calc
      _ ≤ ∑ e ∈ S, (1 + if (H.edge e ∩ Xb).card = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro e he
        have := hcaple e he
        split_ifs <;> omega
      _ = S.card + T.card := by simp [Finset.sum_add_distrib, T]
  have hchoose : (Xb.card.choose 2 : ℝ) ≤ (Xb.card : ℝ) ^ 2 / 2 := by
    have hn := Nat.div_mul_le_self (Xb.card * (Xb.card - 1)) 2
    have hm : Xb.card * (Xb.card - 1) ≤ Xb.card * Xb.card :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [Nat.choose_two_right]
    have hc : ((Xb.card * (Xb.card - 1) / 2 : ℕ) : ℝ) * 2 ≤
        (Xb.card : ℝ) * Xb.card := by exact_mod_cast hn.trans hm
    nlinarith
  have hpow2 : ((D : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (D : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hDpos)]
    congr 1
    norm_num
  have hchoosebound : (Xb.card.choose 2 : ℝ) ≤ 18 * (D : ℝ) ^ ((2 : ℝ) / 3) := by
    have hsquare := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ Xb.card)
      (by positivity : 0 ≤ 6 * (D : ℝ) ^ ((1 : ℝ) / 3)) |>.2 hbcard
    nlinarith [hchoose, hpow2]
  rw [hinc]
  have hnat := hincle.trans (Nat.add_le_add_left hTcard S.card)
  rw [hScard] at hnat
  have hcast : ((∑ e ∈ S, (H.edge e ∩ Xb).card : ℕ) : ℝ) ≤
      ((D - 1 : ℕ) : ℝ) + (Xb.card.choose 2 : ℝ) := by exact_mod_cast hnat
  have hsub : ((D - 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.sub_le D 1
  linarith
