import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformSaturatedEdgeStructure
import Tablet.SaturatedLineGraphEdgeCount
import Tablet.FiniteNonnegativeWeightCutoff
import Tablet.FiniteHypergraphClassRelabeling

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleSetupConstruction]
theorem ThreeUniformThreeSimpleSetupConstruction
    (D : ℕ) (hD : 100 ≤ D)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E)
    (hF : F ∈ HypergraphClass (V := V) (E := E) 3 3 D)
    (hmax : ∀ {V' E' : Type} [Fintype E'] [DecidableEq E'] [DecidableEq V'],
      ∀ H : MultiHypergraph V' E',
        H ∈ HypergraphClass (V := V') (E := E') 3 3 D → ∀ e : E',
          @LocalBParameter E' _ _ (LineGraphOfHypergraph H)
            (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e ≤
          @LocalBParameter E _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) (3 * D) f)
    (hv : ∀ v ∈ F.edge f, HypergraphDegree F v = D)
    (hn : ((Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)).card = 3 * (D - 1)) :
    Nonempty (ThreeUniformThreeSimpleLocalSetup D F f) := by
-- BODY
  classical
  let X := (Finset.univ : Finset V).filter (fun x => x ∉ F.edge f ∧
    ∃ g : E, g ≠ f ∧ x ∈ F.edge g ∧ (F.edge g ∩ F.edge f).Nonempty)
  let a := fun v x : V => (((Finset.univ : Finset E).filter
    (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let c := fun x : V => ∑ v ∈ F.edge f, a v x
  let r := fun v : V => ∑ x ∈ X, a v x
  have ha (v x : V) : 0 ≤ a v x := Nat.cast_nonneg _
  have hc (x : V) : 0 ≤ c x := Finset.sum_nonneg (fun v _ => ha v x)
  obtain ⟨Xs, hXs, hcut, hmaxcut, horder⟩ :=
    FiniteNonnegativeWeightCutoff X c (fun x _ => hc x)
      ((D : ℝ) / 2) (by positivity)
  let Xb := X \ Xs
  have hXpart : Xs ∪ Xb = X := Finset.union_sdiff_of_subset hXs
  have hXdis : Disjoint Xs Xb := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have htotalSplit : (∑ x ∈ X, c x) = (∑ x ∈ Xs, c x) + ∑ x ∈ Xb, c x := by
    rw [← hXpart, Finset.sum_union hXdis]
  obtain ⟨hone, hcol, hrow⟩ :=
    ThreeUniformSaturatedEdgeStructure D F hF.1 hF.2.2 f hn
  have hXeq : X = (Finset.univ : Finset V).filter (fun x => x ∉ F.edge f ∧
      ((Finset.univ : Finset E).filter
        (fun g => (F.edge g ∩ F.edge f).Nonempty ∧ x ∈ F.edge g)).Nonempty) := by
    ext x
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, Finset.Nonempty]
    constructor
    · rintro ⟨hx, g, hgf, hxg, hg⟩
      exact ⟨hx, g, hg, hxg⟩
    · rintro ⟨hx, g, hg, hxg⟩
      exact ⟨hx, g, fun he => hx (he ▸ hxg), hxg, hg⟩
  have hcolumn (x : V) (hx : x ∈ X) : c x ≤ (D : ℝ) := by
    have h := hcol x (Finset.mem_filter.mp hx).2.1
    dsimp [c, a]
    exact_mod_cast h
  have hrows (v : V) (hvf : v ∈ F.edge f) : r v = 2 * ((D : ℝ) - 1) := by
    have h := hrow v hvf
    rw [← hXeq] at h
    have hfilter (x : V) (hx : x ∈ X) :
        ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ F.edge g ∧ x ∈ F.edge g)) =
        ((Finset.univ : Finset E).filter (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun he =>
        (Finset.mem_filter.mp hx).2.1 (he ▸ h.2), h⟩⟩
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hcast
    simp_rw [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] at hcast
    change (∑ x ∈ X, a v x) = _
    rw [← hcast]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hfilter x hx]
  have htotal : (∑ x ∈ X, c x) = 6 * ((D : ℝ) - 1) := by
    change (∑ x ∈ X, ∑ v ∈ F.edge f, a v x) = _
    rw [Finset.sum_comm]
    calc
      _ = ∑ v ∈ F.edge f, 2 * ((D : ℝ) - 1) := Finset.sum_congr rfl hrows
      _ = _ := by simp [hF.1 f]; ring
  let N := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  let V1 := N.filter (fun g => (F.edge g ∩ Xs).Nonempty)
  let V2 := N \ V1
  have hV1 : V1 ⊆ N := Finset.filter_subset _ _
  have hVpart : V1 ∪ V2 = N := Finset.union_sdiff_of_subset hV1
  have hVdis : Disjoint V1 V2 := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
  have hshape (g : E) (hg : g ∈ V2) :
      (F.edge g ∩ F.edge f).card = 1 ∧ (F.edge g ∩ Xb).card = 2 := by
    obtain ⟨hgN, hgV⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hgf, hmeet⟩ := (Finset.mem_filter.mp hgN).2
    have hcard : (F.edge g ∩ F.edge f).card = 1 :=
      Nat.le_antisymm (hone g hgf) (Finset.card_pos.mpr hmeet)
    have havoid : ¬ (F.edge g ∩ Xs).Nonempty := by
      intro h
      exact hgV (Finset.mem_filter.mpr ⟨hgN, h⟩)
    have heq : F.edge g ∩ Xb = F.edge g \ F.edge f := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, Xb]
      constructor
      · exact fun h => ⟨h.1, (Finset.mem_filter.mp h.2.1).2.1⟩
      · intro h
        refine ⟨h.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2,
          g, hgf, h.1, hmeet⟩, ?_⟩
        exact fun hx => havoid ⟨x, Finset.mem_inter.mpr ⟨h.1, hx⟩⟩
    refine ⟨hcard, ?_⟩
    rw [heq, Finset.card_sdiff, Finset.inter_comm, hcard, hF.1 g]
  let weight := fun x : V => ∑ p ∈ ((Finset.univ : Finset (Finset V)).filter
    (fun p => p.card = 2 ∧ p ⊆ F.edge f)), ∏ v ∈ p, a v x
  have hWsplit : (∑ x ∈ X, weight x) =
      (∑ x ∈ Xs, weight x) + ∑ x ∈ Xb, weight x := by
    rw [← hXpart, Finset.sum_union hXdis]
  let triples := (Finset.univ : Finset (Finset E)).filter (fun S =>
    S.card = 3 ∧ S ⊆ N ∧ ∀ ⦃g⦄, g ∈ S → ∀ ⦃h⦄, h ∈ S → g ≠ h →
      ¬ (g ≠ h ∧ (F.edge g ∩ F.edge h).Nonempty))
  let triples1 := triples.filter (fun S => ∃ g ∈ S, g ∈ V1)
  let triples2 := triples.filter (fun S => S ⊆ V2)
  have htriplepart : triples1 ∪ triples2 = triples := by
    ext S
    simp only [triples1, triples2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hS
      by_cases h : ∃ g ∈ S, g ∈ V1
      · exact Or.inl ⟨hS, h⟩
      · refine Or.inr ⟨hS, fun g hg => ?_⟩
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hS).2.2.1 hg,
          fun hgV => h ⟨g, hg, hgV⟩⟩
  have htripledis : Disjoint triples1 triples2 := by
    apply Finset.disjoint_left.mpr
    intro S h1 h2
    obtain ⟨g, hg, hgV⟩ := (Finset.mem_filter.mp h1).2
    exact (Finset.mem_sdiff.mp ((Finset.mem_filter.mp h2).2 hg)).2 hgV
  have hneighbor : (LineGraphOfHypergraph F).neighborFinset f = N := by
    ext g
    simp only [SimpleGraph.mem_neighborFinset, LineGraphOfHypergraph, N,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ne_comm, Finset.inter_comm]
  have htriplecount : @IndependentTripleCount E _ _ (LineGraphOfHypergraph F)
      (Classical.decRel (LineGraphOfHypergraph F).Adj) f = triples.card := by
    as_aux_lemma =>
    unfold IndependentTripleCount
    rw [hneighbor]
    apply congrArg Finset.card
    ext S
    simp only [triples, Finset.mem_filter, Finset.mem_univ, true_and,
      LineGraphOfHypergraph]
  have hTsplit : (triples.card : ℝ) = (triples1.card : ℝ) + triples2.card := by
    rw [← htriplepart, Finset.card_union_of_disjoint htripledis, Nat.cast_add]
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  letI : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
  let Y : ℤ := ∑ v ∈ F.edge f, ∑ v' ∈ (F.edge f).filter (fun u => v < u),
    ∑ e1 ∈ ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ F.edge g)),
    ∑ e2 ∈ ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v' ∈ F.edge g)),
      max (0 : ℤ) (((F.edge e1 ∩ F.edge e2).card : ℤ) - 1)
  have hcounts := SaturatedLineGraphEdgeCount D F f hF.1 hF.2.2 hn
  have hY : 0 ≤ Y := hcounts.1
  refine ⟨{
    D_large := hD
    class_mem := hF
    b := _
    b_eq := rfl
    maximizes_b := by
      intro V' E' _ _ _ H hH e
      obtain ⟨V'', E'', iV, iE, dE, dV, H', e', hH', heq⟩ :=
        FiniteHypergraphClassRelabeling.{_, _, 0, 0}
          3 3 D (3 * D) H hH e (by omega) (le_refl _)
      letI := iV
      letI := iE
      letI := dE
      letI := dV
      rw [heq]
      exact hmax H' hH' e'
    saturated_neighbors := hn
    saturated_vertex_degrees := hv
    X := X
    Xs := Xs
    Xb := Xb
    X_eq := rfl
    X_partition := hXpart
    Xs_disjoint_Xb := hXdis
    Xb_eq := rfl
    V1 := V1
    V2 := V2
    V1_eq := rfl
    V2_eq := rfl
    V_partition := hVpart
    V1_disjoint_V2 := hVdis
    P := _
    T := _
    W := ∑ x ∈ X, weight x
    WXs := ∑ x ∈ Xs, weight x
    WXb := ∑ x ∈ Xb, weight x
    Y := (Y : ℝ)
    T1 := (triples1.card : ℝ)
    T2 := (triples2.card : ℝ)
    totalX := ∑ x ∈ X, c x
    totalXs := ∑ x ∈ Xs, c x
    totalXb := ∑ x ∈ Xb, c x
    vertexDegreeIntoF := c
    rowDegreeOverX := r
    crossDegree := fun g => ∑ x ∈ F.edge g \ F.edge f,
      ∑ v ∈ F.edge f \ F.edge g, a v x
    vertexDegreeIntoF_eq := fun _ => rfl
    rowDegreeOverX_eq := fun _ => rfl
    crossDegree_eq := fun _ => rfl
    P_is_independent_pair_count := rfl
    T_is_independent_triple_count := rfl
    pair_identity := ?_
    Y_nonnegative := by exact_mod_cast hY
    W_split := hWsplit
    T_split := by rw [htriplecount]; exact hTsplit
    T1_is_triangle_count_meeting_V1 := ?_
    T2_is_triangle_count_inside_V2 := ?_
    totalX_eq_sum := rfl
    totalXs_eq_sum := rfl
    totalXb_eq_sum := rfl
    totalX_value := htotal
    Xs_total_cutoff := hcut
    Xs_maximal_under_cutoff := hmaxcut
    Xb_total_eq := by linarith [htotalSplit]
    column_bound := hcolumn
    row_sum := hrows
    Xs_low_degree_maximal := horder
    V2_edge_shape := hshape
    WXs_is_weight_of_Xs := rfl
    WXb_is_weight_of_Xb := rfl
    T1_nonnegative := Nat.cast_nonneg _
    T2_nonnegative := Nat.cast_nonneg _ }⟩
  · as_aux_lemma =>
    let pairs := N.powersetCard 2
    let adjacent := fun s : Finset E =>
      ∀ g ∈ s, ∀ h ∈ s, g ≠ h → (F.edge g ∩ F.edge h).Nonempty
    have hcompl (s : Finset E) (hs : s.card = 2) :
        (¬ adjacent s) ↔
          (∀ ⦃g⦄, g ∈ s → ∀ ⦃h⦄, h ∈ s → g ≠ h →
            ¬ (LineGraphOfHypergraph F).Adj g h) := by
      obtain ⟨g, h, hgh, rfl⟩ := Finset.card_eq_two.mp hs
      have heq : adjacent {g,h} ↔ (F.edge g ∩ F.edge h).Nonempty := by
        constructor
        · exact fun h => h g (by simp) _ (by simp) hgh
        · intro hmeet u hu v hv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact (huv rfl).elim
          · exact hmeet
          · simpa only [Finset.inter_comm] using hmeet
          · exact (huv rfl).elim
      rw [heq]
      constructor
      · intro hnot u hu v hv huv hadj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact huv rfl
        · exact hnot hadj.2
        · exact hnot (by simpa only [Finset.inter_comm] using hadj.2)
        · exact huv rfl
      · intro hnot hmeet
        exact hnot (by simp) (by simp) hgh ⟨hgh, hmeet⟩
    have hA : pairs.filter adjacent = (Finset.univ : Finset (Finset E)).filter
        (fun s => s.card = 2 ∧ s ⊆ N ∧ adjacent s) := by
      ext s
      simp only [pairs, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ, true_and]
      tauto
    have hI : (pairs.filter (fun s => ¬ adjacent s)).card =
        @IndependentPairCount E _ _ (LineGraphOfHypergraph F)
          (Classical.decRel (LineGraphOfHypergraph F).Adj) f := by
      unfold IndependentPairCount
      apply congrArg Finset.card
      ext s
      simp only [pairs, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ,
        true_and, hneighbor]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hn⟩
        exact ⟨hcard, hsub, (hcompl s hcard).mp hn⟩
      · rintro ⟨hcard, hsub, hi⟩
        exact ⟨⟨hsub, hcard⟩, (hcompl s hcard).mpr hi⟩
    have hcount := Finset.card_filter_add_card_filter_not (s := pairs) adjacent
    rw [hA, hI, show pairs.card = Nat.choose (3 * (D - 1)) 2 by
      change (N.powersetCard 2).card = _
      rw [Finset.card_powersetCard]
      exact congrArg (fun n => Nat.choose n 2) hn] at hcount
    have hcountR := congrArg (fun n : ℕ => (n : ℝ)) hcount
    simp only [Nat.cast_add] at hcountR
    have hedge := congrArg (fun z : ℤ => (z : ℝ)) hcounts.2
    dsimp only at hedge
    push_cast at hedge
    rw [← hXeq] at hedge
    have hYcast : (Y : ℝ) =
        ∑ v ∈ F.edge f, ∑ v' ∈ (F.edge f).filter (fun u => v < u),
          ∑ e1 ∈ ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ F.edge g)),
          ∑ e2 ∈ ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v' ∈ F.edge g)),
            max (0 : ℝ) (((F.edge e1 ∩ F.edge e2).card : ℝ) - 1) := by
      dsimp only [Y]
      push_cast
      rfl
    rw [← hYcast] at hedge
    change _ = 3 * (Nat.choose (D - 1) 2 : ℝ) + (∑ x ∈ X, weight x) - (Y : ℝ) at hedge
    have hbinom : (Nat.choose (3 * (D - 1)) 2 : ℝ) -
        3 * (Nat.choose (D - 1) 2 : ℝ) = 3 * (D : ℝ)^2 - 6 * (D : ℝ) + 3 := by
      have htwo (n : ℕ) : 2 * (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
        cases n with
        | zero => norm_num
        | succ n =>
          have h := Nat.add_one_mul_choose_eq n 1
          simp only [Nat.choose_one_right] at h
          have hz := congrArg (fun n : ℕ => (n : ℝ)) h
          push_cast at hz ⊢
          nlinarith
      have h1 := htwo (3 * (D - 1))
      have h2 := htwo (D - 1)
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] at h1
      rw [Nat.cast_sub (show 1 ≤ D by omega), Nat.cast_one] at h2
      nlinarith
    dsimp only [N, adjacent] at hcountR
    linarith [hedge]
  · simp only [triples1, triples, N, Finset.filter_filter, and_assoc]
  · simp only [triples2, triples, N, Finset.filter_filter, and_assoc]
