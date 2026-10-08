import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.KUniformNeighborOneIntersectionFromSaturation
import Tablet.TriangleCountPartite
import Tablet.NeighborhoodComplementTriangleCountEqualsIndependentTripleCount
import Tablet.NeighborhoodComplementEdgeCountLeIndependentPairCount

-- [TABLET NODE: ThreeUniformThreeSimpleNeighborhoodComplementBounds]
theorem ThreeUniformThreeSimpleNeighborhoodComplementBounds
    {D : ℕ} {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E)
    (S : ThreeUniformThreeSimpleLocalSetup D F f) :
    0 ≤ S.P ∧ S.P ≤ (9 / 2 : ℝ) * (D : ℝ) ^ 2 ∧
    0 ≤ S.T ∧ S.T ^ 2 ≤ S.P ^ 3 / 27 ∧
    S.b = 3 * ((D : ℝ) - 1) / (3 * (D : ℝ)) -
      S.P / (3 * (D : ℝ)) ^ 2 + S.T / (3 * (D : ℝ)) ^ 3 := by
-- BODY
  classical
  let G := LineGraphOfHypergraph F
  letI : DecidableRel G.Adj := Classical.decRel _
  let N := G.neighborFinset f
  have hN : N = (Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty) := by
    ext g
    simp only [N, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact G.adj_comm f g
  have hcard : N.card = 3 * (D - 1) := hN ▸ S.saturated_neighbors
  have hD : 1 ≤ D := le_trans (by norm_num) S.D_large
  have hcardR : (N.card : ℝ) = 3 * ((D : ℝ) - 1) := by
    rw [hcard]
    push_cast [Nat.cast_sub hD]
    ring
  have hP : S.P = (IndependentPairCount G f : ℝ) := S.P_is_independent_pair_count
  have hT : S.T = (IndependentTripleCount G f : ℝ) := S.T_is_independent_triple_count
  have hP0 : 0 ≤ S.P := by rw [hP]; positivity
  have hT0 : 0 ≤ S.T := by rw [hT]; positivity
  have hpairs : IndependentPairCount G f ≤ N.card.choose 2 := by
    unfold IndependentPairCount
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.mem_powersetCard.mpr ⟨hs.2.1, hs.1⟩
  have hpairNat : 2 * IndependentPairCount G f ≤ N.card * N.card := by
    have hh := Nat.mul_le_mul_left 2 hpairs
    rw [Nat.choose_two_right] at hh
    have hd := Nat.div_mul_le_self (N.card * (N.card - 1)) 2
    have hm := Nat.mul_le_mul_left N.card (Nat.sub_le N.card 1)
    omega
  have hpairReal : 2 * S.P ≤ (N.card : ℝ) ^ 2 := by
    rw [hP, pow_two]
    exact_mod_cast hpairNat
  have hPbound : S.P ≤ (9 / 2 : ℝ) * (D : ℝ) ^ 2 := by
    rw [hcardR] at hpairReal
    have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  let C : SimpleGraph {g : E // g ∈ N} :=
    { Adj := fun x y => x ≠ y ∧ ¬ G.Adj x.1 y.1
      symm := by intro x y h; exact ⟨h.1.symm, fun h' => h.2 h'.symm⟩
      loopless := ⟨by intro x h; exact h.1 rfl⟩ }
  letI : DecidableRel C.Adj := Classical.decRel _
  have hC (x y : {g : E // g ∈ N}) :
      C.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x.1 y.1 := Iff.rfl
  have hmeet (g : {g : E // g ∈ N}) : (F.edge g.1 ∩ F.edge f).Nonempty := by
    have hg : G.Adj f g.1 := by simpa only [N, SimpleGraph.mem_neighborFinset] using g.2
    exact hg.symm.2
  let vertex (g : {g : E // g ∈ N}) : {v : V // v ∈ F.edge f} :=
    ⟨(hmeet g).choose, (Finset.mem_inter.mp (hmeet g).choose_spec).2⟩
  have hvertex (g : {g : E // g ∈ N}) : (vertex g).1 ∈ F.edge g.1 :=
    (Finset.mem_inter.mp (hmeet g).choose_spec).1
  have hthree : Fintype.card {v : V // v ∈ F.edge f} = 3 := by
    rw [Fintype.card_coe]
    exact S.class_mem.1 f
  let label := Fintype.equivFinOfCardEq hthree
  have hpart : ∃ part : {g : E // g ∈ N} → Fin 3,
      ∀ ⦃x y⦄, C.Adj x y → part x ≠ part y := by
    refine ⟨fun g => label (vertex g), ?_⟩
    intro x y hxy heq
    have hv := congrArg Subtype.val (label.injective heq)
    apply hxy.2
    refine ⟨?_, ?_⟩
    · intro he; exact hxy.1 (Subtype.ext he)
    · exact ⟨(vertex x).1, Finset.mem_inter.mpr
        ⟨hvertex x, hv.symm ▸ hvertex y⟩⟩
  have ht := TriangleCountPartite C hpart
  have he := NeighborhoodComplementEdgeCountLeIndependentPairCount G f C hC
  have htr := NeighborhoodComplementTriangleCountEqualsIndependentTripleCount G f C hC
  have hbound : S.T ≤ (S.P / 3) ^ ((3 : ℝ) / 2) := by
    rw [hT, htr]
    refine ht.trans ?_
    apply Real.rpow_le_rpow
      (div_nonneg (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)) _
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
    rw [hP]
    exact_mod_cast he
  have hsquare : ((S.P / 3) ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = S.P ^ 3 / 27 := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ S.P / 3)]
    norm_num
    ring
  have hTsquare : S.T ^ 2 ≤ S.P ^ 3 / 27 := by
    rw [← hsquare]
    exact pow_le_pow_left₀ hT0 hbound 2
  refine ⟨hP0, hPbound, hT0, hTsquare, ?_⟩
  rw [S.b_eq]
  change (G.degree f : ℝ) / (↑(3 * D) : ℝ) -
    (IndependentPairCount G f : ℝ) / (↑(3 * D) : ℝ) ^ 2 +
    (IndependentTripleCount G f : ℝ) / (↑(3 * D) : ℝ) ^ 3 = _
  rw [← hP, ← hT, ← SimpleGraph.card_neighborFinset_eq_degree]
  change (N.card : ℝ) / _ - _ + _ = _
  rw [hcardR]
  norm_num
