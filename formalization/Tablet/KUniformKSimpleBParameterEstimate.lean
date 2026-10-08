import Tablet.HypergraphClass
import Tablet.IndependentPairCount
import Tablet.IndependentPairCountLeChooseNeighborCard
import Tablet.IndependentTripleCount
import Tablet.HypergraphDegree
import Tablet.KPartiteTriangleCount
import Tablet.KUniformKSimpleExtremalSaturation
import Tablet.KUniformKSimpleBParameterRealEstimate
import Tablet.KUniformKSimpleLocalPatternExtremalReduction
import Tablet.KUniformKSimplePairLowerBound
import Tablet.KUniformNeighborOneIntersectionFromSaturation
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.NeighborhoodComplementEdgeCountLeIndependentPairCount
import Tablet.NeighborhoodComplementTriangleCountEqualsIndependentTripleCount
import Tablet.SubhypergraphOf
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

set_option maxHeartbeats 800000

-- [TABLET NODE: KUniformKSimpleBParameterEstimate]
theorem KUniformKSimpleBParameterEstimate :
    ∀ eta : ℝ, 0 < eta → ∀ k : ℕ, 0 < k →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) k k D →
            ∀ e : E,
              @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                  (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e
                ≤ 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
                    (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
                      (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) + eta := by
-- BODY
  classical
  intro eta heta k hk
  obtain ⟨Dsat0, hsat⟩ := KUniformKSimpleExtremalSaturation k hk
  obtain ⟨Dpair0, hpair⟩ := KUniformKSimplePairLowerBound k hk
  refine ⟨max (2 * k ^ 2) (max 1 (max Dsat0 Dpair0)), ?_⟩
  intro D hD V E _ _ _ H hH e
  have hDlarge : 2 * k ^ 2 ≤ D := by
    exact le_trans (Nat.le_max_left (2 * k ^ 2) (max 1 (max Dsat0 Dpair0))) hD
  have hDpos : 0 < D := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (le_trans
        (le_trans (Nat.le_max_left 1 (max Dsat0 Dpair0))
          (Nat.le_max_right (2 * k ^ 2) (max 1 (max Dsat0 Dpair0)))) hD)
  obtain
    ⟨Vloc, Eloc, instFintypeEloc, instDecidableEqEloc, instDecidableEqVloc,
      F, f, hF, hb_le, hmax⟩ :=
    KUniformKSimpleLocalPatternExtremalReduction k hk D hDpos H hH e
  letI : Fintype Eloc := instFintypeEloc
  letI : DecidableEq Eloc := instDecidableEqEloc
  letI : DecidableEq Vloc := instDecidableEqVloc
  have hDsat : Dsat0 ≤ D := by
    exact le_trans (le_trans (Nat.le_max_left Dsat0 Dpair0)
      (le_trans (Nat.le_max_right 1 (max Dsat0 Dpair0))
        (Nat.le_max_right (2 * k ^ 2) (max 1 (max Dsat0 Dpair0))))) hD
  have hDpair : Dpair0 ≤ D := by
    exact le_trans (le_trans (Nat.le_max_right Dsat0 Dpair0)
      (le_trans (Nat.le_max_right 1 (max Dsat0 Dpair0))
        (Nat.le_max_right (2 * k ^ 2) (max 1 (max Dsat0 Dpair0))))) hD
  have hsaturated :
      (∀ v : Vloc, v ∈ F.edge f → HypergraphDegree F v = D) ∧
        ((Finset.univ : Finset Eloc).filter
          (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)).card = k * D - k := by
    exact hsat D hDsat F hF f hmax
  have hpair_lower :
      (((k : ℝ) - 1) / 2) * (D : ℝ) ^ 2 - (k : ℝ) ^ 2 * (D : ℝ)
        ≤ (@IndependentPairCount Eloc _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) f : ℝ) := by
    exact hpair D hDpair F hF f hmax
  by_cases hk_one : k = 1
  · subst k
    let G : SimpleGraph Eloc := LineGraphOfHypergraph F
    let N : Finset Eloc :=
      (Finset.univ : Finset Eloc).filter
        (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
    obtain ⟨a, hfa⟩ : ∃ a : Vloc, F.edge f = {a} := by
      exact Finset.card_eq_one.mp (by simpa using hF.1 f)
    have hneighbor_eq : G.neighborFinset f = N := by
      ext g
      simp only [G, N, LineGraphOfHypergraph, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hfg, hnon⟩
        exact ⟨hfg.symm, by simpa [Finset.inter_comm] using hnon⟩
      · rintro ⟨hgf, hnon⟩
        exact ⟨hgf.symm, by simpa [Finset.inter_comm] using hnon⟩
    have hdegree : G.degree f = D - 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbor_eq]
      simpa [N] using hsaturated.2
    have hneighbor_contains_a : ∀ g : Eloc, g ∈ G.neighborFinset f → a ∈ F.edge g := by
      intro g hg
      have hfg : G.Adj f g := by
        simpa [SimpleGraph.mem_neighborFinset] using hg
      rcases hfg.2 with ⟨x, hx⟩
      have hxf : x ∈ F.edge f := (Finset.mem_inter.mp hx).1
      have hxg : x ∈ F.edge g := (Finset.mem_inter.mp hx).2
      have hxa : x = a := by
        simpa [hfa] using hxf
      simpa [hxa] using hxg
    have hneighbor_clique :
        ∀ ⦃x⦄, x ∈ G.neighborFinset f → ∀ ⦃y⦄, y ∈ G.neighborFinset f →
          x ≠ y → G.Adj x y := by
      intro x hx y hy hxy
      have hax : a ∈ F.edge x := hneighbor_contains_a x hx
      have hay : a ∈ F.edge y := hneighbor_contains_a y hy
      exact ⟨hxy, ⟨a, Finset.mem_inter.mpr ⟨hax, hay⟩⟩⟩
    have hpair_zero :
        @IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f = 0 := by
      unfold IndependentPairCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hS' :
          S.card = 2 ∧ S ⊆ G.neighborFinset f ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y := by
        simpa using hS
      have hlt : 1 < S.card := by omega
      rcases Finset.one_lt_card.mp hlt with ⟨x, hxS, y, hyS, hxy⟩
      exact hS'.2.2 hxS hyS hxy (hneighbor_clique (hS'.2.1 hxS) (hS'.2.1 hyS) hxy)
    have htriple_zero :
        @IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f = 0 := by
      unfold IndependentTripleCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hS' :
          S.card = 3 ∧ S ⊆ G.neighborFinset f ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y := by
        simpa using hS
      have hlt : 1 < S.card := by omega
      rcases Finset.one_lt_card.mp hlt with ⟨x, hxS, y, hyS, hxy⟩
      exact hS'.2.2 hxS hyS hxy (hneighbor_clique (hS'.2.1 hxS) (hS'.2.1 hyS) hxy)
    have hDreal_pos : (0 : ℝ) < (D : ℝ) := by
      exact_mod_cast hDpos
    have hlocal_le_one :
        @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) (1 * D) f ≤ 1 := by
      rw [show LineGraphOfHypergraph F = G by rfl]
      simp [LocalBParameter, hdegree, hpair_zero, htriple_zero]
      have hDsub_cast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.succ_le_of_lt hDpos)]
        norm_num
      rw [hDsub_cast]
      field_simp [ne_of_gt hDreal_pos]
      linarith
    calc
      @LocalBParameter E _ _ (LineGraphOfHypergraph H)
          (Classical.decRel (LineGraphOfHypergraph H).Adj) (1 * D) e
          ≤ @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
              (Classical.decRel (LineGraphOfHypergraph F).Adj) (1 * D) f := hb_le
      _ ≤ 1 := hlocal_le_one
      _ ≤ 1 - (((1 : ℕ) : ℝ) - 1) / (2 * (((1 : ℕ) : ℝ) ^ 2)) +
            ((((1 : ℕ) : ℝ) - 1) * (((1 : ℕ) : ℝ) - 2)) /
              (6 * (((1 : ℕ) : ℝ) ^ 3) * Real.sqrt (((1 : ℕ) : ℝ))) + eta := by
          nlinarith [le_of_lt heta]
  calc
    @LocalBParameter E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e
        ≤ @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f := hb_le
    _ ≤ 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) + eta := by
        have hk_ge_two : 2 ≤ k := by omega
        let G : SimpleGraph Eloc := LineGraphOfHypergraph F
        have hneighbor_eq :
            G.neighborFinset f =
              (Finset.univ : Finset Eloc).filter
                (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty) := by
          ext g
          simp only [G, LineGraphOfHypergraph, SimpleGraph.mem_neighborFinset,
            Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hfg, hnon⟩
            exact ⟨hfg.symm, by simpa [Finset.inter_comm] using hnon⟩
          · rintro ⟨hgf, hnon⟩
            exact ⟨hgf.symm, by simpa [Finset.inter_comm] using hnon⟩
        have hdegree : G.degree f = k * D - k := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbor_eq]
          exact hsaturated.2
        have hneighbor_one :
            ∀ g : Eloc, g ≠ f → (F.edge g ∩ F.edge f).Nonempty →
              (F.edge g ∩ F.edge f).card = 1 := by
          exact KUniformNeighborOneIntersectionFromSaturation k D F f hF.1 hsaturated.1
            hsaturated.2
        let C : SimpleGraph {g : Eloc // g ∈ G.neighborFinset f} :=
          { Adj := fun x y => x ≠ y ∧ ¬ G.Adj x.1 y.1
            symm := by
              intro x y hxy
              exact ⟨hxy.1.symm, by
                intro hyx
                exact hxy.2 hyx.symm⟩
            loopless := ⟨by
              intro x hxx
              exact hxx.1 rfl⟩ }
        letI : DecidableRel C.Adj := Classical.decRel C.Adj
        let fVerts : Finset Vloc := F.edge f
        let equivF : fVerts ≃ Fin k :=
          Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hF.1 f])
        have hneighbor_meets (x : {g : Eloc // g ∈ G.neighborFinset f}) :
            (F.edge x.1 ∩ F.edge f).Nonempty := by
          have hxadj : G.Adj f x.1 := by
            have hxmem : x.1 ∈ G.neighborFinset f := x.2
            rw [SimpleGraph.mem_neighborFinset] at hxmem
            exact hxmem
          simpa [G, LineGraphOfHypergraph, Finset.inter_comm] using hxadj.2
        let meetVertex : {g : Eloc // g ∈ G.neighborFinset f} → Vloc :=
          fun x => Classical.choose (hneighbor_meets x)
        have meetVertex_mem (x : {g : Eloc // g ∈ G.neighborFinset f}) :
            meetVertex x ∈ F.edge x.1 ∩ F.edge f := by
          exact Classical.choose_spec (hneighbor_meets x)
        have meetVertex_mem_edge (x : {g : Eloc // g ∈ G.neighborFinset f}) :
            meetVertex x ∈ F.edge x.1 := (Finset.mem_inter.mp (meetVertex_mem x)).1
        have meetVertex_mem_f (x : {g : Eloc // g ∈ G.neighborFinset f}) :
            meetVertex x ∈ F.edge f := (Finset.mem_inter.mp (meetVertex_mem x)).2
        let part : {g : Eloc // g ∈ G.neighborFinset f} → Fin k :=
          fun x => equivF ⟨meetVertex x, by simpa [fVerts] using meetVertex_mem_f x⟩
        have hpartite :
            ∃ part : {g : Eloc // g ∈ G.neighborFinset f} → Fin k,
              ∀ ⦃u v : {g : Eloc // g ∈ G.neighborFinset f}⦄,
                C.Adj u v → part u ≠ part v := by
          refine ⟨part, ?_⟩
          intro u v huv hsame
          have hval_ne : u.1 ≠ v.1 := by
            intro hval
            exact huv.1 (Subtype.ext hval)
          have hmeet_card :
              (F.edge u.1 ∩ F.edge f).card = 1 := by
            have huadj : G.Adj f u.1 := by
              have humem : u.1 ∈ G.neighborFinset f := u.2
              rw [SimpleGraph.mem_neighborFinset] at humem
              exact humem
            exact hneighbor_one u.1 huadj.1.symm
              (by simpa [G, LineGraphOfHypergraph, Finset.inter_comm] using huadj.2)
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hmeet_card
          have hu_eq : meetVertex u = a := by
            have hm : meetVertex u ∈ ({a} : Finset Vloc) := by
              simpa [← ha] using meetVertex_mem u
            simpa using hm
          have hv_eq : meetVertex v = a := by
            have hmv_eq : meetVertex v = meetVertex u := by
              have hsub_eq :
                  (⟨meetVertex v, by simpa [fVerts] using meetVertex_mem_f v⟩ : fVerts) =
                    ⟨meetVertex u, by simpa [fVerts] using meetVertex_mem_f u⟩ := by
                exact equivF.injective hsame.symm
              exact congrArg Subtype.val hsub_eq
            simpa [hu_eq] using hmv_eq
          have ha_v : a ∈ F.edge v.1 := by
            simpa [← hv_eq] using meetVertex_mem_edge v
          have ha_u : a ∈ F.edge u.1 := by
            simpa [← hu_eq] using meetVertex_mem_edge u
          have huv_adj : G.Adj u.1 v.1 := by
            exact ⟨hval_ne, ⟨a, Finset.mem_inter.mpr ⟨ha_u, ha_v⟩⟩⟩
          exact huv.2 huv_adj
        have htriangle_partite :
            (((Finset.univ : Finset (Finset {g : Eloc // g ∈ G.neighborFinset f})).filter
                (fun s =>
                  s.card = 3 ∧
                    ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → C.Adj u v)).card : ℝ)
              ≤ (Nat.choose k 3 : ℝ) *
                (((C.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
          exact KPartiteTriangleCount k hk C hpartite
        have hDreal_pos : (0 : ℝ) < (D : ℝ) := by
          exact_mod_cast hDpos
        have hkD_pos : (0 : ℝ) < (k * D : ℕ) := by
          exact_mod_cast Nat.mul_pos hk hDpos
        have hlocal_expand :
            @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f =
              (G.degree f : ℝ) / (k * D : ℕ) -
                (@IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  (k * D : ℕ) ^ 2 +
                (@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  (k * D : ℕ) ^ 3 := by
          simp [LocalBParameter, G]
        have hk_real_pos : (0 : ℝ) < (k : ℝ) := by
          exact_mod_cast hk
        have hkD_nat_pos : 0 < k * D := by
          exact Nat.mul_pos hk hDpos
        have hkD_cast_ne : ((k * D : ℕ) : ℝ) ≠ 0 := by
          exact ne_of_gt hkD_pos
        have hdegree_cast :
            ((G.degree f : ℕ) : ℝ) = (k : ℝ) * (D : ℝ) - (k : ℝ) := by
          rw [hdegree]
          have hk_le_kD : k ≤ k * D := by
            exact Nat.le_mul_of_pos_right k hDpos
          rw [Nat.cast_sub hk_le_kD, Nat.cast_mul]
        have hdegree_ratio :
            ((G.degree f : ℕ) : ℝ) / ((k * D : ℕ) : ℝ) =
              1 - (1 : ℝ) / (D : ℝ) := by
          rw [hdegree_cast, Nat.cast_mul]
          field_simp [ne_of_gt hk_real_pos, ne_of_gt hDreal_pos]
        have hlocal_degree_expand :
            @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f =
              (1 - (1 : ℝ) / (D : ℝ)) -
                (@IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  (k * D : ℕ) ^ 2 +
                (@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  (k * D : ℕ) ^ 3 := by
          rw [hlocal_expand, hdegree_ratio]
        have hpair_scaled_lower :
            (((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2)) - (1 : ℝ) / (D : ℝ)
              ≤ (@IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  ((k * D : ℕ) : ℝ) ^ 2 := by
          have hden_pos : (0 : ℝ) < ((k * D : ℕ) : ℝ) ^ 2 := by
            exact sq_pos_of_ne_zero hkD_cast_ne
          rw [Nat.cast_mul]
          field_simp [ne_of_gt hk_real_pos, ne_of_gt hDreal_pos]
          nlinarith [hpair_lower]
        have hlocal_pair_reduced :
            @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f
              ≤ 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
                (@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ) /
                  ((k * D : ℕ) : ℝ) ^ 3 := by
          rw [hlocal_degree_expand]
          nlinarith [hpair_scaled_lower]
        have hC_adj :
            ∀ x y : {g : Eloc // g ∈ G.neighborFinset f},
              C.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x.1 y.1 := by
          intro x y
          rfl
        have hC_edges_le_pair :
            C.edgeFinset.card ≤
              @IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f := by
          exact NeighborhoodComplementEdgeCountLeIndependentPairCount (G := G) f C hC_adj
        have htriple_eq_triangle :
            @IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f =
              ((Finset.univ : Finset (Finset {g : Eloc // g ∈ G.neighborFinset f})).filter
                (fun s =>
                  s.card = 3 ∧
                    ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → C.Adj u v)).card := by
          exact NeighborhoodComplementTriangleCountEqualsIndependentTripleCount (G := G) f C hC_adj
        have htriple_partite_bound :
            ((@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℕ) : ℝ)
              ≤ (Nat.choose k 3 : ℝ) *
                (((C.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
          rw [htriple_eq_triangle]
          exact htriangle_partite
        let P : ℝ :=
          (@IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ)
        let T : ℝ :=
          (@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℝ)
        have hP_nonneg : 0 ≤ P := by
          dsimp [P]
          positivity
        have hT_nonneg : 0 ≤ T := by
          dsimp [T]
          positivity
        have hP_lower :
            (((k : ℝ) - 1) / 2) * (D : ℝ) ^ 2 - (k : ℝ) ^ 2 * (D : ℝ) ≤ P := by
          simpa [P, G] using hpair_lower
        have hchoose_two_pos : (0 : ℝ) < (Nat.choose k 2 : ℝ) := by
          exact_mod_cast Nat.choose_pos hk_ge_two
        have hC_ratio_nonneg :
            0 ≤ (C.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ) := by
          exact div_nonneg (by positivity) (le_of_lt hchoose_two_pos)
        have hC_ratio_le_P_ratio :
            (C.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ) ≤
              P / (Nat.choose k 2 : ℝ) := by
          have hC_le_P_real : (C.edgeFinset.card : ℝ) ≤ P := by
            dsimp [P]
            exact_mod_cast hC_edges_le_pair
          exact div_le_div_of_nonneg_right hC_le_P_real (le_of_lt hchoose_two_pos)
        have htriple_pair_bound :
            T ≤ (Nat.choose k 3 : ℝ) *
                ((P / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
          dsimp [T]
          calc
            ((@IndependentTripleCount Eloc _ _ G (Classical.decRel G.Adj) f : ℕ) : ℝ)
                ≤ (Nat.choose k 3 : ℝ) *
                    (((C.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ)) ^
                      ((3 : ℝ) / 2)) := htriple_partite_bound
            _ ≤ (Nat.choose k 3 : ℝ) *
                    ((P / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact Real.rpow_le_rpow hC_ratio_nonneg hC_ratio_le_P_ratio
                    (by norm_num)
        let y : ℝ := P / (D : ℝ) ^ 2
        have hy_nonneg : 0 ≤ y := by
          dsimp [y]
          exact div_nonneg hP_nonneg (sq_nonneg (D : ℝ))
        have hy_lower :
            ((k : ℝ) - 1) / 2 - (k : ℝ) ^ 2 / (D : ℝ) ≤ y := by
          dsimp [y]
          have hDsq_pos : (0 : ℝ) < (D : ℝ) ^ 2 := sq_pos_of_pos hDreal_pos
          calc
            ((k : ℝ) - 1) / 2 - (k : ℝ) ^ 2 / (D : ℝ)
                = ((((k : ℝ) - 1) / 2) * (D : ℝ) ^ 2 -
                    (k : ℝ) ^ 2 * (D : ℝ)) / (D : ℝ) ^ 2 := by
                  field_simp [ne_of_gt hDreal_pos, ne_of_gt hDsq_pos]
            _ ≤ P / (D : ℝ) ^ 2 := by
                  exact div_le_div_of_nonneg_right hP_lower (le_of_lt hDsq_pos)
        have hneighbor_card : (G.neighborFinset f).card = k * D - k := by
          rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree]
        have hP_le_choose_neighbor :
            @IndependentPairCount Eloc _ _ G (Classical.decRel G.Adj) f ≤
              Nat.choose (G.neighborFinset f).card 2 := by
          exact IndependentPairCountLeChooseNeighborCard G f
        have hP_le_choose_degree :
            P ≤ (Nat.choose (k * D - k) 2 : ℝ) := by
          dsimp [P]
          rw [← hneighbor_card]
          exact_mod_cast hP_le_choose_neighbor
        have hchoose_degree_le :
            (Nat.choose (k * D - k) 2 : ℝ) ≤
              ((k : ℝ) ^ 2 * (D : ℝ) ^ 2) / 2 := by
          have hsub_le : k * D - k ≤ k * D := Nat.sub_le (k * D) k
          have hsub_le_real : ((k * D - k : ℕ) : ℝ) ≤ ((k * D : ℕ) : ℝ) := by
            exact_mod_cast hsub_le
          have hsub_nonneg : 0 ≤ ((k * D - k : ℕ) : ℝ) := by positivity
          have hsub_minus_le :
              (((k * D - k : ℕ) : ℝ) - 1) ≤ ((k * D - k : ℕ) : ℝ) := by
            linarith
          have hsquares_le :
              ((k * D - k : ℕ) : ℝ) * ((k * D - k : ℕ) : ℝ) ≤
                ((k * D : ℕ) : ℝ) * ((k * D : ℕ) : ℝ) := by
            exact mul_le_mul hsub_le_real hsub_le_real hsub_nonneg (by positivity)
          calc
            (Nat.choose (k * D - k) 2 : ℝ)
                = ((k * D - k : ℕ) : ℝ) * (((k * D - k : ℕ) : ℝ) - 1) / 2 := by
                  rw [Nat.cast_choose_two]
            _ ≤ ((k * D - k : ℕ) : ℝ) * ((k * D - k : ℕ) : ℝ) / 2 := by
                  exact div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hsub_minus_le hsub_nonneg) (by norm_num)
            _ ≤ ((k * D : ℕ) : ℝ) ^ 2 / 2 := by
                  rw [sq]
                  exact div_le_div_of_nonneg_right hsquares_le (by norm_num)
            _ = ((k : ℝ) ^ 2 * (D : ℝ) ^ 2) / 2 := by
                  rw [Nat.cast_mul]
                  ring
        have hP_upper : P ≤ ((k : ℝ) ^ 2 * (D : ℝ) ^ 2) / 2 :=
          le_trans hP_le_choose_degree hchoose_degree_le
        have hy_upper : y ≤ (k : ℝ) ^ 2 / 2 := by
          dsimp [y]
          have hDsq_pos : (0 : ℝ) < (D : ℝ) ^ 2 := sq_pos_of_pos hDreal_pos
          calc
            P / (D : ℝ) ^ 2
                ≤ (((k : ℝ) ^ 2 * (D : ℝ) ^ 2) / 2) / (D : ℝ) ^ 2 := by
                  exact div_le_div_of_nonneg_right hP_upper (le_of_lt hDsq_pos)
            _ = (k : ℝ) ^ 2 / 2 := by
                  field_simp [ne_of_gt hDsq_pos]
        have hthreshold_endpoint :
            (k : ℝ) ^ 2 / (D : ℝ) ≤ ((k : ℝ) - 1) / 2 := by
          have hlarge_real : (2 : ℝ) * (k : ℝ) ^ 2 ≤ (D : ℝ) := by
            exact_mod_cast hDlarge
          have hk_sq_nonneg : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
          have hlarge_den_pos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by
            exact mul_pos (by norm_num) (sq_pos_of_pos hk_real_pos)
          have hk_sq_ne : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hk_real_pos)
          have hhalf : (k : ℝ) ^ 2 / (D : ℝ) ≤ (1 : ℝ) / 2 := by
            calc
              (k : ℝ) ^ 2 / (D : ℝ)
                  ≤ (k : ℝ) ^ 2 / (2 * (k : ℝ) ^ 2) := by
                    exact div_le_div_of_nonneg_left hk_sq_nonneg hlarge_den_pos hlarge_real
              _ = (1 : ℝ) / 2 := by
                    field_simp [hk_sq_ne]
          have hk_minus : (1 : ℝ) / 2 ≤ ((k : ℝ) - 1) / 2 := by
            have hk2_real : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge_two
            have hone_le : (1 : ℝ) ≤ (k : ℝ) - 1 := by
              have hsub := sub_le_sub_right hk2_real (1 : ℝ)
              norm_num at hsub
              exact hsub
            exact div_le_div_of_nonneg_right hone_le (by norm_num)
          exact le_trans hhalf hk_minus
        have hpair_norm :
            P / (((k * D : ℕ) : ℝ) ^ 2) = y / (k : ℝ) ^ 2 := by
          dsimp [y]
          rw [Nat.cast_mul]
          field_simp [ne_of_gt hk_real_pos, ne_of_gt hDreal_pos]
        have hDsq_rpow :
            ((D : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (D : ℝ) ^ 3 := by
          have h := Real.rpow_natCast_mul (le_of_lt hDreal_pos) 2 ((3 : ℝ) / 2)
          norm_num at h
          rw [← h]
        have htriple_norm :
            T / (((k * D : ℕ) : ℝ) ^ 3) ≤
              ((Nat.choose k 3 : ℝ) /
                  ((k : ℝ) ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))) *
                y ^ ((3 : ℝ) / 2) := by
          have hkD_cube_pos : 0 < (((k * D : ℕ) : ℝ) ^ 3) := by
            positivity
          calc
            T / (((k * D : ℕ) : ℝ) ^ 3)
                ≤ ((Nat.choose k 3 : ℝ) *
                    ((P / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2))) /
                    (((k * D : ℕ) : ℝ) ^ 3) := by
                  exact div_le_div_of_nonneg_right htriple_pair_bound (le_of_lt hkD_cube_pos)
            _ = ((Nat.choose k 3 : ℝ) /
                  ((k : ℝ) ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))) *
                y ^ ((3 : ℝ) / 2) := by
                  dsimp [y]
                  rw [Nat.cast_mul]
                  have hDsq_pos : 0 < (D : ℝ) ^ 2 := sq_pos_of_pos hDreal_pos
                  have hC_nonneg : 0 ≤ (Nat.choose k 2 : ℝ) := le_of_lt hchoose_two_pos
                  have hDsq_nonneg : 0 ≤ (D : ℝ) ^ 2 := le_of_lt hDsq_pos
                  rw [show P / (Nat.choose k 2 : ℝ) =
                      (P / (D : ℝ) ^ 2 / (Nat.choose k 2 : ℝ)) * (D : ℝ) ^ 2 by
                        field_simp [ne_of_gt hDsq_pos, ne_of_gt hchoose_two_pos]]
                  rw [Real.mul_rpow (div_nonneg (div_nonneg hP_nonneg (le_of_lt hDsq_pos))
                    hC_nonneg) hDsq_nonneg]
                  rw [Real.div_rpow (div_nonneg hP_nonneg (le_of_lt hDsq_pos))
                    hC_nonneg]
                  rw [hDsq_rpow]
                  field_simp [ne_of_gt hk_real_pos, ne_of_gt hDreal_pos,
                    ne_of_gt hchoose_two_pos,
                    ne_of_gt (Real.rpow_pos_of_pos hchoose_two_pos _)]
        have hlocal_y :
            @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f
              ≤ 1 - (1 : ℝ) / (D : ℝ) - y / (k : ℝ) ^ 2 +
                ((Nat.choose k 3 : ℝ) /
                    ((k : ℝ) ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))) *
                  y ^ ((3 : ℝ) / 2) := by
          rw [hlocal_degree_expand]
          dsimp [P, T] at hpair_norm htriple_norm
          rw [hpair_norm]
          linarith
        have hreal_est :
            1 - (1 : ℝ) / (D : ℝ) - y / (k : ℝ) ^ 2 +
                ((Nat.choose k 3 : ℝ) /
                    ((k : ℝ) ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))) *
                  y ^ ((3 : ℝ) / 2)
              ≤ 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
                (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
                  (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
          exact KUniformKSimpleBParameterRealEstimate hk_ge_two hDpos hthreshold_endpoint
            hy_nonneg hy_lower hy_upper
        linarith [hlocal_y, hreal_est, le_of_lt heta]
