import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.KUniformFreshEdgeIndependentPairUpperBound
import Tablet.KUniformFreshEdgeIndependentTripleLowerBound
import Tablet.KUniformFreshEdgeLineGraphNeighborCount
import Tablet.KUniformSaturatedOneIntersectionNeighborCount
import Tablet.KUniformFreshEdgePreservesClass
import Tablet.KUniformDoubleIntersectionNeighborCountUpperBound
import Tablet.KUniformSplitEdgeHypergraph
import Tablet.KUniformSplitEdgeIndependentPairUpperBound
import Tablet.KUniformSplitEdgeIndependentTripleLowerBound
import Tablet.KUniformSplitEdgeLineGraphNeighborCount
import Tablet.KUniformSplitEdgePreservesClass
import Tablet.KUniformSplitEdgeUniformity
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.LocalBParameterStrictIncrease
import Tablet.MaxDegreeAtMost
import Tablet.OneUniformNonemptyIntersectionCard
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

universe u v

-- [TABLET NODE: KUniformKSimpleExtremalSaturation]
theorem KUniformKSimpleExtremalSaturation :
    ∀ k : ℕ, 0 < k →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) k k D →
            ∀ f : E,
              (∀ {V' : Type u} {E' : Type v}
                [Fintype E'] [DecidableEq E'] [DecidableEq V'],
                ∀ H' : MultiHypergraph V' E',
                  H' ∈ HypergraphClass (V := V') (E := E') k k D →
                  ∀ e' : E',
                    @LocalBParameter E' _ _ (LineGraphOfHypergraph H')
                        (Classical.decRel (LineGraphOfHypergraph H').Adj) (k * D) e'
                      ≤ @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                        (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) f) →
              (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) ∧
                ((Finset.univ : Finset E).filter
                  (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := by
-- BODY
  classical
  intro k hk
  refine ⟨2, ?_⟩
  intro D hD V E _ _ _ H hH f hmax
  have hunif : UniformHypergraph H k := hH.1
  have hcount_from_endpoint :
      (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
        (∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
          (H.edge g ∩ H.edge f).card = 1) →
        ((Finset.univ : Finset E).filter
          (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := by
    intro hsat hone
    exact KUniformSaturatedOneIntersectionNeighborCount k D H f hunif hsat hone
  have hfresh_preserves :
      ∀ v : V,
        HypergraphDegree H v < D →
          KUniformFreshEdgeHypergraph k H v ∈
            HypergraphClass (V := V ⊕ Fin (k - 1)) (E := E ⊕ Unit) k k D := by
    intro v hv
    exact KUniformFreshEdgePreservesClass k D hk H hH v hv
  have hfresh_line_degree :
      ∀ v : V, v ∈ H.edge f →
        ((Finset.univ : Finset (E ⊕ Unit)).filter
            (fun e =>
              (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj
                (Sum.inl f) e)).card =
          ((Finset.univ : Finset E).filter
            (fun e => (LineGraphOfHypergraph H).Adj f e)).card + 1 := by
    intro v hv
    exact KUniformFreshEdgeLineGraphNeighborCount k H f v hv
  have hfresh_pair_bound :
      ∀ v : V,
        IndependentPairCount
            (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)) (Sum.inl f) ≤
          IndependentPairCount (LineGraphOfHypergraph H) f +
            ((Finset.univ : Finset E).filter
              (fun e => (LineGraphOfHypergraph H).Adj f e)).card := by
    intro v
    exact KUniformFreshEdgeIndependentPairUpperBound k H f v
  have hfresh_triple_bound :
      ∀ v : V,
        IndependentTripleCount (LineGraphOfHypergraph H) f ≤
          IndependentTripleCount
            (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)) (Sum.inl f) := by
    intro v
    exact KUniformFreshEdgeIndependentTripleLowerBound k H f v
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num : 0 < 2) hD
  have hsat : ∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D := by
    intro v hvf
    apply le_antisymm
    · exact hH.2.2 v
    · by_contra hnot
      have hlow : HypergraphDegree H v < D := Nat.lt_of_not_ge hnot
      let Hnew : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
        KUniformFreshEdgeHypergraph k H v
      let Gold := LineGraphOfHypergraph H
      let Gnew := LineGraphOfHypergraph Hnew
      let M : ℕ := k * D
      let dOld : ℕ := ((Finset.univ : Finset E).filter (fun e => Gold.Adj f e)).card
      have hMpos : 0 < M := by
        dsimp [M]
        exact Nat.mul_pos hk hDpos
      have hnewClass :
          Hnew ∈ HypergraphClass (V := V ⊕ Fin (k - 1)) (E := E ⊕ Unit) k k D := by
        simpa [Hnew] using hfresh_preserves v hlow
      have hmax_new :
          @LocalBParameter (E ⊕ Unit) _ _ Gnew
              (Classical.decRel Gnew.Adj) M (Sum.inl f)
            ≤ @LocalBParameter E _ _ Gold
              (Classical.decRel Gold.Adj) M f := by
        simpa [Hnew, Gnew, Gold, M] using
          hmax (V' := V ⊕ Fin (k - 1)) (E' := E ⊕ Unit) Hnew hnewClass (Sum.inl f)
      have hdegree_new :
          Gnew.degree (Sum.inl f) = dOld + 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        simpa [SimpleGraph.neighborFinset, Gnew, Hnew, Gold, dOld] using
          hfresh_line_degree v hvf
      have hdegree_old :
          Gold.degree f = dOld := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        simp [SimpleGraph.neighborFinset, dOld]
      have hneighbor_subset :
          (Gold.neighborFinset f) ⊆
            (H.edge f).biUnion (fun x =>
              ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e))) := by
        intro e he
        rcases (by
            simpa [SimpleGraph.mem_neighborFinset, Gold, LineGraphOfHypergraph]
              using he) with ⟨hef, hnon⟩
        rcases hnon with ⟨x, hx⟩
        rcases Finset.mem_inter.mp hx with ⟨hxf, hxe⟩
        exact Finset.mem_biUnion.mpr
          ⟨x, hxf, by
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ e,
                ⟨by
                  intro hef'
                  exact hef hef'.symm,
                hxe⟩⟩⟩
      have hincident_bound (x : V) (hx : x ∈ H.edge f) :
          (((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)).card) ≤
            D - 1 := by
        have hmem :
            f ∈ ((Finset.univ : Finset E).filter (fun e => x ∈ H.edge e)) := by
          simp [hx]
        have hfilter :
            ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)) =
              ((Finset.univ : Finset E).filter (fun e => x ∈ H.edge e)).erase f := by
          ext e
          by_cases hef : e = f
          · subst hef
            simp [hx]
          · simp [hef]
        rw [hfilter, Finset.card_erase_of_mem hmem]
        exact Nat.pred_le_pred (hH.2.2 x)
      have hneighbor_le :
          dOld ≤ k * (D - 1) := by
        have hcard_bi :
            ((H.edge f).biUnion (fun x =>
              ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)))).card
                ≤ (H.edge f).card * (D - 1) :=
          Finset.card_biUnion_le_card_mul (s := H.edge f)
            (f := fun x => ((Finset.univ : Finset E).filter
              (fun e => e ≠ f ∧ x ∈ H.edge e)))
            (n := D - 1) hincident_bound
        have hdeg_le := Finset.card_le_card hneighbor_subset
        have hcardf : (H.edge f).card = k := hunif f
        calc
          dOld = (Gold.neighborFinset f).card := by
            simp [SimpleGraph.neighborFinset, dOld]
          _ ≤ ((H.edge f).biUnion (fun x =>
              ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)))).card :=
                hdeg_le
          _ ≤ (H.edge f).card * (D - 1) := hcard_bi
          _ = k * (D - 1) := by rw [hcardf]
      have hdOld_lt_M : dOld < M := by
        dsimp [M]
        calc
          dOld ≤ k * (D - 1) := hneighbor_le
          _ < k * D := Nat.mul_lt_mul_of_pos_left
            (Nat.sub_lt hDpos (by norm_num : 0 < 1)) hk
      have hpair :
          IndependentPairCount Gnew (Sum.inl f) ≤
            IndependentPairCount Gold f + dOld := by
        simpa [Gnew, Hnew, Gold, dOld] using hfresh_pair_bound v
      have htriple :
          IndependentTripleCount Gold f ≤
            IndependentTripleCount Gnew (Sum.inl f) := by
        simpa [Gnew, Hnew, Gold] using hfresh_triple_bound v
      have hstrict :
          @LocalBParameter (E ⊕ Unit) _ _ Gnew
              (Classical.decRel Gnew.Adj) M (Sum.inl f)
            > @LocalBParameter E _ _ Gold
              (Classical.decRel Gold.Adj) M f := by
        exact LocalBParameterStrictIncrease Gold Gnew f (Sum.inl f) M
          dOld hMpos (by simpa [hdegree_old] using hdegree_new)
          hpair htriple hdOld_lt_M
      exact not_lt_of_ge hmax_new hstrict
  refine ⟨hsat, ?_⟩
  apply hcount_from_endpoint hsat
  intro g hgf hnon
  by_cases hk_one : k = 1
  · subst k
    exact OneUniformNonemptyIntersectionCard H hunif f g hnon
  · have hk_gt_one : 1 < k := by
      exact lt_of_le_of_ne (Nat.succ_le_of_lt hk) (Ne.symm hk_one)
    by_contra hcard_ne
    let S : Finset V := H.edge g ∩ H.edge f
    have hSpos : 0 < S.card := Finset.card_pos.mpr hnon
    have hS_ne_one : S.card ≠ 1 := by
      simpa [S] using hcard_ne
    have hS_two : 2 ≤ S.card := by
      omega
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS_two
    obtain ⟨u, v, huv, hTuv⟩ := (Finset.card_eq_two.mp hTcard)
    have huS : u ∈ S := by
      exact hTS (by simp [hTuv])
    have hvS : v ∈ S := by
      exact hTS (by simp [hTuv])
    have hug : u ∈ H.edge g := (Finset.mem_inter.mp huS).1
    have huf : u ∈ H.edge f := (Finset.mem_inter.mp huS).2
    have hvg : v ∈ H.edge g := (Finset.mem_inter.mp hvS).1
    have hvf : v ∈ H.edge f := (Finset.mem_inter.mp hvS).2
    have hkm1 : 0 < k - 1 := Nat.sub_pos_of_lt hk_gt_one
    let x1 : Fin (k - 1) := ⟨0, hkm1⟩
    let Hsplit : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
      KUniformSplitEdgeHypergraph k H g v hvg x1
    let Gold := LineGraphOfHypergraph H
    let Gsplit := LineGraphOfHypergraph Hsplit
    let M : ℕ := k * D
    let oldNeighbors : Finset E :=
      (Finset.univ : Finset E).filter (fun e => Gold.Adj f e)
    let dOld : ℕ := oldNeighbors.card
    let dErase : ℕ := (oldNeighbors.erase g).card
    have hMpos : 0 < M := by
      dsimp [M]
      exact Nat.mul_pos hk hDpos
    have hsplitClass :
        Hsplit ∈ HypergraphClass (V := V ⊕ Fin (k - 1)) (E := E ⊕ Unit) k k D := by
      simpa [Hsplit] using KUniformSplitEdgePreservesClass k D hD H hH g v hvg x1
    have hmax_split :
        @LocalBParameter (E ⊕ Unit) _ _ Gsplit
            (Classical.decRel Gsplit.Adj) M (Sum.inl f)
          ≤ @LocalBParameter E _ _ Gold
            (Classical.decRel Gold.Adj) M f := by
      simpa [Hsplit, Gsplit, Gold, M] using
        hmax (V' := V ⊕ Fin (k - 1)) (E' := E ⊕ Unit) Hsplit hsplitClass
          (Sum.inl f)
    have hdegree_new :
        Gsplit.degree (Sum.inl f) = dOld + 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      simpa [SimpleGraph.neighborFinset, Gsplit, Hsplit, Gold, oldNeighbors, dOld] using
        KUniformSplitEdgeLineGraphNeighborCount k H f g u v hgf huv huf hvf hug hvg x1
    have hdegree_old :
        Gold.degree f = dOld := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      simp [SimpleGraph.neighborFinset, Gold, oldNeighbors, dOld]
    have hdOld_bound : dOld ≤ k * (D - 1) - 1 := by
      simpa [Gold, oldNeighbors, dOld] using
        KUniformDoubleIntersectionNeighborCountUpperBound k D H f g u v hunif hsat hgf
          huv huf hvf hug hvg
    have hdOld_lt_M : dOld < M := by
      dsimp [M]
      have hbase : k * (D - 1) - 1 < k * D := by
        have hlt : k * (D - 1) < k * D :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.sub_lt hDpos (by norm_num : 0 < 1)) hk
        omega
      exact lt_of_le_of_lt hdOld_bound hbase
    have hdErase_lt_M : dErase < M := by
      have herase_le : dErase ≤ dOld := by
        dsimp [dErase, dOld]
        exact Finset.card_erase_le
      exact lt_of_le_of_lt herase_le hdOld_lt_M
    have hpair :
        IndependentPairCount Gsplit (Sum.inl f) ≤
          IndependentPairCount Gold f + dErase := by
      simpa [Gsplit, Hsplit, Gold, oldNeighbors, dErase] using
        KUniformSplitEdgeIndependentPairUpperBound k H f g u v hgf huv huf hvf hug hvg x1
    have htriple :
        IndependentTripleCount Gold f ≤
          IndependentTripleCount Gsplit (Sum.inl f) := by
      simpa [Gsplit, Hsplit, Gold] using
        KUniformSplitEdgeIndependentTripleLowerBound k H f g u v hgf huv huf hug hvg x1
    have hstrict :
        @LocalBParameter (E ⊕ Unit) _ _ Gsplit
            (Classical.decRel Gsplit.Adj) M (Sum.inl f)
          > @LocalBParameter E _ _ Gold
            (Classical.decRel Gold.Adj) M f := by
      exact LocalBParameterStrictIncrease Gold Gsplit f (Sum.inl f) M
        dErase hMpos (by simpa [hdegree_old] using hdegree_new)
        hpair htriple hdErase_lt_M
    exact not_lt_of_ge hmax_split hstrict
