import Tablet.KUniformSplitEdgeHypergraph
import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: KUniformSplitEdgeLineGraphNeighborCount]
theorem KUniformSplitEdgeLineGraphNeighborCount :
      ∀ k : ℕ, ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E, ∀ f g : E, ∀ u v : V,
        [DecidableRel (LineGraphOfHypergraph H).Adj] →
        g ≠ f → u ≠ v → u ∈ H.edge f → v ∈ H.edge f → u ∈ H.edge g →
          ∀ hv : v ∈ H.edge g, ∀ x1 : Fin (k - 1),
            [DecidableRel
              (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1)).Adj] →
            ((Finset.univ : Finset (E ⊕ Unit)).filter
                (fun e =>
                  (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1)).Adj
                    (Sum.inl f) e)).card =
              ((Finset.univ : Finset E).filter
                (fun e => (LineGraphOfHypergraph H).Adj f e)).card + 1 := by
-- BODY
  classical
  intro k V E _ _ _ H f g u v _ hgf huv huf hvf hug hv x1 _
  let Hsplit : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
    KUniformSplitEdgeHypergraph k H g v hv x1
  let sOld : Finset (E ⊕ Unit) :=
    (((Finset.univ : Finset E).filter
      (fun e => (LineGraphOfHypergraph H).Adj f e)).image Sum.inl)
  have hfg : f ≠ g := hgf.symm
  have hf_edge :
      Hsplit.edge (Sum.inl f) = Finset.image Sum.inl (H.edge f) := by
    simp [Hsplit, KUniformSplitEdgeHypergraph, hfg]
  have hg_split_meets :
      (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge (Sum.inl g)).Nonempty := by
    refine ⟨Sum.inl u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [hf_edge]
      exact Finset.mem_image.mpr ⟨u, huf, rfl⟩
    · simp [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase, hug, huv]
  have hg_old_meets : (H.edge f ∩ H.edge g).Nonempty :=
    ⟨u, Finset.mem_inter.mpr ⟨huf, hug⟩⟩
  have himage_nonempty (old : E) (hold : old ≠ g) :
      (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge (Sum.inl old)).Nonempty ↔
        (H.edge f ∩ H.edge old).Nonempty := by
    constructor
    · intro h
      rcases h with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxf, hxo⟩
      rw [hf_edge] at hxf
      have hold_edge :
          Hsplit.edge (Sum.inl old) = Finset.image Sum.inl (H.edge old) := by
        simp [Hsplit, KUniformSplitEdgeHypergraph, hold]
      rw [hold_edge] at hxo
      rcases Finset.mem_image.mp hxf with ⟨a, haf, rfl⟩
      rcases Finset.mem_image.mp hxo with ⟨b, hbo, hb⟩
      cases hb
      exact ⟨a, Finset.mem_inter.mpr ⟨haf, hbo⟩⟩
    · intro h
      rcases h with ⟨a, ha⟩
      rcases Finset.mem_inter.mp ha with ⟨haf, hao⟩
      refine ⟨Sum.inl a, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [hf_edge]
        exact Finset.mem_image.mpr ⟨a, haf, rfl⟩
      · have hold_edge :
            Hsplit.edge (Sum.inl old) = Finset.image Sum.inl (H.edge old) := by
          simp [Hsplit, KUniformSplitEdgeHypergraph, hold]
        rw [hold_edge]
        exact Finset.mem_image.mpr ⟨a, hao, rfl⟩
  have hold_adj (old : E) :
      (LineGraphOfHypergraph Hsplit).Adj (Sum.inl f) (Sum.inl old) ↔
        (LineGraphOfHypergraph H).Adj f old := by
    by_cases hof : old = f
    · subst old
      simp [LineGraphOfHypergraph]
    · by_cases hog : old = g
      · subst old
        simp [LineGraphOfHypergraph, hfg, hg_split_meets, hg_old_meets]
      · simp [LineGraphOfHypergraph, himage_nonempty old hog]
  have hfilter :
      ((Finset.univ : Finset (E ⊕ Unit)).filter
        (fun e =>
          (LineGraphOfHypergraph Hsplit).Adj (Sum.inl f) e)) =
        sOld ∪ ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
    ext e
    cases e with
    | inl old =>
        simp [sOld, hold_adj old]
    | inr unitLabel =>
        cases unitLabel
        have hnew_meets :
            (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge (Sum.inr ())).Nonempty := by
          refine ⟨Sum.inl v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
          · rw [hf_edge]
            exact Finset.mem_image.mpr ⟨v, hvf, rfl⟩
          · simp [Hsplit, KUniformSplitEdgeHypergraph]
        simp [sOld, LineGraphOfHypergraph, hnew_meets]
  have hdis : Disjoint sOld ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
    rw [Finset.disjoint_left]
    intro x hx hxs
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    simp at hxs
  calc
    ((Finset.univ : Finset (E ⊕ Unit)).filter
        (fun e =>
          (LineGraphOfHypergraph Hsplit).Adj (Sum.inl f) e)).card
        = (sOld ∪ ({Sum.inr ()} : Finset (E ⊕ Unit))).card := by
          rw [hfilter]
    _ = sOld.card + ({Sum.inr ()} : Finset (E ⊕ Unit)).card :=
          Finset.card_union_of_disjoint hdis
    _ = ((Finset.univ : Finset E).filter
        (fun e => (LineGraphOfHypergraph H).Adj f e)).card + 1 := by
          simp [sOld, Finset.card_image_of_injective _ Sum.inl_injective]
