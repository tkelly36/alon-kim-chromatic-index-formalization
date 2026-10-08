import Tablet.KUniformFreshEdgeHypergraph
import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: KUniformFreshEdgeLineGraphNeighborCount]
theorem KUniformFreshEdgeLineGraphNeighborCount :
    ∀ k : ℕ, ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E, ∀ f : E, ∀ v : V,
        [DecidableRel (LineGraphOfHypergraph H).Adj] →
        [DecidableRel (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj] →
        v ∈ H.edge f →
          ((Finset.univ : Finset (E ⊕ Unit)).filter
              (fun e =>
                (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj
                  (Sum.inl f) e)).card =
            ((Finset.univ : Finset E).filter
              (fun e => (LineGraphOfHypergraph H).Adj f e)).card + 1 := by
-- BODY
  classical
  intro k V E _ _ _ H f v _ _ hvf
  let sOld : Finset (E ⊕ Unit) :=
    (((Finset.univ : Finset E).filter
      (fun e => (LineGraphOfHypergraph H).Adj f e)).image Sum.inl)
  have himage_nonempty (old : E) :
      (Finset.image (Sum.inl : V → V ⊕ Fin (k - 1)) (H.edge f) ∩
          Finset.image Sum.inl (H.edge old)).Nonempty ↔
        (H.edge f ∩ H.edge old).Nonempty := by
    constructor
    · intro h
      rcases h with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxf, hxo⟩
      rcases Finset.mem_image.mp hxf with ⟨a, haf, rfl⟩
      rcases Finset.mem_image.mp hxo with ⟨b, hbo, hb⟩
      cases hb
      exact ⟨a, Finset.mem_inter.mpr ⟨haf, hbo⟩⟩
    · intro h
      rcases h with ⟨a, ha⟩
      rcases Finset.mem_inter.mp ha with ⟨haf, hao⟩
      exact ⟨Sum.inl a,
        Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨a, haf, rfl⟩,
            Finset.mem_image.mpr ⟨a, hao, rfl⟩⟩⟩
  have hfilter :
      ((Finset.univ : Finset (E ⊕ Unit)).filter
        (fun e =>
          (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj
            (Sum.inl f) e)) =
        sOld ∪ ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
    ext e
    cases e with
    | inl old =>
        simp [sOld, LineGraphOfHypergraph, KUniformFreshEdgeHypergraph,
          himage_nonempty old]
    | inr u =>
        cases u
        simp [sOld, LineGraphOfHypergraph, KUniformFreshEdgeHypergraph, hvf]
  have hdis : Disjoint sOld ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
    rw [Finset.disjoint_left]
    intro x hx hxs
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    simp at hxs
  calc
    ((Finset.univ : Finset (E ⊕ Unit)).filter
        (fun e =>
          (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj
            (Sum.inl f) e)).card
        = (sOld ∪ ({Sum.inr ()} : Finset (E ⊕ Unit))).card := by
          rw [hfilter]
    _ = sOld.card + ({Sum.inr ()} : Finset (E ⊕ Unit)).card :=
          Finset.card_union_of_disjoint hdis
    _ = ((Finset.univ : Finset E).filter
        (fun e => (LineGraphOfHypergraph H).Adj f e)).card + 1 := by
          simp [sOld, Finset.card_image_of_injective _ Sum.inl_injective]
