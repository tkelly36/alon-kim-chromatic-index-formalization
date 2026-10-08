import Tablet.KUniformSplitEdgeHypergraph
import Tablet.UniformHypergraph

-- [TABLET NODE: KUniformSplitEdgeUniformity]
theorem KUniformSplitEdgeUniformity :
    ∀ k : ℕ, ∀ {V E : Type*} [DecidableEq V] [DecidableEq E],
      ∀ H : MultiHypergraph V E,
        UniformHypergraph H k →
        ∀ g : E, ∀ v : V, ∀ hv : v ∈ H.edge g, ∀ x1 : Fin (k - 1),
          UniformHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1) k := by
-- BODY
  classical
  intro k V E _ _ H hunif g v hv x1 e
  have hk : 0 < k := by
    have hpos : 0 < (H.edge g).card := Finset.card_pos.mpr ⟨v, hv⟩
    simpa [hunif g] using hpos
  cases e with
  | inl old =>
      by_cases hold : old = g
      · subst old
        have hdis :
            Disjoint (((H.edge g).erase v).image (Sum.inl : V → V ⊕ Fin (k - 1)))
              ({Sum.inr x1} : Finset (V ⊕ Fin (k - 1))) := by
          rw [Finset.disjoint_left]
          intro x hx hsingleton
          rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
          simp at hsingleton
        have herase_card : ((H.edge g).erase v).card = k - 1 := by
          rw [Finset.card_erase_of_mem hv, hunif g]
        calc
          ((KUniformSplitEdgeHypergraph k H g v hv x1).edge (Sum.inl g)).card
              = (((H.edge g).erase v).image (Sum.inl : V → V ⊕ Fin (k - 1)) ∪
                  ({Sum.inr x1} : Finset (V ⊕ Fin (k - 1)))).card := by
                simp [KUniformSplitEdgeHypergraph]
          _ = (((H.edge g).erase v).image (Sum.inl : V → V ⊕ Fin (k - 1))).card +
                ({Sum.inr x1} : Finset (V ⊕ Fin (k - 1))).card := by
                exact Finset.card_union_of_disjoint hdis
          _ = ((H.edge g).erase v).card + 1 := by
                rw [Finset.card_image_of_injective _ Sum.inl_injective]
                simp
          _ = k := by
                rw [herase_card]
                omega
      · calc
          ((KUniformSplitEdgeHypergraph k H g v hv x1).edge (Sum.inl old)).card
              = ((H.edge old).image (Sum.inl : V → V ⊕ Fin (k - 1))).card := by
                simp [KUniformSplitEdgeHypergraph, hold]
          _ = (H.edge old).card := by
                exact Finset.card_image_of_injective _ Sum.inl_injective
          _ = k := hunif old
  | inr new =>
      have hdis :
          Disjoint ({Sum.inl v} : Finset (V ⊕ Fin (k - 1)))
            ((Finset.univ : Finset (Fin (k - 1))).image Sum.inr) := by
        rw [Finset.disjoint_left]
        intro x hx hxin
        simp at hx
        subst hx
        simp at hxin
      have hcard_image :
          (((Finset.univ : Finset (Fin (k - 1))).image
              (Sum.inr : Fin (k - 1) → V ⊕ Fin (k - 1))).card) = k - 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · exact Sum.inr_injective
      calc
        ((KUniformSplitEdgeHypergraph k H g v hv x1).edge (Sum.inr new)).card
            = ({Sum.inl v} : Finset (V ⊕ Fin (k - 1))).card +
                (((Finset.univ : Finset (Fin (k - 1))).image
                  (Sum.inr : Fin (k - 1) → V ⊕ Fin (k - 1))).card) := by
              rw [KUniformSplitEdgeHypergraph, Finset.card_union_of_disjoint hdis]
        _ = 1 + (k - 1) := by rw [hcard_image]; simp
        _ = k := by omega
