import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.KUniformSplitEdgeHypergraph
import Tablet.KUniformSplitEdgeUniformity
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

set_option maxHeartbeats 700000

-- [TABLET NODE: KUniformSplitEdgePreservesClass]
theorem KUniformSplitEdgePreservesClass :
    ∀ k D : ℕ, 2 ≤ D →
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) k k D →
          ∀ g : E, ∀ v : V, ∀ hv : v ∈ H.edge g, ∀ x1 : Fin (k - 1),
            KUniformSplitEdgeHypergraph k H g v hv x1 ∈
              HypergraphClass (V := V ⊕ Fin (k - 1)) (E := E ⊕ Unit) k k D := by
-- BODY
  classical
  intro k D hD V E _ _ _ H hH g v hv x1
  rcases hH with ⟨hunif, hsimple, hdeg⟩
  let Hsplit : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
    KUniformSplitEdgeHypergraph k H g v hv x1
  have hunif_split : UniformHypergraph Hsplit k := by
    simpa [Hsplit] using KUniformSplitEdgeUniformity k H hunif g v hv x1
  refine ⟨hunif_split, ?_, ?_⟩
  · intro e f hef
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (hunif_split e))
  · intro x
    cases x with
    | inl w =>
        by_cases hwv : w = v
        · subst w
          have hfilter :
              ((Finset.univ : Finset (E ⊕ Unit)).filter
                (fun e => Sum.inl v ∈ Hsplit.edge e)) =
                (((Finset.univ : Finset E).filter (fun e => e ≠ g ∧ v ∈ H.edge e)).image
                    (Sum.inl : E → E ⊕ Unit)) ∪
                  ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
            ext e
            cases e with
            | inl old =>
                by_cases hold : old = g
                · subst old
                  simp [Hsplit, KUniformSplitEdgeHypergraph]
                · simp [Hsplit, KUniformSplitEdgeHypergraph, hold]
            | inr u =>
                cases u
                simp [Hsplit, KUniformSplitEdgeHypergraph]
          have hdis :
              Disjoint
                ((((Finset.univ : Finset E).filter (fun e => e ≠ g ∧ v ∈ H.edge e)).image
                  (Sum.inl : E → E ⊕ Unit)))
                ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
            rw [Finset.disjoint_left]
            intro e he hs
            rcases Finset.mem_image.mp he with ⟨old, hold, rfl⟩
            simp at hs
          have hfilter_old :
              ((Finset.univ : Finset E).filter (fun e => e ≠ g ∧ v ∈ H.edge e)) =
                ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).erase g := by
            ext e
            by_cases heg : e = g
            · subst e
              simp [hv]
            · simp [heg]
          have hmem_old :
              g ∈ ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)) := by
            simp [hv]
          calc
            HypergraphDegree Hsplit (Sum.inl v)
                = (((Finset.univ : Finset E).filter (fun e => e ≠ g ∧ v ∈ H.edge e)).card) + 1 := by
                  simp [HypergraphDegree, hfilter, Finset.card_union_of_disjoint hdis,
                    Finset.card_image_of_injective _ Sum.inl_injective]
            _ = HypergraphDegree H v := by
                  rw [hfilter_old, HypergraphDegree, Finset.card_erase_of_mem hmem_old]
                  have hpos : 0 < ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).card :=
                    Finset.card_pos.mpr ⟨g, hmem_old⟩
                  omega
            _ ≤ D := hdeg v
        · have hfilter :
              ((Finset.univ : Finset (E ⊕ Unit)).filter
                (fun e => Sum.inl w ∈ Hsplit.edge e)) =
                (((Finset.univ : Finset E).filter (fun e => w ∈ H.edge e)).image
                    (Sum.inl : E → E ⊕ Unit)) := by
            ext e
            cases e with
            | inl old =>
                by_cases hold : old = g
                · subst old
                  simp [Hsplit, KUniformSplitEdgeHypergraph, hwv]
                · simp [Hsplit, KUniformSplitEdgeHypergraph, hold]
            | inr u =>
                cases u
                simp [Hsplit, KUniformSplitEdgeHypergraph, hwv]
          calc
            HypergraphDegree Hsplit (Sum.inl w)
                = HypergraphDegree H w := by
                  simp [HypergraphDegree, hfilter,
                    Finset.card_image_of_injective _ Sum.inl_injective]
            _ ≤ D := hdeg w
    | inr y =>
        have hfilter_subset :
            ((Finset.univ : Finset (E ⊕ Unit)).filter
              (fun e => Sum.inr y ∈ Hsplit.edge e)) ⊆
              ({Sum.inl g, Sum.inr ()} : Finset (E ⊕ Unit)) := by
          intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          cases e with
          | inl old =>
              by_cases hold : old = g
              · subst old
                simp
              · simp [Hsplit, KUniformSplitEdgeHypergraph, hold] at he
          | inr u =>
              cases u
              simp
        calc
          HypergraphDegree Hsplit (Sum.inr y)
              ≤ ({Sum.inl g, Sum.inr ()} : Finset (E ⊕ Unit)).card := by
                exact Finset.card_le_card hfilter_subset
          _ ≤ 2 := by simp
          _ ≤ D := hD
