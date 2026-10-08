import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.KUniformFreshEdgeHypergraph
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

set_option maxHeartbeats 500000

-- [TABLET NODE: KUniformFreshEdgePreservesClass]
theorem KUniformFreshEdgePreservesClass :
    ∀ k D : ℕ, 0 < k →
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) k k D →
          ∀ v : V,
            HypergraphDegree H v < D →
            KUniformFreshEdgeHypergraph k H v ∈
              HypergraphClass (V := V ⊕ Fin (k - 1)) (E := E ⊕ Unit) k k D := by
-- BODY
  classical
  intro k D hk V E _ _ _ H hH v hlow
  rcases hH with ⟨hunif, hsimple, hdeg⟩
  have hDpos : 0 < D := Nat.lt_of_le_of_lt (Nat.zero_le _) hlow
  refine ⟨?_, ?_, ?_⟩
  · intro e
    cases e with
    | inl old =>
        simpa [KUniformFreshEdgeHypergraph, hunif old] using
          (Finset.card_image_of_injective (H.edge old) Sum.inl_injective)
    | inr u =>
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
          ((KUniformFreshEdgeHypergraph k H v).edge (Sum.inr u)).card
              = ({Sum.inl v} : Finset (V ⊕ Fin (k - 1))).card +
                  (((Finset.univ : Finset (Fin (k - 1))).image
                    (Sum.inr : Fin (k - 1) → V ⊕ Fin (k - 1))).card) := by
                rw [KUniformFreshEdgeHypergraph, Finset.card_union_of_disjoint hdis]
          _ = 1 + (k - 1) := by rw [hcard_image]; simp
          _ = k := by omega
  · intro e f hef
    cases e with
    | inl eold =>
        cases f with
        | inl fold =>
            have holdneq : eold ≠ fold := by
              intro h
              exact hef (by simp [h])
            have himage :
                ((H.edge eold).image (Sum.inl : V → V ⊕ Fin (k - 1)) ∩
                    (H.edge fold).image Sum.inl) =
                  ((H.edge eold ∩ H.edge fold).image Sum.inl) := by
              ext x
              constructor
              · intro hx
                rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
                rcases Finset.mem_image.mp hx₁ with ⟨a, ha, rfl⟩
                rcases Finset.mem_image.mp hx₂ with ⟨b, hb, hab⟩
                cases hab
                exact Finset.mem_image.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, hb⟩, rfl⟩
              · intro hx
                rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
                exact Finset.mem_inter.mpr
                  ⟨Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩,
                    Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).2, rfl⟩⟩
            calc
              (((KUniformFreshEdgeHypergraph k H v).edge (Sum.inl eold)) ∩
                  ((KUniformFreshEdgeHypergraph k H v).edge (Sum.inl fold))).card
                  = ((H.edge eold ∩ H.edge fold).image Sum.inl).card := by
                    rw [KUniformFreshEdgeHypergraph, himage]
              _ = (H.edge eold ∩ H.edge fold).card := by
                    exact Finset.card_image_of_injective _ Sum.inl_injective
              _ ≤ k := hsimple holdneq
        | inr u =>
            have hsubset :
                ((KUniformFreshEdgeHypergraph k H v).edge (Sum.inl eold) ∩
                    (KUniformFreshEdgeHypergraph k H v).edge (Sum.inr u)) ⊆
                  ({Sum.inl v} : Finset (V ⊕ Fin (k - 1))) := by
              intro x hx
              rcases Finset.mem_inter.mp hx with ⟨hxold, hxnew⟩
              rcases Finset.mem_image.mp hxold with ⟨a, ha, rfl⟩
              simp [KUniformFreshEdgeHypergraph] at hxnew
              simp [hxnew]
            exact le_trans (Finset.card_le_card hsubset) (by simpa using hk)
    | inr u =>
        cases f with
        | inl fold =>
            have hsubset :
                ((KUniformFreshEdgeHypergraph k H v).edge (Sum.inr u) ∩
                    (KUniformFreshEdgeHypergraph k H v).edge (Sum.inl fold)) ⊆
                  ({Sum.inl v} : Finset (V ⊕ Fin (k - 1))) := by
              intro x hx
              rcases Finset.mem_inter.mp hx with ⟨hxnew, hxold⟩
              rcases Finset.mem_image.mp hxold with ⟨a, ha, rfl⟩
              simp [KUniformFreshEdgeHypergraph] at hxnew
              simp [hxnew]
            exact le_trans (Finset.card_le_card hsubset) (by simpa using hk)
        | inr w =>
            exfalso
            exact hef (by cases u; cases w; rfl)
  · intro x
    cases x with
    | inl oldv =>
        by_cases hxv : oldv = v
        · subst oldv
          have hfilter :
              ((Finset.univ : Finset (E ⊕ Unit)).filter
                (fun e => Sum.inl v ∈ (KUniformFreshEdgeHypergraph k H v).edge e)) =
                (((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).image Sum.inl) ∪
                  ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
            ext e
            cases e with
            | inl old =>
                simp [KUniformFreshEdgeHypergraph]
            | inr u =>
                cases u
                simp [KUniformFreshEdgeHypergraph]
          have hdis :
              Disjoint ((((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).image
                (Sum.inl : E → E ⊕ Unit))) ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
            rw [Finset.disjoint_left]
            intro x hx hxs
            rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
            simp at hxs
          calc
            HypergraphDegree (KUniformFreshEdgeHypergraph k H v) (Sum.inl v)
                = HypergraphDegree H v + 1 := by
                  simp [HypergraphDegree, hfilter,
                    Finset.card_image_of_injective _ Sum.inl_injective]
            _ ≤ D := Nat.succ_le_of_lt hlow
        · have hfilter :
              ((Finset.univ : Finset (E ⊕ Unit)).filter
                (fun e => Sum.inl oldv ∈ (KUniformFreshEdgeHypergraph k H v).edge e)) =
                (((Finset.univ : Finset E).filter (fun e => oldv ∈ H.edge e)).image Sum.inl) := by
            ext e
            cases e with
            | inl old =>
                simp [KUniformFreshEdgeHypergraph]
            | inr u =>
                simp [KUniformFreshEdgeHypergraph, hxv]
          calc
            HypergraphDegree (KUniformFreshEdgeHypergraph k H v) (Sum.inl oldv)
                = HypergraphDegree H oldv := by
                  simp [HypergraphDegree, hfilter,
                    Finset.card_image_of_injective _ Sum.inl_injective]
            _ ≤ D := hdeg oldv
    | inr fresh =>
        have hfilter :
            ((Finset.univ : Finset (E ⊕ Unit)).filter
              (fun e => Sum.inr fresh ∈ (KUniformFreshEdgeHypergraph k H v).edge e)) =
              ({Sum.inr ()} : Finset (E ⊕ Unit)) := by
          ext e
          cases e with
          | inl old =>
              simp [KUniformFreshEdgeHypergraph]
          | inr u =>
              cases u
              simp [KUniformFreshEdgeHypergraph]
        calc
          HypergraphDegree (KUniformFreshEdgeHypergraph k H v) (Sum.inr fresh) = 1 := by
            simp [HypergraphDegree, hfilter]
          _ ≤ D := hDpos
