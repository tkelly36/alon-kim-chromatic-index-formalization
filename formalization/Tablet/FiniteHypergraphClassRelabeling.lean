import Tablet.HypergraphClass
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport

universe u v u' v'

-- [TABLET NODE: FiniteHypergraphClassRelabeling]
theorem FiniteHypergraphClassRelabeling
    {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V]
    (k t D M : ℕ) (H : MultiHypergraph V E)
    (hH : H ∈ HypergraphClass (V := V) (E := E) k t D) (f : E)
    (_hMpos : 0 < M) (_hMbound : k * D ≤ M) :
    ∃ (V' : Type u') (E' : Type v') (_ : Fintype V') (_ : Fintype E')
      (_ : DecidableEq E') (_ : DecidableEq V') (H' : MultiHypergraph V' E') (f' : E'),
      H' ∈ HypergraphClass (V := V') (E := E') k t D ∧
      @LocalBParameter E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) M f =
      @LocalBParameter E' _ _ (LineGraphOfHypergraph H')
        (Classical.decRel (LineGraphOfHypergraph H').Adj) M f' := by
-- BODY
  classical
  let S : Finset V := Finset.univ.biUnion H.edge
  have hmem (e : E) {x : V} (hx : x ∈ H.edge e) : x ∈ S :=
    Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, hx⟩
  let U : Type u' := ULift.{u'} (Fin (Fintype.card S))
  let W : Type v' := ULift.{v'} (Fin (Fintype.card E))
  let a : U ≃ S := Equiv.ulift.trans (Fintype.equivFin S).symm
  let b : E ≃ W := (Fintype.equivFin E).trans Equiv.ulift.symm
  let i : U ↪ V := a.toEmbedding.trans (Function.Embedding.subtype _)
  have hi (z : U) : i z ∈ S := (a z).property
  have hisurj {x : V} (hx : x ∈ S) : ∃ z : U, i z = x := by
    exact ⟨a.symm ⟨x, hx⟩, by simp [i]⟩
  let F : MultiHypergraph U W :=
    ⟨fun e => Finset.univ.filter (fun z => i z ∈ H.edge (b.symm e))⟩
  have hinc (e : W) (z : U) : z ∈ F.edge e ↔ i z ∈ H.edge (b.symm e) := by
    simp [F]
  have hcard (e : W) : (F.edge e).card = (H.edge (b.symm e)).card := by
    apply Finset.card_bij (fun z _ => i z)
    · intro z hz; exact (hinc e z).mp hz
    · intro x hx y hy heq; exact i.injective heq
    · intro x hx
      obtain ⟨z, rfl⟩ := hisurj (hmem _ hx)
      exact ⟨z, (hinc e z).mpr hx, rfl⟩
  have hinter (e g : W) :
      (F.edge e ∩ F.edge g).card = (H.edge (b.symm e) ∩ H.edge (b.symm g)).card := by
    apply Finset.card_bij (fun z _ => i z)
    · intro z hz
      exact Finset.mem_inter.mpr ⟨(hinc e z).mp (Finset.mem_inter.mp hz).1,
        (hinc g z).mp (Finset.mem_inter.mp hz).2⟩
    · intro x hx y hy heq; exact i.injective heq
    · intro x hx
      obtain ⟨z, rfl⟩ := hisurj (hmem _ (Finset.mem_inter.mp hx).1)
      exact ⟨z, Finset.mem_inter.mpr
        ⟨(hinc e z).mpr (Finset.mem_inter.mp hx).1,
          (hinc g z).mpr (Finset.mem_inter.mp hx).2⟩, rfl⟩
  have hclass : F ∈ HypergraphClass (V := U) (E := W) k t D := by
    refine ⟨fun e => (hcard e).trans (hH.1 _), ?_, ?_⟩
    · intro e g heg
      rw [hinter]
      exact hH.2.1 (fun h => heg (b.symm.injective h))
    · intro z
      have hdeg : HypergraphDegree F z = HypergraphDegree H (i z) := by
        unfold HypergraphDegree
        apply Finset.card_bij (fun e _ => b.symm e)
        · intro e he
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hinc] using he
        · intro e he g hg heq; exact b.symm.injective heq
        · intro e he
          refine ⟨b e, ?_, b.symm_apply_apply e⟩
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hinc,
            b.symm_apply_apply] using he
      rw [hdeg]
      exact hH.2.2 _
  have hadj (e g : E) : (LineGraphOfHypergraph H).Adj e g ↔
      (LineGraphOfHypergraph F).Adj (b e) (b g) := by
    change (e ≠ g ∧ _) ↔ (b e ≠ b g ∧ _)
    rw [← Finset.card_pos, ← Finset.card_pos, hinter]
    simp only [b.symm_apply_apply, ne_eq, b.injective.eq_iff]
  refine ⟨U, W, inferInstance, inferInstance, inferInstance, inferInstance, F, b f, hclass, ?_⟩
  apply LocalBParameterNeighborhoodEmbeddingTransport
    (LineGraphOfHypergraph H) (LineGraphOfHypergraph F) M f (b f) b.toEmbedding
  · intro e he
    rw [SimpleGraph.mem_neighborFinset] at he ⊢
    exact (hadj f e).mp he
  · intro e he
    refine ⟨b.symm e, ?_, b.apply_symm_apply e⟩
    rw [SimpleGraph.mem_neighborFinset] at he ⊢
    apply (hadj f (b.symm e)).mpr
    simpa using he
  · intro e he g hg
    exact hadj e g
