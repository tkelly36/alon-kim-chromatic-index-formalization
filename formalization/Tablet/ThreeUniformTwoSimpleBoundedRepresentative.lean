import Tablet.KUniformKSimpleLocalTruncationPreservesBParameter
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport

universe u v

-- [TABLET NODE: ThreeUniformTwoSimpleBoundedRepresentative]
theorem ThreeUniformTwoSimpleBoundedRepresentative
    (D : ℕ) (hD : 0 < D)
    {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) (hH : H ∈ HypergraphClass 3 2 D) (e : E) :
    ∃ (m l : ℕ), m ≤ 1 + 3 * (D - 1) ∧ l ≤ 3 * m ∧
      ∃ (F : MultiHypergraph (Fin l) (Fin m)) (f : Fin m),
        F ∈ HypergraphClass 3 2 D ∧
        @LocalBParameter E _ _ (LineGraphOfHypergraph H)
          (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e =
        @LocalBParameter (Fin m) _ _ (LineGraphOfHypergraph F)
          (Classical.decRel (LineGraphOfHypergraph F).Adj) (3 * D) f := by
-- BODY
  classical
  have hH3 : H ∈ HypergraphClass 3 3 D :=
    ⟨hH.1, fun _ _ h => (hH.2.1 h).trans (by decide), hH.2.2⟩
  obtain ⟨U, A, iA, dA, dU, K, a, ee, ve, hea, hmem, hK, hscore⟩ :=
    KUniformKSimpleLocalTruncationPreservesBParameter 3 (by decide) D hD H hH3 e
  letI : Fintype A := iA
  letI : DecidableEq A := dA
  letI : DecidableEq U := dU
  have hsimple : TSimpleHypergraph K 2 := by
    intro b c hbc
    have hinj : Function.Injective (fun x : U => (ve x).val) :=
      Subtype.val_injective.comp ve.injective
    have hle : (K.edge b ∩ K.edge c).card ≤
        (H.edge (ee b).val ∩ H.edge (ee c).val).card := by
      apply Finset.card_le_card_of_injOn (fun x : U => (ve x).val)
      · intro x hx
        exact Finset.mem_inter.mpr
          ⟨(hmem b x).mp (Finset.mem_inter.mp hx).1,
            (hmem c x).mp (Finset.mem_inter.mp hx).2⟩
      · exact hinj.injOn
    exact hle.trans (hH.2.1 (fun h => hbc (ee.injective (Subtype.ext h))))
  have hadj (b : A) (hb : b ≠ a) : (LineGraphOfHypergraph K).Adj b a := by
    have hne : (ee b).val ≠ e := by
      intro h
      apply hb
      apply ee.injective
      rw [hea]
      exact Subtype.ext h
    have hba := (ee b).property.resolve_left hne
    obtain ⟨x, hx⟩ := hba.2
    let y := ve.symm ⟨x, (ee b).val, (ee b).property, (Finset.mem_inter.mp hx).1⟩
    refine ⟨hb, y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply (hmem b y).mpr
      simpa [y] using (Finset.mem_inter.mp hx).1
    · apply (hmem a y).mpr
      simpa [y, hea] using (Finset.mem_inter.mp hx).2
  have hbound : Fintype.card A ≤ 1 + 3 * (D - 1) := by
    let fibers := fun x : U => (Finset.univ.erase a).filter (fun b => x ∈ K.edge b)
    have hcover : Finset.univ.erase a ⊆ (K.edge a).biUnion fibers := by
      intro b hb
      obtain ⟨x, hx⟩ := (hadj b (Finset.mem_erase.mp hb).1).2
      exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_inter.mp hx).2,
        by simp [fibers, hb, (Finset.mem_inter.mp hx).1]⟩
    have hfiber (x : U) (hx : x ∈ K.edge a) : (fibers x).card ≤ D - 1 := by
      have heq : fibers x = (Finset.univ.filter (fun b => x ∈ K.edge b)).erase a := by
        ext b
        simp [fibers, and_comm]
      rw [heq, Finset.card_erase_of_mem (by simp [hx])]
      exact Nat.sub_le_sub_right (hK.2.2 x) 1
    have hle : (Finset.univ.erase a).card ≤ 3 * (D - 1) := calc
      _ ≤ ((K.edge a).biUnion fibers).card := Finset.card_le_card hcover
      _ ≤ (K.edge a).card * (D - 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ hfiber
      _ = 3 * (D - 1) := by rw [hK.1 a]
    have hc := Finset.card_erase_add_one (Finset.mem_univ a)
    rw [Finset.card_univ] at hc
    omega
  let S : Finset U := Finset.univ.biUnion K.edge
  have hs (b : A) {x : U} (hx : x ∈ K.edge b) : x ∈ S :=
    Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hx⟩
  have hsize : S.card ≤ 3 * Fintype.card A := by
    calc
      S.card ≤ Finset.univ.card * 3 :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => (hK.1 b).le)
      _ = 3 * Fintype.card A := by simp [Nat.mul_comm]
  let bv : Fin S.card ≃ S := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin S).symm
  let be : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let i : Fin S.card ↪ U := bv.toEmbedding.trans (Function.Embedding.subtype _)
  have hisurj {x : U} (hx : x ∈ S) : ∃ z, i z = x :=
    ⟨bv.symm ⟨x, hx⟩, by simp [i]⟩
  let F : MultiHypergraph (Fin S.card) (Fin (Fintype.card A)) :=
    ⟨fun b => Finset.univ.filter (fun z => i z ∈ K.edge (be.symm b))⟩
  have hinc (b : Fin (Fintype.card A)) (z : Fin S.card) :
      z ∈ F.edge b ↔ i z ∈ K.edge (be.symm b) := by simp [F]
  have hcard (b : Fin (Fintype.card A)) :
      (F.edge b).card = (K.edge (be.symm b)).card := by
    apply Finset.card_bij (fun z _ => i z)
    · intro z hz; exact (hinc b z).mp hz
    · intro x hx y hy heq; exact i.injective heq
    · intro x hx
      obtain ⟨z, rfl⟩ := hisurj (hs _ hx)
      exact ⟨z, (hinc b z).mpr hx, rfl⟩
  have hinter (b c : Fin (Fintype.card A)) :
      (F.edge b ∩ F.edge c).card =
        (K.edge (be.symm b) ∩ K.edge (be.symm c)).card := by
    apply Finset.card_bij (fun z _ => i z)
    · intro z hz
      exact Finset.mem_inter.mpr ⟨(hinc b z).mp (Finset.mem_inter.mp hz).1,
        (hinc c z).mp (Finset.mem_inter.mp hz).2⟩
    · intro x hx y hy heq; exact i.injective heq
    · intro x hx
      obtain ⟨z, rfl⟩ := hisurj (hs _ (Finset.mem_inter.mp hx).1)
      exact ⟨z, Finset.mem_inter.mpr
        ⟨(hinc b z).mpr (Finset.mem_inter.mp hx).1,
          (hinc c z).mpr (Finset.mem_inter.mp hx).2⟩, rfl⟩
  have hclass : F ∈ HypergraphClass 3 2 D := by
    refine ⟨fun b => (hcard b).trans (hK.1 _), ?_, ?_⟩
    · intro b c hbc
      rw [hinter]
      exact hsimple (fun h => hbc (be.symm.injective h))
    · intro z
      have hdeg : HypergraphDegree F z = HypergraphDegree K (i z) := by
        unfold HypergraphDegree
        apply Finset.card_bij (fun b _ => be.symm b)
        · intro b hb
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hinc] using hb
        · intro b hb c hc hbc; exact be.symm.injective hbc
        · intro b hb
          refine ⟨be b, ?_, be.symm_apply_apply b⟩
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hinc,
            be.symm_apply_apply] using hb
      rw [hdeg]
      exact hK.2.2 _
  have hadj' (b c : A) : (LineGraphOfHypergraph K).Adj b c ↔
      (LineGraphOfHypergraph F).Adj (be b) (be c) := by
    change (b ≠ c ∧ _) ↔ (be b ≠ be c ∧ _)
    rw [← Finset.card_pos, ← Finset.card_pos, hinter]
    simp only [be.symm_apply_apply, ne_eq, be.injective.eq_iff]
  refine ⟨Fintype.card A, S.card, hbound, hsize, F, be a, hclass, hscore.trans ?_⟩
  apply LocalBParameterNeighborhoodEmbeddingTransport
    (LineGraphOfHypergraph K) (LineGraphOfHypergraph F) (3 * D) a (be a) be.toEmbedding
  · intro b hb
    rw [SimpleGraph.mem_neighborFinset] at hb ⊢
    exact (hadj' a b).mp hb
  · intro b hb
    refine ⟨be.symm b, ?_, be.apply_symm_apply b⟩
    rw [SimpleGraph.mem_neighborFinset] at hb ⊢
    apply (hadj' a (be.symm b)).mpr
    simpa using hb
  · intro b hb c hc
    exact hadj' b c
