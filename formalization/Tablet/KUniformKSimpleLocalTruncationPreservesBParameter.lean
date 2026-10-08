import Tablet.HypergraphClass
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

universe u v

-- [TABLET NODE: KUniformKSimpleLocalTruncationPreservesBParameter]
theorem KUniformKSimpleLocalTruncationPreservesBParameter :
    ∀ k : ℕ, 0 < k → ∀ D : ℕ, 0 < D →
      ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) k k D →
          ∀ e : E,
            ∃ (Vloc : Type u) (Eloc : Type v),
              ∃ (_instFintype : Fintype Eloc) (_instDecidableEqE : DecidableEq Eloc)
                (_instDecidableEqV : DecidableEq Vloc),
                ∃ (F : MultiHypergraph Vloc Eloc) (f : Eloc),
                  ∃ (edgeEquiv :
                      Eloc ≃
                        {g : E // g = e ∨ (LineGraphOfHypergraph H).Adj g e})
                    (vertexEquiv :
                      Vloc ≃
                        {x : V //
                          ∃ g : E,
                            (g = e ∨ (LineGraphOfHypergraph H).Adj g e) ∧
                              x ∈ H.edge g}),
                    edgeEquiv f = ⟨e, Or.inl rfl⟩ ∧
                    (∀ a : Eloc, ∀ x : Vloc,
                      x ∈ F.edge a ↔
                        (vertexEquiv x).1 ∈ H.edge (edgeEquiv a).1) ∧
                    F ∈ HypergraphClass (V := Vloc) (E := Eloc) k k D ∧
                    @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                        (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e
                      =
                    @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                        (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f := by
-- BODY
  classical
  intro k hk D hD V E instE instDecE instDecV H hH e
  let G : SimpleGraph E := LineGraphOfHypergraph H
  let retainedEdge : E → Prop := fun g => g = e ∨ G.Adj g e
  let Eloc : Type v := {g : E // retainedEdge g}
  let retainedVertex : V → Prop :=
    fun x => ∃ g : E, retainedEdge g ∧ x ∈ H.edge g
  let Vloc : Type u := {x : V // retainedVertex x}
  let edgeEquiv : Eloc ≃ {g : E // g = e ∨ (LineGraphOfHypergraph H).Adj g e} :=
    Equiv.refl Eloc
  let vertexEquiv :
      Vloc ≃
        {x : V //
          ∃ g : E,
            (g = e ∨ (LineGraphOfHypergraph H).Adj g e) ∧ x ∈ H.edge g} :=
    Equiv.refl Vloc
  let F : MultiHypergraph Vloc Eloc :=
    { edge := fun a => (H.edge a.1).subtype retainedVertex }
  let f : Eloc := ⟨e, Or.inl rfl⟩
  refine ⟨Vloc, Eloc, inferInstance, inferInstance, inferInstance, F, f,
    edgeEquiv, vertexEquiv, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro a x
    exact Finset.mem_subtype
  · rcases hH with ⟨hUniform, _hSimple, hMaxDegree⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a
      change ((H.edge a.1).subtype retainedVertex).card = k
      rw [Finset.card_subtype]
      have hfilter :
          (H.edge a.1).filter retainedVertex = H.edge a.1 := by
        apply Finset.filter_true_of_mem
        intro x hx
        exact ⟨a.1, a.2, hx⟩
      rw [hfilter]
      exact hUniform a.1
    · intro a b hab
      have hcard_a : (F.edge a).card = k := by
        change ((H.edge a.1).subtype retainedVertex).card = k
        rw [Finset.card_subtype]
        have hfilter :
            (H.edge a.1).filter retainedVertex = H.edge a.1 := by
          apply Finset.filter_true_of_mem
          intro x hx
          exact ⟨a.1, a.2, hx⟩
        rw [hfilter]
        exact hUniform a.1
      calc
        ((F.edge a) ∩ (F.edge b)).card ≤ (F.edge a).card :=
          Finset.card_le_card (Finset.inter_subset_left)
        _ = k := hcard_a
    · intro x
      let localIncident : Finset Eloc :=
        (Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a)
      let originalIncident : Finset E :=
        (Finset.univ : Finset E).filter (fun g => x.1 ∈ H.edge g)
      have hmaps : Set.MapsTo (fun a : Eloc => a.1)
          (↑localIncident : Set Eloc) (↑originalIncident : Set E) := by
        intro a ha
        simp only [localIncident, originalIncident, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and] at ha ⊢
        exact Finset.mem_subtype.mp ha
      have hinj : Set.InjOn (fun a : Eloc => a.1) (↑localIncident : Set Eloc) := by
        intro a ha b hb hco
        exact Subtype.ext hco
      have hcard_le :
          localIncident.card ≤ originalIncident.card :=
        Finset.card_le_card_of_injOn (fun a : Eloc => a.1) hmaps hinj
      calc
        HypergraphDegree F x = localIncident.card := by
          simp [HypergraphDegree, localIncident]
        _ ≤ originalIncident.card := hcard_le
        _ = HypergraphDegree H x.1 := by
          simp [HypergraphDegree, originalIncident]
        _ ≤ D := hMaxDegree x.1
  ·
    let GH : SimpleGraph E := LineGraphOfHypergraph H
    let GF : SimpleGraph Eloc := LineGraphOfHypergraph F
    have hAdj_f (a : Eloc) : GF.Adj f a ↔ GH.Adj e a.1 := by
      constructor
      · intro h
        rcases h with ⟨hne, hnonempty⟩
        refine ⟨?_, ?_⟩
        · intro heq
          apply hne
          exact Subtype.ext heq
        · rcases hnonempty with ⟨x, hx⟩
          have hxmem := Finset.mem_inter.mp hx
          exact ⟨x.1, Finset.mem_inter.mpr
            ⟨Finset.mem_subtype.mp hxmem.1, Finset.mem_subtype.mp hxmem.2⟩⟩
      · intro h
        rcases h with ⟨hne, hnonempty⟩
        refine ⟨?_, ?_⟩
        · intro hfeq
          apply hne
          simpa [f] using congrArg Subtype.val hfeq
        · rcases hnonempty with ⟨x, hx⟩
          have hxmem := Finset.mem_inter.mp hx
          let y : Vloc := ⟨x, ⟨e, Or.inl rfl, hxmem.1⟩⟩
          exact ⟨y, Finset.mem_inter.mpr
            ⟨Finset.mem_subtype.mpr hxmem.1, Finset.mem_subtype.mpr hxmem.2⟩⟩
    have hdegree_eq : GH.degree e = GF.degree f := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree GH e,
        ← SimpleGraph.card_neighborFinset_eq_degree GF f]
      refine Finset.card_bij'
        (fun g hg =>
          (⟨g, Or.inr (by
            have hgAdj : GH.Adj e g := (SimpleGraph.mem_neighborFinset GH e g).mp hg
            simpa [GH, G] using hgAdj.symm)⟩ : Eloc))
        (fun a _ha => a.1) ?_ ?_ ?_ ?_
      · intro g hg
        rw [SimpleGraph.mem_neighborFinset]
        apply (hAdj_f _).mpr
        exact (SimpleGraph.mem_neighborFinset GH e g).mp hg
      · intro a ha
        rw [SimpleGraph.mem_neighborFinset]
        exact (hAdj_f a).mp ((SimpleGraph.mem_neighborFinset GF f a).mp ha)
      · intro g hg
        rfl
      · intro a ha
        exact Subtype.ext rfl
    have hAdj_loc (a b : Eloc) : GF.Adj a b ↔ GH.Adj a.1 b.1 := by
      constructor
      · intro h
        rcases h with ⟨hne, hnonempty⟩
        refine ⟨?_, ?_⟩
        · intro hval
          exact hne (Subtype.ext hval)
        · rcases hnonempty with ⟨x, hx⟩
          have hxmem := Finset.mem_inter.mp hx
          exact ⟨x.1, Finset.mem_inter.mpr
            ⟨Finset.mem_subtype.mp hxmem.1, Finset.mem_subtype.mp hxmem.2⟩⟩
      · intro h
        rcases h with ⟨hne, hnonempty⟩
        refine ⟨?_, ?_⟩
        · intro hab
          exact hne (congrArg Subtype.val hab)
        · rcases hnonempty with ⟨x, hx⟩
          have hxmem := Finset.mem_inter.mp hx
          let y : Vloc := ⟨x, ⟨a.1, a.2, hxmem.1⟩⟩
          exact ⟨y, Finset.mem_inter.mpr
            ⟨Finset.mem_subtype.mpr hxmem.1, Finset.mem_subtype.mpr hxmem.2⟩⟩
    have hcount_eq (n : ℕ) :
        ((Finset.univ : Finset (Finset E)).filter (fun S =>
          S.card = n ∧ S ⊆ GH.neighborFinset e ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ GH.Adj x y)).card =
        ((Finset.univ : Finset (Finset Eloc)).filter (fun S =>
          S.card = n ∧ S ⊆ GF.neighborFinset f ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ GF.Adj x y)).card := by
      let AH : Finset (Finset E) :=
        (Finset.univ : Finset (Finset E)).filter (fun S =>
          S.card = n ∧ S ⊆ GH.neighborFinset e ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ GH.Adj x y)
      let AF : Finset (Finset Eloc) :=
        (Finset.univ : Finset (Finset Eloc)).filter (fun S =>
          S.card = n ∧ S ⊆ GF.neighborFinset f ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ GF.Adj x y)
      change AH.card = AF.card
      refine Finset.card_bij'
        (fun S _ => S.subtype retainedEdge)
        (fun S _ => S.image (fun a : Eloc => a.1))
        ?_ ?_ ?_ ?_
      · intro S hS
        dsimp [AH, AF] at hS ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        rcases hS with ⟨hcard, hsub, hind⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [Finset.card_subtype]
          have hfilter : S.filter retainedEdge = S := by
            apply Finset.filter_true_of_mem
            intro g hg
            have hge : GH.Adj e g := (SimpleGraph.mem_neighborFinset GH e g).mp (hsub hg)
            exact Or.inr hge.symm
          rw [hfilter, hcard]
        · intro a ha
          rw [SimpleGraph.mem_neighborFinset]
          apply (hAdj_f a).mpr
          exact (SimpleGraph.mem_neighborFinset GH e a.1).mp
            (hsub (Finset.mem_subtype.mp ha))
        · intro a ha b hb hab
          rw [hAdj_loc a b]
          exact hind (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb)
            (by
              intro hval
              exact hab (Subtype.ext hval))
      · intro S hS
        dsimp [AH, AF] at hS ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        rcases hS with ⟨hcard, hsub, hind⟩
        refine ⟨?_, ?_, ?_⟩
        · have himage : (S.image (fun a : Eloc => a.1)).card = S.card := by
            rw [Finset.card_image_iff]
            intro a ha b hb hval
            exact Subtype.ext hval
          rw [himage, hcard]
        · intro g hg
          rcases Finset.mem_image.mp hg with ⟨a, ha, rfl⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact (hAdj_f a).mp ((SimpleGraph.mem_neighborFinset GF f a).mp (hsub ha))
        · intro g hg h hg' hne
          rcases Finset.mem_image.mp hg with ⟨a, ha, rfl⟩
          rcases Finset.mem_image.mp hg' with ⟨b, hb, rfl⟩
          rw [← hAdj_loc a b]
          exact hind ha hb (by
            intro hab
            exact hne (congrArg Subtype.val hab))
      · intro S hS
        apply Finset.ext
        intro g
        constructor
        · intro hg
          rcases Finset.mem_image.mp hg with ⟨a, ha, hval⟩
          simpa [hval] using (Finset.mem_subtype.mp ha)
        · intro hg
          exact Finset.mem_image.mpr ⟨⟨g, by
            dsimp [AH] at hS
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
            have hge : GH.Adj e g :=
              (SimpleGraph.mem_neighborFinset GH e g).mp (hS.2.1 hg)
            exact Or.inr hge.symm⟩, Finset.mem_subtype.mpr hg, rfl⟩
      · intro S hS
        apply Finset.ext
        intro a
        constructor
        · intro ha
          rcases Finset.mem_subtype.mp ha with haim
          rcases Finset.mem_image.mp haim with ⟨b, hb, hval⟩
          have hab : a = b := Subtype.ext hval.symm
          simpa [hab] using hb
        · intro ha
          exact Finset.mem_subtype.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have hpair_eq :
        IndependentPairCount GH e = IndependentPairCount GF f := by
      unfold IndependentPairCount
      exact hcount_eq 2
    have htriple_eq :
        IndependentTripleCount GH e = IndependentTripleCount GF f := by
      unfold IndependentTripleCount
      exact hcount_eq 3
    unfold LocalBParameter
    rw [hdegree_eq, hpair_eq, htriple_eq]
