import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.KUniformKSimpleBoundedLocalPattern
import Tablet.KUniformKSimpleLocalTruncationPreservesBParameter
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.UniformHypergraph

universe u v

-- [TABLET NODE: KUniformKSimpleLocalPatternTransportToBounded]
theorem KUniformKSimpleLocalPatternTransportToBounded :
    ∀ k : ℕ, 0 < k → ∀ D : ℕ, 0 < D →
      ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) k k D →
          ∀ e : E,
            ∃ P : KUniformKSimpleBoundedLocalPattern k D,
              @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                  (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e
                ≤
              @LocalBParameter (Fin (1 + k * (D - 1))) _ _
                  (LineGraphOfHypergraph
                    ({ edge := P.1.1 } :
                      MultiHypergraph
                        (Fin (k + k * k * (D - 1)))
                        (Fin (1 + k * (D - 1)))))
                  (Classical.decRel
                    (LineGraphOfHypergraph
                      ({ edge := P.1.1 } :
                        MultiHypergraph
                          (Fin (k + k * k * (D - 1)))
                          (Fin (1 + k * (D - 1))))).Adj)
                  (k * D) P.1.2 := by
-- BODY
  classical
  intro k hk D hD V E instFintypeE instDecidableEqE instDecidableEqV H hH e
  obtain ⟨Vloc, Eloc, instFintypeEloc, instDecidableEqEloc, instDecidableEqVloc,
      F, f, edgeEquiv, vertexEquiv, hedge_f, hmem, hF, hscore⟩ :=
    KUniformKSimpleLocalTruncationPreservesBParameter
      k hk D hD H hH e
  letI : Fintype Eloc := instFintypeEloc
  letI : DecidableEq Eloc := instDecidableEqEloc
  letI : DecidableEq Vloc := instDecidableEqVloc
  have hAdj_of_ne : ∀ a : Eloc, a ≠ f → (LineGraphOfHypergraph F).Adj a f := by
    intro a haf
    have ha_or : (edgeEquiv a).1 = e ∨ (LineGraphOfHypergraph H).Adj (edgeEquiv a).1 e :=
      (edgeEquiv a).2
    have hnot_e : (edgeEquiv a).1 ≠ e := by
      intro hval
      apply haf
      apply edgeEquiv.injective
      rw [hedge_f]
      exact Subtype.ext hval
    rcases ha_or with ha_e | ha_adj
    · exact False.elim (hnot_e ha_e)
    · have ha_retained :
          (edgeEquiv a).1 = e ∨ (LineGraphOfHypergraph H).Adj (edgeEquiv a).1 e :=
        Or.inr ha_adj
      rcases ha_adj with ⟨_hne, hnonempty⟩
      refine ⟨?_, ?_⟩
      · intro h_eq
        exact haf h_eq
      · rcases hnonempty with ⟨x, hx⟩
        have hxmem := Finset.mem_inter.mp hx
        let y : Vloc := vertexEquiv.symm
          ⟨x, ⟨(edgeEquiv a).1, ha_retained, hxmem.1⟩⟩
        refine ⟨y, Finset.mem_inter.mpr ?_⟩
        constructor
        · exact (hmem a y).mpr (by simp [y, hxmem.1])
        · have hy : (vertexEquiv y).1 ∈ H.edge (edgeEquiv f).1 := by
            simpa [y, hedge_f] using hxmem.2
          exact (hmem f y).mpr hy
  have hEdgeBound : Fintype.card Eloc ≤ 1 + k * (D - 1) := by
    rcases hF with ⟨hUniformF, _hSimpleF, hMaxDegreeF⟩
    let fibers : Vloc → Finset Eloc :=
      fun x => ((Finset.univ : Finset Eloc).erase f).filter (fun a => x ∈ F.edge a)
    have hcover :
        (Finset.univ : Finset Eloc).erase f ⊆ (F.edge f).biUnion fibers := by
      intro a ha
      have haf : a ≠ f := (Finset.mem_erase.mp ha).1
      have hadj : (LineGraphOfHypergraph F).Adj a f := hAdj_of_ne a haf
      rcases hadj.2 with ⟨x, hx⟩
      have hxmem := Finset.mem_inter.mp hx
      exact Finset.mem_biUnion.mpr ⟨x, hxmem.2, by
        simp [fibers, ha, hxmem.1]⟩
    have hfiber (x : Vloc) (hx : x ∈ F.edge f) : (fibers x).card ≤ D - 1 := by
      have hf_mem : f ∈ (Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a) := by
        simp [hx]
      have hdegree_eq :
          ((Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a)).card =
            HypergraphDegree F x := by
        simp [HypergraphDegree]
      have herase_filter :
          fibers x =
            ((Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a)).erase f := by
        ext a
        by_cases hax : x ∈ F.edge a <;> by_cases haf : a = f <;> simp [fibers, hax, haf]
      calc
        (fibers x).card =
            (((Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a)).erase f).card := by
              rw [herase_filter]
        _ = ((Finset.univ : Finset Eloc).filter (fun a => x ∈ F.edge a)).card - 1 := by
              exact Finset.card_erase_of_mem hf_mem
        _ = HypergraphDegree F x - 1 := by rw [hdegree_eq]
        _ ≤ D - 1 := Nat.sub_le_sub_right (hMaxDegreeF x) 1
    have herase_le : ((Finset.univ : Finset Eloc).erase f).card ≤ k * (D - 1) := by
      calc
        ((Finset.univ : Finset Eloc).erase f).card
            ≤ ((F.edge f).biUnion fibers).card := Finset.card_le_card hcover
        _ ≤ (F.edge f).card * (D - 1) :=
            Finset.card_biUnion_le_card_mul (F.edge f) fibers (D - 1) hfiber
        _ = k * (D - 1) := by rw [hUniformF f]
    have hcard_univ :
        Fintype.card Eloc = ((Finset.univ : Finset Eloc).erase f).card + 1 := by
      have hf_univ : f ∈ (Finset.univ : Finset Eloc) := Finset.mem_univ f
      simpa using (Finset.card_erase_add_one hf_univ).symm
    omega
  have hRetainedVertexBound :
      ((Finset.univ : Finset Eloc).biUnion (fun a => F.edge a)).card ≤
        k + k * k * (D - 1) := by
    rcases hF with ⟨hUniformF, _hSimpleF, _hMaxDegreeF⟩
    calc
      ((Finset.univ : Finset Eloc).biUnion (fun a => F.edge a)).card
          ≤ (Finset.univ : Finset Eloc).card * k :=
          Finset.card_biUnion_le_card_mul (Finset.univ : Finset Eloc) (fun a => F.edge a) k
            (by intro a _ha; exact le_of_eq (hUniformF a))
      _ = Fintype.card Eloc * k := by simp
      _ ≤ (1 + k * (D - 1)) * k := Nat.mul_le_mul_right k hEdgeBound
      _ = k + k * k * (D - 1) := by ring
  have hBoundedTransport :
      ∃ P : KUniformKSimpleBoundedLocalPattern k D,
        @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f
          ≤
        @LocalBParameter (Fin (1 + k * (D - 1))) _ _
            (LineGraphOfHypergraph
              ({ edge := P.1.1 } :
                MultiHypergraph
                  (Fin (k + k * k * (D - 1)))
                  (Fin (1 + k * (D - 1)))))
            (Classical.decRel
              (LineGraphOfHypergraph
                ({ edge := P.1.1 } :
                  MultiHypergraph
                    (Fin (k + k * k * (D - 1)))
                    (Fin (1 + k * (D - 1))))).Adj)
            (k * D) P.1.2 := by
    let edgeBound : ℕ := 1 + k * (D - 1)
    let vertexBound : ℕ := k + k * k * (D - 1)
    obtain ⟨edgeEmb⟩ :
        Nonempty (Eloc ↪ Fin edgeBound) :=
      Function.Embedding.nonempty_of_card_le (by
        simpa [edgeBound] using hEdgeBound)
    let U : Finset Vloc := (Finset.univ : Finset Eloc).biUnion (fun a => F.edge a)
    have hU_card_le_mul : U.card ≤ Fintype.card Eloc * k := by
      rcases hF with ⟨hUniformF, _hSimpleF, _hMaxDegreeF⟩
      calc
        U.card ≤ (Finset.univ : Finset Eloc).card * k :=
          Finset.card_biUnion_le_card_mul (Finset.univ : Finset Eloc) (fun a => F.edge a) k
            (by intro a _ha; exact le_of_eq (hUniformF a))
        _ = Fintype.card Eloc * k := by simp
    have hU_card_bound : U.card ≤ vertexBound := by
      simpa [U, vertexBound] using hRetainedVertexBound
    obtain ⟨vertEmb⟩ :
        Nonempty ({x : Vloc // x ∈ U} ↪ Fin vertexBound) :=
      Function.Embedding.nonempty_of_card_le (by
        have hcard : Fintype.card {x : Vloc // x ∈ U} ≤ vertexBound := by
          rwa [Fintype.card_coe]
        simpa using hcard)
    let usedEdgeLabels : Finset (Fin edgeBound) :=
      (Finset.univ : Finset Eloc).image (fun a => edgeEmb a)
    let unusedEdgeLabels : Finset (Fin edgeBound) :=
      (Finset.univ : Finset (Fin edgeBound)) \ usedEdgeLabels
    let usedVertices : Finset (Fin vertexBound) :=
      (Finset.univ : Finset {x : Vloc // x ∈ U}).image (fun x => vertEmb x)
    let unusedVertices : Finset (Fin vertexBound) :=
      (Finset.univ : Finset (Fin vertexBound)) \ usedVertices
    have hUsedEdgeLabels_card : usedEdgeLabels.card = Fintype.card Eloc := by
      dsimp [usedEdgeLabels]
      simp only [Fintype.card, Finset.card_image_iff]
      intro a _ha b _hb h
      exact edgeEmb.injective h
    have hUnusedEdgeLabels_card :
        unusedEdgeLabels.card = edgeBound - Fintype.card Eloc := by
      dsimp [unusedEdgeLabels]
      rw [Finset.card_sdiff]
      simp [hUsedEdgeLabels_card]
    have hUsedVertices_card : usedVertices.card = U.card := by
      dsimp [usedVertices]
      calc
        ((Finset.univ : Finset {x : Vloc // x ∈ U}).image (fun x => vertEmb x)).card =
            (Finset.univ : Finset {x : Vloc // x ∈ U}).card := by
          exact Finset.card_image_of_injOn (by
            intro a _ha b _hb h
            exact vertEmb.injective h)
        _ = U.card := by simp
    have hUnusedVertices_card :
        unusedVertices.card = vertexBound - U.card := by
      dsimp [unusedVertices]
      rw [Finset.card_sdiff]
      simp [hUsedVertices_card]
    have hVertexBound_eq : vertexBound = k * edgeBound := by
      simp [vertexBound, edgeBound]
      ring
    have hPaddingCapacity :
        Fintype.card ({a : Fin edgeBound // a ∈ unusedEdgeLabels} × Fin k) ≤
          unusedVertices.card := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
        hUnusedVertices_card, hUnusedEdgeLabels_card, hVertexBound_eq]
      exact (by
        calc
          (edgeBound - Fintype.card Eloc) * k =
              k * (edgeBound - Fintype.card Eloc) := by ring
          _ ≤ k * edgeBound - U.card := by
            have hU' : U.card ≤ k * Fintype.card Eloc := by
              simpa [Nat.mul_comm] using hU_card_le_mul
            calc
              k * (edgeBound - Fintype.card Eloc) =
                  k * edgeBound - k * Fintype.card Eloc := by
                    rw [Nat.mul_sub_left_distrib]
              _ ≤ k * edgeBound - U.card :=
                    Nat.sub_le_sub_left hU' (k * edgeBound))
    obtain ⟨padEmb⟩ :
        Nonempty
          (({a : Fin edgeBound // a ∈ unusedEdgeLabels} × Fin k) ↪
            {x : Fin vertexBound // x ∈ unusedVertices}) :=
      Function.Embedding.nonempty_of_card_le (by
        simpa [Fintype.card_coe] using hPaddingCapacity)
    let edgePreimage (b : Fin edgeBound) (hb : b ∈ usedEdgeLabels) : Eloc :=
      Classical.choose (by
        have hb' := Finset.mem_image.mp hb
        rcases hb' with ⟨a, _ha, ha⟩
        exact ⟨a, ha⟩)
    have edgePreimage_spec (b : Fin edgeBound) (hb : b ∈ usedEdgeLabels) :
        edgeEmb (edgePreimage b hb) = b := by
      dsimp [edgePreimage]
      exact Classical.choose_spec (by
        have hb' := Finset.mem_image.mp hb
        rcases hb' with ⟨a, _ha, ha⟩
        exact ⟨a, ha⟩)
    let copiedEdge (a : Eloc) : Finset (Fin vertexBound) :=
      (F.edge a).attach.image (fun x =>
        vertEmb ⟨x.1, by
          dsimp [U]
          exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, x.2⟩⟩)
    let paddedEdge (b : Fin edgeBound) (hb : b ∈ unusedEdgeLabels) :
        Finset (Fin vertexBound) :=
      (Finset.univ : Finset (Fin k)).image (fun i => (padEmb (⟨b, hb⟩, i)).1)
    let PEdge : Fin edgeBound → Finset (Fin vertexBound) :=
      fun b =>
        if hb : b ∈ usedEdgeLabels then
          copiedEdge (edgePreimage b hb)
        else
          paddedEdge b (by
            dsimp [unusedEdgeLabels]
            simp [hb])
    have hPEdge_used (a : Eloc) :
        PEdge (edgeEmb a) = copiedEdge a := by
      have hused : edgeEmb a ∈ usedEdgeLabels := by
        dsimp [usedEdgeLabels]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      dsimp [PEdge]
      rw [dif_pos hused]
      apply congrArg copiedEdge
      exact edgeEmb.injective (edgePreimage_spec (edgeEmb a) hused)
    have hCopiedEdge_card (a : Eloc) : (copiedEdge a).card = k := by
      rcases hF with ⟨hUniformF, _hSimpleF, _hMaxDegreeF⟩
      dsimp [copiedEdge]
      rw [Finset.card_image_of_injOn]
      · simp [hUniformF a]
      · intro x _hx y _hy hxy
        apply Subtype.ext
        have hsub :
            (⟨x.1, by
              dsimp [U]
              exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, x.2⟩⟩ :
                {x : Vloc // x ∈ U}) =
              ⟨y.1, by
                dsimp [U]
                exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, y.2⟩⟩ := by
          exact vertEmb.injective hxy
        exact congrArg (fun z : {x : Vloc // x ∈ U} => z.1) hsub
    have hPaddedEdge_card (b : Fin edgeBound) (hb : b ∈ unusedEdgeLabels) :
        (paddedEdge b hb).card = k := by
      dsimp [paddedEdge]
      rw [Finset.card_image_of_injOn]
      · simp
      · intro i _hi j _hj hij
        have hsub :
            padEmb (⟨b, hb⟩, i) = padEmb (⟨b, hb⟩, j) := by
          apply Subtype.ext
          exact hij
        have hp := padEmb.injective hsub
        exact Prod.ext_iff.mp hp |>.2
    have hPEdge_uniform : UniformHypergraph ({ edge := PEdge } :
        MultiHypergraph (Fin vertexBound) (Fin edgeBound)) k := by
      intro b
      dsimp [PEdge]
      by_cases hb : b ∈ usedEdgeLabels
      · rw [dif_pos hb]
        exact hCopiedEdge_card (edgePreimage b hb)
      · rw [dif_neg hb]
        exact hPaddedEdge_card b (by
          dsimp [unusedEdgeLabels]
          simp [hb])
    have hPEdge_simple : TSimpleHypergraph ({ edge := PEdge } :
        MultiHypergraph (Fin vertexBound) (Fin edgeBound)) k := by
      intro b c _hne
      calc
        ((PEdge b) ∩ (PEdge c)).card ≤ (PEdge b).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = k := hPEdge_uniform b
    have hCopied_subset_used (a : Eloc) :
        copiedEdge a ⊆ usedVertices := by
      intro y hy
      dsimp [copiedEdge] at hy
      rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
      dsimp [usedVertices]
      exact Finset.mem_image.mpr ⟨
        (⟨x.1, by
          dsimp [U]
          exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, x.2⟩⟩ :
          {x : Vloc // x ∈ U}), Finset.mem_univ _, rfl⟩
    have hPadded_subset_unused (b : Fin edgeBound) (hb : b ∈ unusedEdgeLabels) :
        paddedEdge b hb ⊆ unusedVertices := by
      intro y hy
      dsimp [paddedEdge] at hy
      rcases Finset.mem_image.mp hy with ⟨i, _hi, rfl⟩
      exact (padEmb (⟨b, hb⟩, i)).2
    have hPEdge_max : MaxDegreeAtMost ({ edge := PEdge } :
        MultiHypergraph (Fin vertexBound) (Fin edgeBound)) D := by
      intro y
      dsimp [HypergraphDegree]
      let incident : Finset (Fin edgeBound) :=
        (Finset.univ : Finset (Fin edgeBound)).filter (fun b => y ∈ PEdge b)
      change incident.card ≤ D
      by_cases hy : y ∈ usedVertices
      · have hy' :
            y ∈ (Finset.univ : Finset {x : Vloc // x ∈ U}).image
              (fun x => vertEmb x) := by
          change y ∈ (Finset.univ : Finset {x : Vloc // x ∈ U}).image
            (fun x => vertEmb x) at hy
          exact hy
        rcases Finset.mem_image.mp hy' with ⟨x, _hx, hx⟩
        let localIncident : Finset Eloc :=
          (Finset.univ : Finset Eloc).filter (fun a => x.1 ∈ F.edge a)
        let toLocal (b : Fin edgeBound) : Eloc :=
          if hb : b ∈ usedEdgeLabels then edgePreimage b hb else f
        have hIncident_used {b : Fin edgeBound} (hbinc : b ∈ incident) :
            b ∈ usedEdgeLabels := by
          have hbmem : y ∈ PEdge b := (Finset.mem_filter.mp hbinc).2
          by_contra hbused
          have hbunused : b ∈ unusedEdgeLabels := by
            dsimp [unusedEdgeLabels]
            simp [hbused]
          have hypad : y ∈ paddedEdge b hbunused := by
            dsimp [PEdge] at hbmem
            simpa [hbused] using hbmem
          have hyunused : y ∈ unusedVertices := hPadded_subset_unused b hbunused hypad
          have hynot : y ∉ usedVertices := by
            simpa [unusedVertices] using hyunused
          exact hynot hy
        have hMaps : Set.MapsTo toLocal ↑incident ↑localIncident := by
          intro b hbinc
          have hbused : b ∈ usedEdgeLabels := hIncident_used hbinc
          have hbmem : y ∈ PEdge b := (Finset.mem_filter.mp hbinc).2
          have hcopy : y ∈ copiedEdge (edgePreimage b hbused) := by
            dsimp [PEdge] at hbmem
            simpa [hbused] using hbmem
          dsimp [copiedEdge] at hcopy
          rcases Finset.mem_image.mp hcopy with ⟨z, _hz, hz⟩
          have hsub :
              (⟨z.1, by
                dsimp [U]
                exact Finset.mem_biUnion.mpr
                  ⟨edgePreimage b hbused, Finset.mem_univ _, z.2⟩⟩ :
                  {x : Vloc // x ∈ U}) = x := by
            apply vertEmb.injective
            exact hz.trans hx.symm
          have hxedge : x.1 ∈ F.edge (edgePreimage b hbused) := by
            simpa using congrArg (fun w : {x : Vloc // x ∈ U} => w.1) hsub.symm ▸ z.2
          dsimp [toLocal, localIncident]
          simp [hbused, hxedge]
        have hInj : Set.InjOn toLocal ↑incident := by
          intro b hbinc c hcinc hbc
          have hbused : b ∈ usedEdgeLabels := hIncident_used hbinc
          have hcused : c ∈ usedEdgeLabels := hIncident_used hcinc
          dsimp [toLocal] at hbc
          rw [dif_pos hbused, dif_pos hcused] at hbc
          calc
            b = edgeEmb (edgePreimage b hbused) := (edgePreimage_spec b hbused).symm
            _ = edgeEmb (edgePreimage c hcused) := by rw [hbc]
            _ = c := edgePreimage_spec c hcused
        have hcard :
            incident.card ≤ localIncident.card :=
          Finset.card_le_card_of_injOn toLocal hMaps hInj
        have hlocal : localIncident.card = HypergraphDegree F x.1 := by
          simp [localIncident, HypergraphDegree]
        rcases hF with ⟨_hUniformF, _hSimpleF, hMaxDegreeF⟩
        calc
          incident.card ≤ localIncident.card := hcard
          _ = HypergraphDegree F x.1 := hlocal
          _ ≤ D := hMaxDegreeF x.1
      · have hcard_one : incident.card ≤ 1 := by
          rw [Finset.card_le_one_iff]
          intro b c hbinc hcinc
          have hbmem : y ∈ PEdge b := (Finset.mem_filter.mp hbinc).2
          have hcmem : y ∈ PEdge c := (Finset.mem_filter.mp hcinc).2
          have hbnotused : ¬ b ∈ usedEdgeLabels := by
            intro hbused
            have hcopy : y ∈ copiedEdge (edgePreimage b hbused) := by
              dsimp [PEdge] at hbmem
              simpa [hbused] using hbmem
            exact hy (hCopied_subset_used (edgePreimage b hbused) hcopy)
          have hcnotused : ¬ c ∈ usedEdgeLabels := by
            intro hcused
            have hcopy : y ∈ copiedEdge (edgePreimage c hcused) := by
              dsimp [PEdge] at hcmem
              simpa [hcused] using hcmem
            exact hy (hCopied_subset_used (edgePreimage c hcused) hcopy)
          have hbunused : b ∈ unusedEdgeLabels := by
            dsimp [unusedEdgeLabels]
            simp [hbnotused]
          have hcunused : c ∈ unusedEdgeLabels := by
            dsimp [unusedEdgeLabels]
            simp [hcnotused]
          have hbpad : y ∈ paddedEdge b hbunused := by
            dsimp [PEdge] at hbmem
            simpa [hbnotused] using hbmem
          have hcpad : y ∈ paddedEdge c hcunused := by
            dsimp [PEdge] at hcmem
            simpa [hcnotused] using hcmem
          dsimp [paddedEdge] at hbpad hcpad
          rcases Finset.mem_image.mp hbpad with ⟨i, _hi, hi⟩
          rcases Finset.mem_image.mp hcpad with ⟨j, _hj, hj⟩
          have hpad :
              padEmb (⟨b, hbunused⟩, i) = padEmb (⟨c, hcunused⟩, j) := by
            apply Subtype.ext
            exact hi.trans hj.symm
          have hprod := padEmb.injective hpad
          exact congrArg (fun p :
            {a : Fin edgeBound // a ∈ unusedEdgeLabels} × Fin k => p.1.1) hprod
        exact le_trans hcard_one (Nat.succ_le_iff.mpr hD)
    let P : KUniformKSimpleBoundedLocalPattern k D :=
      ⟨⟨PEdge, edgeEmb f⟩, ⟨hPEdge_uniform, hPEdge_simple, hPEdge_max⟩⟩
    let G : SimpleGraph Eloc := LineGraphOfHypergraph F
    let GP : SimpleGraph (Fin edgeBound) :=
      LineGraphOfHypergraph ({ edge := PEdge } : MultiHypergraph (Fin vertexBound) (Fin edgeBound))
    have hCopied_inter_nonempty_of_adj {a b : Eloc} (hab : G.Adj a b) :
        (copiedEdge a ∩ copiedEdge b).Nonempty := by
      rcases hab with ⟨_hne, hnonempty⟩
      rcases hnonempty with ⟨x, hx⟩
      have hxmem := Finset.mem_inter.mp hx
      refine ⟨vertEmb ⟨x, by
        dsimp [U]
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hxmem.1⟩⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨
        Finset.mem_image.mpr ⟨⟨x, hxmem.1⟩, by simp, rfl⟩,
        Finset.mem_image.mpr ⟨⟨x, hxmem.2⟩, by simp, rfl⟩⟩
    have hAdj_copied (a b : Eloc) :
        G.Adj a b ↔ GP.Adj (edgeEmb a) (edgeEmb b) := by
      constructor
      · intro hab
        refine ⟨?_, ?_⟩
        · intro h
          exact hab.1 (edgeEmb.injective h)
        · change (PEdge (edgeEmb a) ∩ PEdge (edgeEmb b)).Nonempty
          rw [hPEdge_used a, hPEdge_used b]
          exact hCopied_inter_nonempty_of_adj hab
      · intro hab
        rcases hab with ⟨hne, hnonempty⟩
        refine ⟨?_, ?_⟩
        · intro h
          exact hne (by rw [h])
        · change (PEdge (edgeEmb a) ∩ PEdge (edgeEmb b)).Nonempty at hnonempty
          rw [hPEdge_used a, hPEdge_used b] at hnonempty
          rcases hnonempty with ⟨y, hy⟩
          have hymem := Finset.mem_inter.mp hy
          dsimp [copiedEdge] at hymem
          rcases Finset.mem_image.mp hymem.1 with ⟨x, _hx, hxy⟩
          rcases Finset.mem_image.mp hymem.2 with ⟨z, _hz, hzy⟩
          have hxz_sub :
              (⟨x.1, by
                dsimp [U]
                exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, x.2⟩⟩ :
                  {x : Vloc // x ∈ U}) =
              ⟨z.1, by
                dsimp [U]
                exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, z.2⟩⟩ := by
            apply vertEmb.injective
            exact hxy.trans hzy.symm
          have hxz : x.1 = z.1 := congrArg (fun t : {x : Vloc // x ∈ U} => t.1) hxz_sub
          refine ⟨x.1, Finset.mem_inter.mpr ⟨x.2, ?_⟩⟩
          simpa [hxz] using z.2
    have hmap :
        ∀ x : Eloc, x ∈ G.neighborFinset f → edgeEmb x ∈ GP.neighborFinset (edgeEmb f) := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx ⊢
      exact (hAdj_copied f x).mp hx
    have hsurj :
        ∀ y : Fin edgeBound, y ∈ GP.neighborFinset (edgeEmb f) →
          ∃ x : Eloc, x ∈ G.neighborFinset f ∧ edgeEmb x = y := by
      intro y hy
      have hyAdj : GP.Adj (edgeEmb f) y := by
        simpa [SimpleGraph.mem_neighborFinset] using hy
      have hy_used : y ∈ usedEdgeLabels := by
        by_contra hy_not_used
        have hy_unused : y ∈ unusedEdgeLabels := by
          dsimp [unusedEdgeLabels]
          simp [hy_not_used]
        rcases hyAdj with ⟨_hne, hnonempty⟩
        have hleft : PEdge (edgeEmb f) = copiedEdge f := hPEdge_used f
        have hright : PEdge y = paddedEdge y hy_unused := by
          dsimp [PEdge]
          simpa [hy_not_used]
        change (PEdge (edgeEmb f) ∩ PEdge y).Nonempty at hnonempty
        rw [hleft, hright] at hnonempty
        rcases hnonempty with ⟨z, hz⟩
        have hzmem := Finset.mem_inter.mp hz
        have hz_used : z ∈ usedVertices := hCopied_subset_used f hzmem.1
        have hz_unused : z ∈ unusedVertices := hPadded_subset_unused y hy_unused hzmem.2
        have hz_not_used : z ∉ usedVertices := by
          simpa [unusedVertices] using hz_unused
        exact hz_not_used hz_used
      let x : Eloc := edgePreimage y hy_used
      refine ⟨x, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        have hx_adj : GP.Adj (edgeEmb f) (edgeEmb x) := by
          simpa [x, edgePreimage_spec y hy_used] using hyAdj
        exact (hAdj_copied f x).mpr hx_adj
      · exact edgePreimage_spec y hy_used
    have hadj_neighbors :
        ∀ ⦃x : Eloc⦄, x ∈ G.neighborFinset f →
          ∀ ⦃y : Eloc⦄, y ∈ G.neighborFinset f →
            (G.Adj x y ↔ GP.Adj (edgeEmb x) (edgeEmb y)) := by
      intro x _hx y _hy
      exact hAdj_copied x y
    have hlocal_eq :
        @LocalBParameter Eloc _ _ G (Classical.decRel G.Adj) (k * D) f =
        @LocalBParameter (Fin edgeBound) _ _ GP (Classical.decRel GP.Adj) (k * D) (edgeEmb f) :=
      LocalBParameterNeighborhoodEmbeddingTransport G GP (k * D) f (edgeEmb f) edgeEmb
        hmap hsurj hadj_neighbors
    exact ⟨P, le_of_eq hlocal_eq⟩
  obtain ⟨P, hP⟩ := hBoundedTransport
  refine ⟨P, ?_⟩
  exact le_trans (le_of_eq hscore) hP
