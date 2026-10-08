import Tablet.IndependentTripleCount
import Tablet.KUniformSplitEdgeHypergraph
import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: KUniformSplitEdgeIndependentTripleLowerBound]
theorem KUniformSplitEdgeIndependentTripleLowerBound :
    ∀ k : ℕ, ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E, ∀ f g : E, ∀ u v : V,
        [DecidableRel (LineGraphOfHypergraph H).Adj] →
        g ≠ f → u ≠ v → u ∈ H.edge f → u ∈ H.edge g →
          ∀ hv : v ∈ H.edge g, ∀ x1 : Fin (k - 1),
            [DecidableRel
              (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1)).Adj] →
            IndependentTripleCount (LineGraphOfHypergraph H) f ≤
              IndependentTripleCount
                (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1))
                (Sum.inl f) := by
-- BODY
  classical
  intro k V E _ _ _ H f g u v _ hgf huv huf hug hv x1 _
  let Hsplit : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
    KUniformSplitEdgeHypergraph k H g v hv x1
  let G := LineGraphOfHypergraph H
  let Gsplit := LineGraphOfHypergraph Hsplit
  let oldTriples : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter (fun S =>
      S.card = 3 ∧ S ⊆ G.neighborFinset f ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
  let splitTriples : Finset (Finset (E ⊕ Unit)) :=
    (Finset.univ : Finset (Finset (E ⊕ Unit))).filter (fun S =>
      S.card = 3 ∧ S ⊆ Gsplit.neighborFinset (Sum.inl f) ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ Gsplit.Adj x y)
  let oldToSplit : Finset E → Finset (E ⊕ Unit) :=
    fun S => S.image (Sum.inl : E → E ⊕ Unit)
  have hfg : f ≠ g := hgf.symm
  have hf_edge :
      Hsplit.edge (Sum.inl f) = Finset.image Sum.inl (H.edge f) := by
    simp [Hsplit, KUniformSplitEdgeHypergraph, hfg]
  have hg_split_meets_f :
      (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge (Sum.inl g)).Nonempty := by
    refine ⟨Sum.inl u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [hf_edge]
      exact Finset.mem_image.mpr ⟨u, huf, rfl⟩
    · simp [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase, hug, huv]
  have himage_nonempty_imp (a b : E) :
      (Hsplit.edge (Sum.inl a) ∩ Hsplit.edge (Sum.inl b)).Nonempty →
        (H.edge a ∩ H.edge b).Nonempty := by
    intro h
    rcases h with ⟨x, hx⟩
    rcases Finset.mem_inter.mp hx with ⟨hxa, hxb⟩
    by_cases hag : a = g
    · subst a
      by_cases hbg : b = g
      · subst b
        exact ⟨v, Finset.mem_inter.mpr ⟨hv, hv⟩⟩
      · have hb_edge :
            Hsplit.edge (Sum.inl b) = Finset.image Sum.inl (H.edge b) := by
          simp [Hsplit, KUniformSplitEdgeHypergraph, hbg]
        rw [hb_edge] at hxb
        rcases Finset.mem_image.mp hxb with ⟨w, hwb, rfl⟩
        have hwg : w ∈ H.edge g := by
          have htmp : ¬ w = v ∧ w ∈ H.edge g := by
            simpa [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase] using hxa
          exact htmp.2
        exact ⟨w, Finset.mem_inter.mpr ⟨hwg, hwb⟩⟩
    · have ha_edge :
          Hsplit.edge (Sum.inl a) = Finset.image Sum.inl (H.edge a) := by
        simp [Hsplit, KUniformSplitEdgeHypergraph, hag]
      rw [ha_edge] at hxa
      rcases Finset.mem_image.mp hxa with ⟨w, hwa, rfl⟩
      by_cases hbg : b = g
      · subst b
        have hwg : w ∈ H.edge g := by
          have htmp : ¬ w = v ∧ w ∈ H.edge g := by
            simpa [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase] using hxb
          exact htmp.2
        exact ⟨w, Finset.mem_inter.mpr ⟨hwa, hwg⟩⟩
      · have hb_edge :
            Hsplit.edge (Sum.inl b) = Finset.image Sum.inl (H.edge b) := by
          simp [Hsplit, KUniformSplitEdgeHypergraph, hbg]
        rw [hb_edge] at hxb
        rcases Finset.mem_image.mp hxb with ⟨z, hzb, hz⟩
        cases hz
        exact ⟨w, Finset.mem_inter.mpr ⟨hwa, hzb⟩⟩
  have hneighbor_map (old : E) :
      G.Adj f old → Gsplit.Adj (Sum.inl f) (Sum.inl old) := by
    intro hold
    rcases hold with ⟨hfo, hmeet⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hfo (Sum.inl_injective h)
    · by_cases hog : old = g
      · subst old
        exact hg_split_meets_f
      · rcases hmeet with ⟨w, hw⟩
        rcases Finset.mem_inter.mp hw with ⟨hwf, hwo⟩
        refine ⟨Sum.inl w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · rw [hf_edge]
          exact Finset.mem_image.mpr ⟨w, hwf, rfl⟩
        · have hold_edge :
              Hsplit.edge (Sum.inl old) = Finset.image Sum.inl (H.edge old) := by
            simp [Hsplit, KUniformSplitEdgeHypergraph, hog]
          rw [hold_edge]
          exact Finset.mem_image.mpr ⟨w, hwo, rfl⟩
  have hadj_imp (a b : E) :
      Gsplit.Adj (Sum.inl a) (Sum.inl b) → G.Adj a b := by
    intro h
    rcases h with ⟨hne, hmeet⟩
    exact ⟨fun hab => hne (by simp [hab]), himage_nonempty_imp a b hmeet⟩
  have hmap (S : Finset E) (hS : S ∈ oldTriples) : oldToSplit S ∈ splitTriples := by
    simp only [oldTriples, splitTriples, Finset.mem_filter] at hS ⊢
    rcases hS with ⟨_, hcard, hsub, hind⟩
    refine ⟨by simp, ?_⟩
    constructor
    · dsimp [oldToSplit]
      rw [Finset.card_image_of_injective _ Sum.inl_injective, hcard]
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, heS, rfl⟩
      have he_neigh := hsub heS
      simpa [SimpleGraph.mem_neighborFinset, Gsplit] using hneighbor_map e
        (by simpa [SimpleGraph.mem_neighborFinset, G] using he_neigh)
    · intro x hx y hy hxy hAdj
      rcases Finset.mem_image.mp hx with ⟨xold, hxold, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨yold, hyold, hy_eq⟩
      cases hy_eq
      have hxyold : xold ≠ yold := by
        intro h
        apply hxy
        simp [h]
      apply hind hxold hyold hxyold
      exact hadj_imp xold yold hAdj
  have hinj : Set.InjOn oldToSplit (↑oldTriples : Set (Finset E)) := by
    intro S _ T _ hST
    ext e
    have := congrArg (fun U : Finset (E ⊕ Unit) => Sum.inl e ∈ U) hST
    simpa [oldToSplit] using this
  have hcard : oldTriples.card ≤ splitTriples.card :=
    Finset.card_le_card_of_injOn oldToSplit hmap hinj
  simpa [IndependentTripleCount, G, Gsplit, oldTriples, splitTriples] using hcard
