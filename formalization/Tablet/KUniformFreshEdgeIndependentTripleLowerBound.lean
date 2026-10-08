import Tablet.IndependentTripleCount
import Tablet.KUniformFreshEdgeHypergraph
import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: KUniformFreshEdgeIndependentTripleLowerBound]
theorem KUniformFreshEdgeIndependentTripleLowerBound {V E : Type*} [Fintype E]
    [DecidableEq E] [DecidableEq V] (k : ℕ) (H : MultiHypergraph V E) (f : E)
    (v : V) [DecidableRel (LineGraphOfHypergraph H).Adj]
    [DecidableRel (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj] :
    IndependentTripleCount (LineGraphOfHypergraph H) f ≤
      IndependentTripleCount
        (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)) (Sum.inl f) := by
-- BODY
  classical
  let G := LineGraphOfHypergraph H
  let Hnew := KUniformFreshEdgeHypergraph k H v
  let Gnew := LineGraphOfHypergraph Hnew
  let oldTriples : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter (fun S =>
      S.card = 3 ∧ S ⊆ G.neighborFinset f ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
  let newTriples : Finset (Finset (E ⊕ Unit)) :=
    (Finset.univ : Finset (Finset (E ⊕ Unit))).filter (fun S =>
      S.card = 3 ∧ S ⊆ Gnew.neighborFinset (Sum.inl f) ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ Gnew.Adj x y)
  have himage_nonempty_old (aold bold : E) :
      (Hnew.edge (Sum.inl aold) ∩ Hnew.edge (Sum.inl bold)).Nonempty ↔
        (H.edge aold ∩ H.edge bold).Nonempty := by
    constructor
    · intro h
      rcases h with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxb⟩
      have hxaimg :
          x ∈ (H.edge aold).image (Sum.inl : V → V ⊕ Fin (k - 1)) := by
        simpa [Hnew, KUniformFreshEdgeHypergraph] using hxa
      have hxbimg :
          x ∈ (H.edge bold).image (Sum.inl : V → V ⊕ Fin (k - 1)) := by
        simpa [Hnew, KUniformFreshEdgeHypergraph] using hxb
      rcases Finset.mem_image.mp hxaimg with ⟨a, haa, rfl⟩
      rcases Finset.mem_image.mp hxbimg with ⟨b, hbb, hb⟩
      cases hb
      exact ⟨a, Finset.mem_inter.mpr ⟨haa, hbb⟩⟩
    · intro h
      rcases h with ⟨a, ha⟩
      rcases Finset.mem_inter.mp ha with ⟨haa, hab⟩
      exact ⟨Sum.inl a, by
        dsimp [Hnew, KUniformFreshEdgeHypergraph]
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨a, haa, rfl⟩,
            Finset.mem_image.mpr ⟨a, hab, rfl⟩⟩⟩
  let oldToNew : Finset E → Finset (E ⊕ Unit) :=
    fun S => S.image (Sum.inl : E → E ⊕ Unit)
  have hmap (S : Finset E) (hS : S ∈ oldTriples) : oldToNew S ∈ newTriples := by
    simp only [oldTriples, newTriples, Finset.mem_filter] at hS ⊢
    rcases hS with ⟨_, hcard, hsub, hind⟩
    refine ⟨by simp, ?_⟩
    constructor
    · dsimp [oldToNew]
      rw [Finset.card_image_of_injective _ Sum.inl_injective, hcard]
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, heS, rfl⟩
      have he_neigh := hsub heS
      rcases (by
          simpa [SimpleGraph.mem_neighborFinset, G, LineGraphOfHypergraph]
            using he_neigh) with ⟨hne, hnonempty⟩
      simp [SimpleGraph.mem_neighborFinset, Gnew, Hnew, LineGraphOfHypergraph]
      exact ⟨by simpa using hne, (himage_nonempty_old f e).mpr hnonempty⟩
    · intro x hx y hy hxy hAdj
      rcases Finset.mem_image.mp hx with ⟨xold, hxold, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨yold, hyold, hy_eq⟩
      cases hy_eq
      have hxyold : xold ≠ yold := by
        intro h
        apply hxy
        simp [h]
      apply hind hxold hyold hxyold
      rcases hAdj with ⟨hne, hnonempty⟩
      exact ⟨by simpa using hne, (himage_nonempty_old xold yold).mp hnonempty⟩
  have hinj : Set.InjOn oldToNew (↑oldTriples : Set (Finset E)) := by
    intro S _ T _ hST
    ext e
    have := congrArg (fun U : Finset (E ⊕ Unit) => Sum.inl e ∈ U) hST
    simpa [oldToNew] using this
  have hcard : oldTriples.card ≤ newTriples.card :=
    Finset.card_le_card_of_injOn oldToNew hmap hinj
  simpa [IndependentTripleCount, G, Gnew, Hnew, oldTriples, newTriples] using hcard
