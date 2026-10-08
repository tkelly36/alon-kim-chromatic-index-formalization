import Tablet.IndependentPairCount
import Tablet.KUniformFreshEdgeHypergraph
import Tablet.LineGraphOfHypergraph

set_option maxHeartbeats 1200000

-- [TABLET NODE: KUniformFreshEdgeIndependentPairUpperBound]
theorem KUniformFreshEdgeIndependentPairUpperBound {V E : Type*} [Fintype E]
    [DecidableEq E] [DecidableEq V] (k : ℕ) (H : MultiHypergraph V E) (f : E)
    (v : V) [DecidableRel (LineGraphOfHypergraph H).Adj]
    [DecidableRel (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)).Adj] :
    IndependentPairCount
        (LineGraphOfHypergraph (KUniformFreshEdgeHypergraph k H v)) (Sum.inl f) ≤
      IndependentPairCount (LineGraphOfHypergraph H) f +
        ((Finset.univ : Finset E).filter
          (fun e => (LineGraphOfHypergraph H).Adj f e)).card := by
-- BODY
  classical
  let G := LineGraphOfHypergraph H
  let Hnew := KUniformFreshEdgeHypergraph k H v
  let Gnew := LineGraphOfHypergraph Hnew
  let fresh : E ⊕ Unit := Sum.inr ()
  let oldOf : Finset (E ⊕ Unit) → Finset E := fun S =>
    S.preimage Sum.inl (by
      intro x _ y _ hxy
      exact Sum.inl.inj hxy)
  let oldPairs : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter (fun S =>
      S.card = 2 ∧ S ⊆ G.neighborFinset f ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
  let newPairs : Finset (Finset (E ⊕ Unit)) :=
    (Finset.univ : Finset (Finset (E ⊕ Unit))).filter (fun S =>
      S.card = 2 ∧ S ⊆ Gnew.neighborFinset (Sum.inl f) ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ Gnew.Adj x y)
  let A := newPairs.filter (fun S => fresh ∉ S)
  let B := newPairs.filter (fun S => fresh ∈ S)
  let oldNeighbors : Finset E :=
    (Finset.univ : Finset E).filter (fun e => G.Adj f e)
  have himage_nonempty_old (aold bold : E) :
      (Hnew.edge (Sum.inl aold) ∩ Hnew.edge (Sum.inl bold)).Nonempty ↔
        (H.edge aold ∩ H.edge bold).Nonempty := by
    constructor
    · intro h
      rcases h with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxb⟩
      have hxaimg : x ∈ (H.edge aold).image (Sum.inl : V → V ⊕ Fin (k - 1)) := by
        simpa [Hnew, KUniformFreshEdgeHypergraph] using hxa
      have hxbimg : x ∈ (H.edge bold).image (Sum.inl : V → V ⊕ Fin (k - 1)) := by
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
  have hAold (S : Finset (E ⊕ Unit)) (hS : S ∈ A) : oldOf S ∈ oldPairs := by
    simp only [A, newPairs, oldPairs, Finset.mem_filter] at hS ⊢
    rcases hS with ⟨⟨_, hcard, hsub, hind⟩, hfresh⟩
    have h_range : ∀ x ∈ S, x ∈ Set.range (Sum.inl : E → E ⊕ Unit) := by
      intro x hx
      cases x with
      | inl e => exact ⟨e, rfl⟩
      | inr u => cases u; exact (hfresh hx).elim
    have himage : (oldOf S).image (Sum.inl : E → E ⊕ Unit) = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
        simpa [oldOf] using he
      · intro hx
        rcases h_range x hx with ⟨e, rfl⟩
        exact Finset.mem_image.mpr ⟨e, by simpa [oldOf], rfl⟩
    refine ⟨by simp, ?_⟩
    constructor
    · have hcard_image : ((oldOf S).image (Sum.inl : E → E ⊕ Unit)).card =
          (oldOf S).card := by
        exact Finset.card_image_of_injective _ Sum.inl_injective
      rw [← hcard_image, himage, hcard]
    constructor
    · intro x hx
      have hxnew : Sum.inl x ∈ Gnew.neighborFinset (Sum.inl f) :=
        hsub (by simpa [oldOf] using hx)
      rcases (by
          simpa [SimpleGraph.mem_neighborFinset, Gnew, LineGraphOfHypergraph]
            using hxnew) with ⟨hne, hint⟩
      simp [SimpleGraph.mem_neighborFinset, G, LineGraphOfHypergraph]
      exact ⟨by simpa using hne, (himage_nonempty_old f x).mp hint⟩
    · intro x hx y hy hxy
      have hxS : Sum.inl x ∈ S := by simpa [oldOf] using hx
      have hyS : Sum.inl y ∈ S := by simpa [oldOf] using hy
      have hxy' : (Sum.inl x : E ⊕ Unit) ≠ Sum.inl y := by simp [hxy]
      have hnotnew := hind hxS hyS hxy'
      intro hold
      apply hnotnew
      rcases hold with ⟨hne, hnonempty⟩
      exact ⟨by simpa using hne, (himage_nonempty_old x y).mpr hnonempty⟩
  have hAinj : Set.InjOn (fun S : Finset (E ⊕ Unit) => oldOf S)
      (↑A : Set (Finset (E ⊕ Unit))) := by
    intro S hS T hT heq
    ext x
    cases x with
    | inl e =>
        have := congrArg (fun (U : Finset E) => e ∈ U) heq
        simpa [oldOf] using this
    | inr u =>
        cases u
        have hSfresh : fresh ∉ S := (Finset.mem_filter.mp hS).2
        have hTfresh : fresh ∉ T := (Finset.mem_filter.mp hT).2
        exact ⟨fun hx => (hSfresh hx).elim, fun hx => (hTfresh hx).elim⟩
  have hAcard : A.card ≤ oldPairs.card :=
    Finset.card_le_card_of_injOn (fun S : Finset (E ⊕ Unit) => oldOf S)
      (by intro S hS; exact hAold S hS) hAinj
  let oldNeighborPairImage : Finset (Finset (E ⊕ Unit)) :=
    oldNeighbors.image (fun e => ({fresh, Sum.inl e} : Finset (E ⊕ Unit)))
  have hBsub : B ⊆ oldNeighborPairImage := by
    intro S hS
    simp only [B, newPairs, Finset.mem_filter] at hS
    rcases hS with ⟨⟨_, hcard, hsub, _hind⟩, hfresh⟩
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfresh
    rcases hfresh with hx | hy
    · subst x
      cases y with
      | inl e =>
          have hye : Sum.inl e ∈ ({fresh, Sum.inl e} : Finset (E ⊕ Unit)) := by
            simp
          have hyneigh := hsub hye
          have heold : e ∈ oldNeighbors := by
            simp only [oldNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases (by
                simpa [SimpleGraph.mem_neighborFinset, Gnew, LineGraphOfHypergraph]
                  using hyneigh) with ⟨hne, hnonempty⟩
            exact ⟨by intro h; apply hne; simp [h],
              (himage_nonempty_old f e).mp hnonempty⟩
          exact Finset.mem_image.mpr ⟨e, heold, by simp [fresh]⟩
      | inr u =>
          cases u
          simp [fresh] at hxy
    · subst y
      cases x with
      | inl e =>
          have hxe : Sum.inl e ∈ ({Sum.inl e, fresh} : Finset (E ⊕ Unit)) := by
            simp
          have hxneigh := hsub hxe
          have heold : e ∈ oldNeighbors := by
            simp only [oldNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases (by
                simpa [SimpleGraph.mem_neighborFinset, Gnew, LineGraphOfHypergraph]
                  using hxneigh) with ⟨hne, hnonempty⟩
            exact ⟨by intro h; apply hne; simp [h],
              (himage_nonempty_old f e).mp hnonempty⟩
          exact Finset.mem_image.mpr
            ⟨e, heold, by ext z <;> simp [fresh, or_comm]⟩
      | inr u =>
          cases u
          simp [fresh] at hxy
  have hBcard : B.card ≤ oldNeighbors.card := by
    have himgcard : oldNeighborPairImage.card = oldNeighbors.card := by
      dsimp [oldNeighborPairImage]
      rw [Finset.card_image_of_injective]
      intro a b hab
      have hmem : (Sum.inl a : E ⊕ Unit) ∈ ({fresh, Sum.inl b} : Finset (E ⊕ Unit)) := by
        change ({fresh, Sum.inl a} : Finset (E ⊕ Unit)) = {fresh, Sum.inl b} at hab
        rw [← hab]
        simp
      simpa [fresh] using hmem
    exact le_trans (Finset.card_le_card hBsub) (by rw [himgcard])
  have hpart : B.card + A.card = newPairs.card := by
    simpa [B, A] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := newPairs)
        (fun S => fresh ∈ S))
  have hnew : newPairs.card ≤ oldPairs.card + oldNeighbors.card := by
    nlinarith
  simpa [IndependentPairCount, G, Gnew, Hnew, oldPairs, newPairs, oldNeighbors,
    LineGraphOfHypergraph] using hnew
