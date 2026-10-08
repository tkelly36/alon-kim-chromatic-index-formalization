import Tablet.IndependentTripleCount

set_option maxHeartbeats 800000

-- [TABLET NODE: NeighborhoodComplementTriangleCountEqualsIndependentTripleCount]
theorem NeighborhoodComplementTriangleCountEqualsIndependentTripleCount :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj], ∀ v : V,
        ∀ C : SimpleGraph {u : V // u ∈ G.neighborFinset v}, ∀ [DecidableRel C.Adj],
          (∀ x y, C.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x.1 y.1) →
        IndependentTripleCount G v =
          ((Finset.univ : Finset (Finset {u : V // u ∈ G.neighborFinset v})).filter
            (fun s =>
              s.card = 3 ∧
                ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → C.Adj x y)).card := by
-- BODY
  classical
  intro V _ _ G _ v C _ hC
  unfold IndependentTripleCount
  let A : Finset (Finset V) :=
    (Finset.univ.filter (fun S =>
      S.card = 3 ∧ S ⊆ G.neighborFinset v ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y))
  let B : Finset (Finset {u : V // u ∈ G.neighborFinset v}) :=
    (Finset.univ.filter (fun s =>
      s.card = 3 ∧
        ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → C.Adj x y))
  change A.card = B.card
  refine Finset.card_bij'
    (fun S _ => S.subtype (fun x => x ∈ G.neighborFinset v))
    (fun s _ => s.image Subtype.val)
    ?_ ?_ ?_ ?_
  · intro S hS
    dsimp [A, B] at hS ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rcases hS with ⟨hcard, hsub, hind⟩
    constructor
    · rw [Finset.card_subtype]
      have hfilter : S.filter (fun x => x ∈ G.neighborFinset v) = S := by
        apply Finset.filter_true_of_mem
        intro x hx
        exact hsub hx
      rw [hfilter, hcard]
    · intro x hx y hy hxy
      exact (hC x y).mpr ⟨by
        intro hval
        exact hxy hval, hind (by simpa using hx) (by simpa using hy)
          (by intro h; exact hxy (Subtype.ext h))⟩
  · intro s hs
    dsimp [A, B] at hs ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rcases hs with ⟨hcard, hclique⟩
    constructor
    · have himage : (s.image Subtype.val).card = s.card := by
        rw [Finset.card_image_iff]
        intro x _ y _ hxy
        exact Subtype.ext hxy
      rw [himage, hcard]
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
      exact a.2
    · intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := by
        intro h
        exact hxy (congrArg Subtype.val h)
      exact ((hC a b).mp (hclique ha hb hab)).2
  · intro S hS
    apply Finset.ext
    intro x
    dsimp
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, hval⟩
      simpa [hval] using (Finset.mem_subtype.mp ha)
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, by
        dsimp [A] at hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        exact hS.2.1 hx⟩, by simpa using hx, rfl⟩
  · intro s _hs
    apply Finset.ext
    intro x
    dsimp
    constructor
    · intro hx
      rcases Finset.mem_subtype.mp hx with hxim
      rcases Finset.mem_image.mp hxim with ⟨a, ha, hval⟩
      have hx_eq_a : x = a := Subtype.ext hval.symm
      simpa [hx_eq_a] using ha
    · intro hx
      exact Finset.mem_subtype.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
