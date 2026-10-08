import Tablet.OrderThreeAffineMultihypergraph
import Tablet.HypergraphClass
import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: OrderThreeAffineGeometry]
theorem OrderThreeAffineGeometry (q : ℕ) :
    OrderThreeAffineMultihypergraph q ∈ HypergraphClass 3 3 (3 * q + 1) ∧
    (∀ u, (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)).Adj none u ↔
      u ≠ none) ∧
    @SimpleGraph.degree _ (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q))
      none (by classical exact inferInstance) = 9 * q ∧
    (∀ m a n b : ZMod 3, ∀ i j : Fin q,
      Disjoint ((OrderThreeAffineMultihypergraph q).edge (some (m, a, i)))
        ((OrderThreeAffineMultihypergraph q).edge (some (n, b, j))) ↔
          m = n ∧ a ≠ b) := by
-- BODY
  have hfinite : ∀ m a n b : ZMod 3,
      Disjoint (Finset.univ.image (fun x : ZMod 3 => (x, m * x + a)))
        (Finset.univ.image (fun x : ZMod 3 => (x, n * x + b))) ↔
        m = n ∧ a ≠ b := by decide
  classical
  have hunif : UniformHypergraph (OrderThreeAffineMultihypergraph q) 3 := by
    intro e
    cases e with
    | none => simp [OrderThreeAffineMultihypergraph, Finset.card_image_of_injective,
        Function.Injective, Prod.mk.injEq]
    | some t =>
      rcases t with ⟨m, a, i⟩
      have hinj : Function.Injective (fun x : ZMod 3 => (x, m * x + a)) :=
        fun _ _ h => congrArg Prod.fst h
      simp [OrderThreeAffineMultihypergraph, Finset.card_image_of_injective _ hinj]
  have hneigh : ∀ u, (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)).Adj
      none u ↔ u ≠ none := by
    intro u
    cases u with
    | none => simp
    | some t =>
      rcases t with ⟨m, a, i⟩
      constructor
      · simp
      · intro _
        refine ⟨by simp, ⟨(0, a), ?_⟩⟩
        simp [OrderThreeAffineMultihypergraph]
  refine ⟨⟨hunif, ?_, ?_⟩, hneigh, ?_, ?_⟩
  · intro e f _
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (hunif e)
  · intro v
    rcases v with ⟨x, y⟩
    let S : Finset (Option (ZMod 3 × ZMod 3 × Fin q)) :=
      Finset.univ.image (fun t : ZMod 3 × Fin q => some (t.1, y - t.1 * x, t.2))
    have hinj : Function.Injective
        (fun t : ZMod 3 × Fin q => some (t.1, y - t.1 * x, t.2)) := by
      intro a b h
      have hh := Option.some.inj h
      apply Prod.ext
      · exact congrArg (fun t : ZMod 3 × ZMod 3 × Fin q => t.1) hh
      · exact congrArg (fun t : ZMod 3 × ZMod 3 × Fin q => t.2.2) hh
    have hScard : S.card = 3 * q := by
      simp [S, Finset.card_image_of_injective _ hinj, Fintype.card_prod]
    have hsub : (Finset.univ.filter
        (fun e => (x, y) ∈ (OrderThreeAffineMultihypergraph q).edge e)) ⊆ insert none S := by
      intro e he
      cases e with
      | none => simp
      | some t =>
        rcases t with ⟨m, a, i⟩
        have heq : m * x + a = y := by
          simpa [OrderThreeAffineMultihypergraph] using he
        have ha : a = y - m * x := by rw [← heq]; ring
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨(m, i), Finset.mem_univ _, by simp [ha]⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans_eq
      (by rw [hScard]))
  · have heq : (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)).neighborFinset
        none = Finset.univ.erase none := by
      ext u
      simp [hneigh]
    rw [SimpleGraph.degree, heq]
    simp [Fintype.card_option, Fintype.card_prod]
    omega
  · intro m a n b i j
    exact hfinite m a n b
