import Tablet.NibbleCompletionData
import Tablet.FiniteSimpleRegularCompletion
import Tablet.UniformHypergraphLineDegreeBound

-- [TABLET NODE: NibbleRegularCompletionsExist]
theorem NibbleRegularCompletionsExist {V E K : Type*} [Fintype E]
    [DecidableEq E] [DecidableEq V] [DecidableEq K]
    (H : MultiHypergraph V E) (M : E → Finset K) (k D : ℕ)
    (hu : UniformHypergraph H k) (hd : MaxDegreeAtMost H D) :
    Nonempty (NibbleCompletionData H M (k * D)) := by
-- BODY
  classical
  have perColor : ∀ a : K, ∃ (n : ℕ) (G : SimpleGraph (Fin n))
      (f : {e : E // a ∈ M e} → Fin n),
      Function.Injective f ∧
      (∀ e g, G.Adj (f e) (f g) ↔ (LineGraphOfHypergraph H).Adj e.val g.val) ∧
      (∀ v, (G.neighborSet v).ncard = k * D) := by
    intro a
    let G := (LineGraphOfHypergraph H).induce {e | a ∈ M e}
    have hdegree : ∀ e, G.degree e ≤ k * D := by
      intro e
      have hinj : Function.Injective
          (fun g : G.neighborSet e =>
            (⟨g.val.val, g.property⟩ : (LineGraphOfHypergraph H).neighborSet e.val)) := by
        intro g h heq
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : (LineGraphOfHypergraph H).neighborSet e.val => x.val) heq
      calc
        G.degree e = Fintype.card (G.neighborSet e) :=
          (G.card_neighborSet_eq_degree e).symm
        _ ≤ Fintype.card ((LineGraphOfHypergraph H).neighborSet e.val) :=
          Fintype.card_le_of_injective _ hinj
        _ = (LineGraphOfHypergraph H).degree e.val :=
          SimpleGraph.card_neighborSet_eq_degree _ _
        _ ≤ k * (D - 1) := UniformHypergraphLineDegreeBound H hu hd e.val
        _ ≤ k * D := Nat.mul_le_mul_left k (Nat.sub_le D 1)
    obtain ⟨W, instF, instD, J, instAdj, f, hf, hi, hr⟩ :=
      FiniteSimpleRegularCompletion G (k * D) hdegree
    letI := instF
    letI := instD
    letI := instAdj
    let b : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
    let J' : SimpleGraph (Fin (Fintype.card W)) := J.comap b.symm
    refine ⟨Fintype.card W, J', b ∘ f, b.injective.comp hf, ?_, ?_⟩
    · intro e g
      simpa [J', SimpleGraph.comap, Function.comp_def] using hi e g
    · intro v
      let nb : J'.neighborSet v ≃ J.neighborSet (b.symm v) :=
        { toFun := fun w => ⟨b.symm w.val, w.property⟩
          invFun := fun w => ⟨b w.val, by
            change J.Adj (b.symm v) (b.symm (b w.val))
            rw [b.symm_apply_apply]
            exact w.property⟩
          left_inv := by intro w; apply Subtype.ext; exact b.apply_symm_apply w.val
          right_inv := by intro w; apply Subtype.ext; exact b.symm_apply_apply w.val }
      calc
        (J'.neighborSet v).ncard = Fintype.card (J'.neighborSet v) :=
          by rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
        _ = Fintype.card (J.neighborSet (b.symm v)) := Fintype.card_congr nb
        _ = J.degree (b.symm v) := J.card_neighborSet_eq_degree _
        _ = k * D := hr _
  choose n G f hf hi hr using perColor
  exact ⟨{ size := n
           graph := G
           embed := f
           injective := hf
           induced := hi
           regular := hr }⟩
