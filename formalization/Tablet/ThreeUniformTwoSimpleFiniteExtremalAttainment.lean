import Tablet.FiniteRealFunctionAttainsMaximum
import Tablet.HypergraphClass
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.ThreeUniformTwoSimpleBoundedRepresentative

universe u v

-- [TABLET NODE: ThreeUniformTwoSimpleFiniteExtremalAttainment]
theorem ThreeUniformTwoSimpleFiniteExtremalAttainment (D : ℕ) (hD : 0 < D) :
    ∃ (V₀ E₀ : Type) (_ : Fintype V₀) (_ : Fintype E₀)
      (_ : DecidableEq E₀) (_ : DecidableEq V₀)
      (F : MultiHypergraph V₀ E₀) (f : E₀),
      F ∈ HypergraphClass (V := V₀) (E := E₀) 3 2 D ∧
      ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) 3 2 D → ∀ e : E,
          @LocalBParameter E _ _ (LineGraphOfHypergraph H)
            (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e ≤
          @LocalBParameter E₀ _ _ (LineGraphOfHypergraph F)
            (Classical.decRel (LineGraphOfHypergraph F).Adj) (3 * D) f := by
-- BODY
  classical
  let M := 1 + 3 * (D - 1)
  let P := Σ m : Fin (M + 1), Σ l : Fin (3 * M + 1),
    {q : (Fin m.val → Finset (Fin l.val)) × Fin m.val //
      ({edge := q.1} : MultiHypergraph (Fin l.val) (Fin m.val)) ∈
        HypergraphClass 3 2 D}
  let score : P → ℝ := fun p =>
    @LocalBParameter (Fin p.1.val) _ _
      (LineGraphOfHypergraph ({edge := p.2.2.val.1} :
        MultiHypergraph (Fin p.2.1.val) (Fin p.1.val)))
      (Classical.decRel _) (3 * D) p.2.2.val.2
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hsingle : ({edge := fun _ : Fin 1 => (Finset.univ : Finset (Fin 3))} :
      MultiHypergraph (Fin 3) (Fin 1)) ∈ HypergraphClass 3 2 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; simp
    · intro a b hab
      exact (hab (Subsingleton.elim a b)).elim
    · intro x
      simpa [HypergraphDegree] using hD
  letI : Nonempty P := ⟨⟨⟨1, by omega⟩, ⟨3, by omega⟩,
    ⟨⟨fun _ => Finset.univ, 0⟩, hsingle⟩⟩⟩
  obtain ⟨p, hp⟩ := FiniteRealFunctionAttainsMaximum score
  refine ⟨Fin p.2.1.val, Fin p.1.val, inferInstance, inferInstance,
    inferInstance, inferInstance, {edge := p.2.2.val.1}, p.2.2.val.2,
    p.2.2.property, ?_⟩
  intro V E _ _ _ H hH e
  obtain ⟨m, l, hm, hl, F, f, hF, heq⟩ :=
    ThreeUniformTwoSimpleBoundedRepresentative D hD H hH e
  have hlM : l ≤ 3 * M := hl.trans (Nat.mul_le_mul_left 3 hm)
  let q : P := ⟨⟨m, by omega⟩, ⟨l, by omega⟩, ⟨⟨F.edge, f⟩, hF⟩⟩
  exact heq.le.trans (hp q)
