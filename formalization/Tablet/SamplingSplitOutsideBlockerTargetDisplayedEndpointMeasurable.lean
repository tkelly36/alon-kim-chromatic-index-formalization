import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerTargetDisplayedEndpointMeasurable]
theorem SamplingSplitOutsideBlockerTargetDisplayedEndpointMeasurable
    {V V' : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V']
    (G : SimpleGraph V) (φ : V → V') (r : V) (X : Finset V)
    {n : ℕ} (zAt : Fin n → V) (B : Fin n → Finset V)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V') :
    @MeasurableSet (Finset V' × (V' → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance)
      {η | ∃ x : V, ∃ hx : x ∈ X, φ x ∈ η.1 ∧
        (∀ y : V, y ∈ insert r X → φ y ∈ η.1 →
          G.Adj x y → η.2 (φ y) < η.2 (φ x)) ∧
        (∀ i : Fin n, x ∈ B i →
          ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
            ¬ (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩ ∈ η.1 ∧
              η.2 (φ x) < η.2 (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩) ∧
              η.2 (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1))} := by
-- BODY
  letI : MeasurableSpace (Finset V') := ⊤
  have ha (v : V') : Measurable (fun η : Finset V' × (V' → ℝ) => v ∈ η.1) :=
    (measurable_of_finite (fun A : Finset V' => v ∈ A)).comp measurable_fst
  have hp (v : V') : Measurable (fun η : Finset V' × (V' → ℝ) => η.2 v) :=
    (measurable_pi_apply v).comp measurable_snd
  have hlt (v y : V') : Measurable (fun η : Finset V' × (V' → ℝ) => η.2 v < η.2 y) :=
    measurableSet_setOf.mp (measurableSet_lt (hp v) (hp y))
  have hu (v : V') : Measurable (fun η : Finset V' × (V' → ℝ) => η.2 v ∈ Set.Icc (0 : ℝ) 1) :=
    measurableSet_setOf.mp (measurableSet_Icc.preimage (hp v))
  apply Measurable.setOf
  apply Measurable.exists
  intro x
  apply Measurable.exists
  intro hx
  exact (ha (φ x)).and
    ((Measurable.forall fun y => measurable_const.imp
      ((ha (φ y)).imp (measurable_const.imp (hlt (φ y) (φ x))))).and
    (Measurable.forall fun i => measurable_const.imp
      (Measurable.forall fun hz =>
        ((ha (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩)).and
          ((hlt (φ x) (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩)).and
            (hu (β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩)))).not)))
