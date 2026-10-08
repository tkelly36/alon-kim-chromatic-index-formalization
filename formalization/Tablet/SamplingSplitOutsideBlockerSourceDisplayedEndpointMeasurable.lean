import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerSourceDisplayedEndpointMeasurable]
theorem SamplingSplitOutsideBlockerSourceDisplayedEndpointMeasurable
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (X : Finset V) {n : ℕ} (zAt : Fin n → V) (B : Fin n → Finset V) :
    @MeasurableSet (Finset V × (V → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance)
      {η : Finset V × (V → ℝ) |
        ∃ x : V, x ∈ X ∧ x ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
          (∀ i : Fin n, x ∈ B i →
            ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
              η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))} := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let coord : V → ((Finset V × (V → ℝ)) → ℝ) := fun v η => η.2 v
  have hcoord_meas : ∀ v : V, Measurable (coord v) := by
    intro v
    dsimp [coord]
    exact (measurable_pi_apply v).comp measurable_snd
  have hlt : ∀ a b : V, MeasurableSet {η : Finset V × (V → ℝ) | η.2 a < η.2 b} := by
    intro a b
    exact measurableSet_lt (hcoord_meas a) (hcoord_meas b)
  have hIcc :
      ∀ a : V, MeasurableSet {η : Finset V × (V → ℝ) | η.2 a ∈ Set.Icc (0 : ℝ) 1} := by
    intro a
    exact measurableSet_Icc.preimage (hcoord_meas a)
  have hactive : ∀ a : V, MeasurableSet {η : Finset V × (V → ℝ) | a ∈ η.1} := by
    intro a
    have hfirst : MeasurableSet {A : Finset V | a ∈ A} := by
      trivial
    exact hfirst.preimage measurable_fst
  have hpiece : ∀ x : V,
      MeasurableSet {η : Finset V × (V → ℝ) | x ∈ X ∧ x ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
          (∀ i : Fin n, x ∈ B i →
            ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
              η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))} := by
    intro x
    by_cases hx : x ∈ X
    · simp only [hx, true_and]
      refine (hactive x).inter ?_
      change MeasurableSet
        ({η : Finset V × (V → ℝ) |
            ∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x} ∩
          {η : Finset V × (V → ℝ) |
            ∀ i : Fin n, x ∈ B i →
              ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)})
      rw [show {η : Finset V × (V → ℝ) |
            ∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x} =
          ⋂ y : V,
            {η : Finset V × (V → ℝ) |
              y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x} by
        ext η
        simp,
        show {η : Finset V × (V → ℝ) |
            ∀ i : Fin n, x ∈ B i →
              ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} =
          ⋂ i : Fin n,
            {η : Finset V × (V → ℝ) |
              x ∈ B i →
                ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} by
        ext η
        simp]
      refine (MeasurableSet.iInter fun y : V => ?_).inter
        (MeasurableSet.iInter fun i : Fin n => ?_)
      · by_cases hyl : y ∈ insert r X
        · by_cases hyadj : G.Adj x y
          · simp only [hyl, hyadj, true_implies]
            rw [show {η : Finset V × (V → ℝ) | y ∈ η.1 → η.2 y < η.2 x} =
                {η | y ∉ η.1} ∪ {η | η.2 y < η.2 x} by
              ext η
              by_cases hyact : y ∈ η.1 <;> simp [hyact]]
            exact (hactive y).compl.union (hlt y x)
          · simp only [hyl, hyadj, IsEmpty.forall_iff, implies_true, Set.setOf_true]
            exact MeasurableSet.univ
        · simp only [hyl, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
      · by_cases hxb : x ∈ B i
        · simp only [hxb, true_implies]
          rw [show {η : Finset V × (V → ℝ) |
              ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} =
              ({η | zAt i ∈ η.1} ∩ {η | η.2 x < η.2 (zAt i)} ∩
                {η | η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1}).compl by
            ext η
            constructor
            · intro h hbad
              exact h ⟨hbad.1.1, hbad.1.2, hbad.2⟩
            · intro h hbad
              exact h ⟨⟨hbad.1, hbad.2.1⟩, hbad.2.2⟩]
          exact (((hactive (zAt i)).inter (hlt x (zAt i))).inter (hIcc (zAt i))).compl
        · simp only [hxb, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
    · simp only [hx, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  rw [show {η : Finset V × (V → ℝ) |
        ∃ x : V, x ∈ X ∧ x ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
          (∀ i : Fin n, x ∈ B i →
            ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
              η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))} =
      ⋃ x : V, {η : Finset V × (V → ℝ) | x ∈ X ∧ x ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 → G.Adj x y → η.2 y < η.2 x) ∧
          (∀ i : Fin n, x ∈ B i →
            ¬ (zAt i ∈ η.1 ∧ η.2 x < η.2 (zAt i) ∧
              η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))} by
    ext η
    simp]
  exact MeasurableSet.iUnion hpiece
