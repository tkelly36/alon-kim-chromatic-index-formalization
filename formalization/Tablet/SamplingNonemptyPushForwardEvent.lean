import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingNonemptyPushForwardEvent]
theorem SamplingNonemptyPushForwardEvent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : Finset V → ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S)
    (hpush : ∀ S : Finset V,
      ENNReal.ofReal (μ S) =
        ν {ω |
          S =
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)})
    (X : Finset V) :
    ENNReal.ofReal (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) =
        ν {ω |
          ((Finset.univ.filter fun z : V =>
            z ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∩ X).Nonempty} := by
-- BODY
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let P : V → Finset V × (V → ℝ) → Prop := fun z ω =>
    z ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z
  let I : Finset V × (V → ℝ) → Finset V := fun ω =>
    Finset.univ.filter fun z : V => P z ω
  let good : Finset V → Prop := fun S => (S ∩ X).Nonempty
  let fiber : Finset V → Set (Finset V × (V → ℝ)) := fun S => {ω | S = I ω}
  have hact_any (a : V) : MeasurableSet {ω : Finset V × (V → ℝ) | a ∈ ω.1} := by
    exact (show MeasurableSet {A : Finset V | a ∈ A} from trivial).preimage measurable_fst
  have hlt_any (a b : V) : MeasurableSet {ω : Finset V × (V → ℝ) | ω.2 a < ω.2 b} := by
    exact measurableSet_lt (Measurable.eval (a := a) measurable_snd)
      (Measurable.eval (a := b) measurable_snd)
  have hP (z : V) : MeasurableSet {ω : Finset V × (V → ℝ) | P z ω} := by
    have hcomp : MeasurableSet {ω : Finset V × (V → ℝ) |
        ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z} := by
      rw [Set.setOf_forall]
      refine MeasurableSet.iInter (ι := V) fun w => ?_
      by_cases hadj : G.Adj z w
      · convert (hact_any w).compl.union (hlt_any w z) using 1
        ext ω
        by_cases hmem : w ∈ ω.1
        · simp [hadj, hmem]
        · simp [hadj, hmem]
      · simp [hadj]
    exact (hact_any z).inter hcomp
  have hfiber_meas (S : Finset V) : MeasurableSet (fiber S) := by
    have hEq : fiber S =
        ⋂ z : V, if z ∈ S then {ω : Finset V × (V → ℝ) | P z ω}
          else {ω : Finset V × (V → ℝ) | ¬ P z ω} := by
      ext ω
      simp only [fiber, I, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h z
        subst h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hp : z ∈ ω.1 ∧
            ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z
        · rw [if_pos hp]
          simpa [P] using hp
        · rw [if_neg hp]
          simpa [P] using hp
      · intro h
        ext z
        have hz := h z
        by_cases hS : z ∈ S
        · have hp : P z ω := by simpa [hS] using hz
          rcases hp with ⟨hzin, hprior⟩
          simp [P, hS, hzin]
          exact hprior
        · have hp : ¬ P z ω := by simpa [hS] using hz
          simp [P, hS, hp]
    rw [hEq]
    refine MeasurableSet.iInter (ι := V) fun z => ?_
    by_cases hz : z ∈ S
    · rw [if_pos hz]
      exact hP z
    · rw [if_neg hz]
      exact (hP z).compl
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ.filter good) : Set (Finset V)) fiber := by
    intro A _hA B _hB hAB
    exact Set.disjoint_left.2 fun _ω hAf hBf =>
      hAB (by simpa [fiber] using hAf.trans hBf.symm)
  have hevent : {ω : Finset V × (V → ℝ) | good (I ω)} =
      ⋃ S ∈ Finset.univ.filter good, fiber S := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨I ω, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, ?_⟩
      · simpa using hω
      · simp [fiber]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨S, hS⟩
      rcases Set.mem_iUnion.1 hS with ⟨hSgood, hSf⟩
      have hgood : good S := by simpa using (Finset.mem_filter.1 hSgood).2
      have hSI : S = I ω := by simpa [fiber] using hSf
      simpa [hSI] using hgood
  have hmeasure : ν {ω : Finset V × (V → ℝ) | good (I ω)} =
      ∑ S ∈ Finset.univ.filter good, ν (fiber S) := by
    rw [hevent]
    exact MeasureTheory.measure_biUnion_finset (μ := ν) hdisj fun S _hS => hfiber_meas S
  calc
    ENNReal.ofReal (∑ S : Finset V, if good S then μ S else 0)
        = ∑ S : Finset V, ENNReal.ofReal (if good S then μ S else 0) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro S _hS
          by_cases hgood : good S
          · simp [hgood, hμ_nonneg S]
          · simp [hgood]
    _ = ∑ S : Finset V, if good S then ν (fiber S) else 0 := by
          refine Finset.sum_congr rfl fun S _hS => ?_
          by_cases hgood : good S
          · simp [hgood, fiber, I, P, hpush S]
          · simp [hgood]
    _ = ∑ S ∈ Finset.univ.filter good, ν (fiber S) := by
          simp [Finset.sum_filter, good]
    _ = ν {ω : Finset V × (V → ℝ) | good (I ω)} := hmeasure.symm
    _ = ν {ω |
          ((Finset.univ.filter fun z : V =>
            z ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∩ X).Nonempty} := by
          rfl
