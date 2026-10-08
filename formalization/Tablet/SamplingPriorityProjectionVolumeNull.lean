import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable

open BigOperators
open MeasureTheory Set

-- [TABLET NODE: SamplingPriorityProjectionVolumeNull]
theorem SamplingPriorityProjectionVolumeNull
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hfinite : ∀ A : Finset V, ν {ω | ω.1 = A} ≠ ⊤)
    (hrect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ q : V, t q ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω | ω.1 = A ∧ ∀ q : V, 0 ≤ ω.2 q ∧ ω.2 q ≤ t q} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ q : V, t q))
    (D : Set (V → ℝ)) (hD : MeasurableSet D) (hvol : volume D = 0) :
    ν {ω | ω.2 ∈ D} = 0 := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let Q : Set (V → ℝ) := {q | ∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1}
  let C : Set (Finset V × (V → ℝ)) := {ω | ω.2 ∈ Q}
  let F : Finset V → Set (Finset V × (V → ℝ)) := fun A => {ω | ω.1 = A}
  have hQ : MeasurableSet Q := by dsimp [Q]; measurability
  have hatom : ∀ A : Finset V, ν {ω | ω.1 = A ∧ ω.2 ∈ D} = 0 := by
    intro A
    have hin : ν ({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) = 0 := by
      have heq := SamplingFiniteProductLowerOrthantEqualityMeasurable
        (ν := ν) (F := fun ω => ω.1 = A) (p := fun ω => ω.2)
        measurable_snd (ν {ω | ω.1 = A}) (D ∩ Q) (hD.inter hQ)
        inter_subset_right (hfinite A) rfl (hrect A)
      have hz : volume (D ∩ Q) = 0 := measure_mono_null inter_subset_left hvol
      rw [hz, mul_zero] at heq
      convert heq using 1
      congr 1
      ext ω
      simp [C, Q, and_assoc, and_left_comm, and_comm]
    have hmass : ν (F A ∩ C) = ν (F A) := by
      simpa [F, C, Q, Set.mem_Icc] using
        hrect A (fun _ => 1) (by intro q; simp)
    have hmeas : MeasurableSet (F A ∩ C) := by
      dsimp [F, C, Q]
      measurability
    have hout : ν (F A \ (F A ∩ C)) = 0 := by
      rw [measure_diff inter_subset_left hmeas.nullMeasurableSet
        (hmass ▸ hfinite A), hmass, tsub_self]
    apply measure_mono_null (t :=
      ({ω | ω.1 = A ∧ ω.2 ∈ D} ∩ C) ∪ (F A \ (F A ∩ C)))
      _ (measure_union_null hin hout)
    intro ω hω
    by_cases hc : ω ∈ C
    · exact Or.inl ⟨hω, hc⟩
    · exact Or.inr ⟨hω.1, fun h => hc h.2⟩
  apply measure_mono_null (t := ⋃ A : Finset V, {ω | ω.1 = A ∧ ω.2 ∈ D})
  · intro ω hω
    exact mem_iUnion.mpr ⟨ω.1, rfl, hω⟩
  · exact measure_iUnion_null_iff.mpr hatom
