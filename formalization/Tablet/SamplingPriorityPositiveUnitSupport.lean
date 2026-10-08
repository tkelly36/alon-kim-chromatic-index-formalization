import Tablet.Preamble

open MeasureTheory

-- [TABLET NODE: SamplingPriorityPositiveUnitSupport]
theorem SamplingPriorityPositiveUnitSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hfinite : ∀ A : Finset V, ν {ω | ω.1 = A} ≠ ⊤)
    (hrect : ∀ (A : Finset V) (t : V → ℝ), (∀ v, t v ∈ Set.Icc (0 : ℝ) 1) →
      ν {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
        ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v)) :
    ∀ᵐ ω ∂ν, ∀ v, 0 < ω.2 v ∧ ω.2 v ≤ 1 := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  let U : Set (Finset V × (V → ℝ)) := {ω | ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1}
  have hU : MeasurableSet U := by
    simp only [U, Set.setOf_forall]
    exact MeasurableSet.iInter fun v =>
      ((measurable_pi_apply v).comp measurable_snd) measurableSet_Icc
  have hH (A : Finset V) : MeasurableSet {ω : Finset V × (V → ℝ) | ω.1 = A} :=
    measurable_fst (measurableSet_singleton A)
  have hunit (A : Finset V) :
      ∀ᵐ ω ∂ν, ω.1 = A → ω ∈ U := by
    have hone : ν ({ω | ω.1 = A} ∩ U) = ν {ω | ω.1 = A} := by
      simpa only [Finset.prod_const_one, ENNReal.ofReal_one, mul_one] using
        hrect A (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩)
    have hn := measure_diff (μ := ν) Set.inter_subset_left
      ((hH A).inter hU).nullMeasurableSet (hone ▸ hfinite A)
    have he : {ω | ω.1 = A} \ ({ω | ω.1 = A} ∩ U) =
        {ω | ¬ (ω.1 = A → ω ∈ U)} := by ext ω; simp
    rw [he, hone, tsub_self] at hn
    exact ae_iff.mpr hn
  have hu : ∀ᵐ ω ∂ν, ω ∈ U := by
    filter_upwards [ae_all_iff.mpr hunit] with ω hω
    exact hω ω.1 rfl
  have hzero (v : V) (A : Finset V) :
      ∀ᵐ ω ∂ν, ¬ (ω.1 = A ∧ ω ∈ U ∧ ω.2 v = 0) := by
    let t : V → ℝ := fun w => if w = v then 0 else 1
    have ht : ∀ w, t w ∈ Set.Icc (0 : ℝ) 1 := by
      intro w
      dsimp [t]
      split_ifs <;> constructor <;> norm_num
    have hp : (∏ w, t w) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [t]
    have hn := hrect A t ht
    rw [hp, ENNReal.ofReal_zero, mul_zero] at hn
    apply compl_mem_ae_iff.mpr
    apply measure_mono_null (t := {ω | ω.1 = A ∧ ∀ w, 0 ≤ ω.2 w ∧ ω.2 w ≤ t w}) _ hn
    rintro ω ⟨hA, hω, hz⟩
    refine ⟨hA, fun w => ⟨(hω w).1, ?_⟩⟩
    by_cases hw : w = v
    · simp [t, hw, hz]
    · simpa [t, hw] using (hω w).2
  have hz : ∀ᵐ ω ∂ν, ∀ v, ∀ A, ¬ (ω.1 = A ∧ ω ∈ U ∧ ω.2 v = 0) :=
    ae_all_iff.mpr fun v => ae_all_iff.mpr (hzero v)
  filter_upwards [hu, hz] with ω hω hnonzero
  intro v
  refine ⟨lt_of_le_of_ne (hω v).1 ?_, (hω v).2⟩
  intro he
  exact hnonzero v ω.1 ⟨rfl, hω, he.symm⟩
