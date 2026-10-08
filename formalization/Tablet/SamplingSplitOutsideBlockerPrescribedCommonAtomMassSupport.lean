import Tablet.Preamble
import Tablet.SamplingPriorityPositiveUnitSupport
import Tablet.SamplingBernoulliActivationTraceMass

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPrescribedCommonAtomMassSupport]
theorem SamplingSplitOutsideBlockerPrescribedCommonAtomMassSupport :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ (sourceCoord : Finset V) (targetCommonCoord : Finset V') (φ : V → V'),
        Function.Injective φ →
        targetCommonCoord = sourceCoord.image φ →
        ∀ (Delta : ℕ) (gamma : ℝ),
          ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
          ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
            0 ≤ gamma / (Delta : ℝ) →
            gamma / (Delta : ℝ) ≤ 1 →
            (∀ A : Finset V,
              ν {ω | ω.1 = A} =
                ENNReal.ofReal
                  ((gamma / (Delta : ℝ)) ^ A.card *
                    (1 - gamma / (Delta : ℝ)) ^
                      ((Finset.univ : Finset V).card - A.card))) →
            (∀ A : Finset V, ∀ t : V → ℝ,
              (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                ν {ω |
                  ω.1 = A ∧
                    ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                  ν {ω | ω.1 = A} *
                    ENNReal.ofReal (∏ v : V, t v)) →
            (∀ A : Finset V',
              ν' {ω | ω.1 = A} =
                ENNReal.ofReal
                  ((gamma / (Delta : ℝ)) ^ A.card *
                    (1 - gamma / (Delta : ℝ)) ^
                      ((Finset.univ : Finset V').card - A.card))) →
            (∀ A : Finset V', ∀ t : V' → ℝ,
              (∀ v : V', t v ∈ Set.Icc (0 : ℝ) 1) →
                ν' {ω |
                  ω.1 = A ∧
                    ∀ v : V', 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                  ν' {ω | ω.1 = A} *
                    ENNReal.ofReal (∏ v' : V', t v')) →
            let Ω₀ := {A : Finset V // A ⊆ sourceCoord}
            let Λ := Bool × {v : V // v ∈ sourceCoord}
            let baseCell : Ω₀ → Set (Finset V × (V → ℝ)) :=
              fun A => {η | η.1 ∩ sourceCoord = A.1}
            let targetBaseCell : Ω₀ → Set (Finset V' × (V' → ℝ)) :=
              fun A => {η | η.1 ∩ targetCommonCoord = A.1.image φ}
            let sourceLabel : Λ → Set (Finset V × (V → ℝ)) :=
              fun ℓ => {η |
                if ℓ.1 then (0 : ℝ) < η.2 ℓ.2.1
                else η.2 ℓ.2.1 ≤ 1}
            let targetLabel : Λ → Set (Finset V' × (V' → ℝ)) :=
              fun ℓ => {η |
                if ℓ.1 then (0 : ℝ) < η.2 (φ ℓ.2.1)
                else η.2 (φ ℓ.2.1) ≤ 1}
            let transport : Ω₀ → (Finset V × (V → ℝ)) →
              (Finset V' × (V' → ℝ)) → Prop :=
              fun _ η η' =>
                η'.1 ∩ targetCommonCoord =
                  (η.1 ∩ sourceCoord).image φ ∧
                    ∀ v : V, v ∈ sourceCoord →
                      η'.2 (φ v) = η.2 v
            (∀ ω₀ : Ω₀,
              @MeasurableSet (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (baseCell ω₀)) ∧
            (∀ ω₀ : Ω₀,
              @MeasurableSet (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (targetBaseCell ω₀)) ∧
            (∀ ℓ : Λ,
              @MeasurableSet (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (sourceLabel ℓ)) ∧
            (∀ ℓ : Λ,
              @MeasurableSet (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)
                (targetLabel ℓ)) ∧
            (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ →
              Disjoint (baseCell ω₁) (baseCell ω₂)) ∧
            (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ →
              Disjoint (targetBaseCell ω₁) (targetBaseCell ω₂)) ∧
            (∀ ω₀ : Ω₀, ∀ η η',
              transport ω₀ η η' →
                (η ∈ baseCell ω₀ ↔ η' ∈ targetBaseCell ω₀)) ∧
            (∀ ω₀ : Ω₀, ∀ η η',
              transport ω₀ η η' →
                ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ η' ∈ targetLabel ℓ)) ∧
            (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
              ∃ w : ℝ, 0 ≤ w ∧
                ENNReal.ofReal w =
                  ν (baseCell ω₀ ∩
                    {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
                ENNReal.ofReal w =
                  ν' (targetBaseCell ω₀ ∩
                    {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
            (∀ η : Finset V × (V → ℝ),
              (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
                ∃ ω₀ : Ω₀, η ∈ baseCell ω₀) ∧
            (∀ η : Finset V' × (V' → ℝ),
              (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1) →
                ∃ ω₀ : Ω₀, η ∈ targetBaseCell ω₀) ∧
            ν {η : Finset V × (V → ℝ) |
              ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)} = 0 ∧
            ν' {η : Finset V' × (V' → ℝ) |
              ¬ (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1)} = 0 := by
-- BODY
  classical
  intro V V' _ _ _ _ S S' φ hφ hS Delta gamma ν ν' hp hp1 ha hr ha' hr'
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  dsimp only
  have hpos := SamplingPriorityPositiveUnitSupport ν
    (fun A => by rw [ha]; exact ENNReal.ofReal_ne_top) hr
  have hpos' := SamplingPriorityPositiveUnitSupport ν'
    (fun A => by rw [ha']; exact ENNReal.ofReal_ne_top) hr'
  have hmass (A : Finset V) (hA : A ⊆ S) :=
    SamplingBernoulliActivationTraceMass ν (gamma / (Delta : ℝ)) hp hp1 ha S A hA
  have hmass' (A : Finset V) (hA : A ⊆ S) :
      ν' {η | η.1 ∩ S' = A.image φ} =
        ENNReal.ofReal ((gamma / (Delta : ℝ)) ^ A.card *
          (1 - gamma / (Delta : ℝ)) ^ (S.card - A.card)) := by
    subst S'
    simpa only [Finset.card_image_of_injective _ hφ] using
      SamplingBernoulliActivationTraceMass ν' (gamma / (Delta : ℝ)) hp hp1 ha'
        (S.image φ) (A.image φ) (Finset.image_subset_image hA)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact measurable_fst (show MeasurableSet {F : Finset V | F ∩ S = A.1} from trivial)
  · intro A
    exact measurable_fst (show MeasurableSet {F : Finset V' | F ∩ S' = A.1.image φ} from trivial)
  · rintro ⟨b, v⟩
    cases b
    · exact measurableSet_le ((measurable_pi_apply v.1).comp measurable_snd) measurable_const
    · exact measurableSet_lt measurable_const ((measurable_pi_apply v.1).comp measurable_snd)
  · rintro ⟨b, v⟩
    cases b
    · exact measurableSet_le ((measurable_pi_apply (φ v.1)).comp measurable_snd) measurable_const
    · exact measurableSet_lt measurable_const ((measurable_pi_apply (φ v.1)).comp measurable_snd)
  · intro A B hAB
    apply Set.disjoint_left.mpr
    intro η hA hB
    exact hAB (Subtype.ext (hA.symm.trans hB))
  · intro A B hAB
    apply Set.disjoint_left.mpr
    intro η hA hB
    exact hAB (Subtype.ext ((Finset.image_injective hφ) (hA.symm.trans hB)))
  · intro A η η' h
    change η.1 ∩ S = A.1 ↔ η'.1 ∩ S' = A.1.image φ
    rw [h.1]
    exact (Finset.image_injective hφ).eq_iff.symm
  · intro A η η' h ℓ
    change (if ℓ.1 then 0 < η.2 ℓ.2.1 else η.2 ℓ.2.1 ≤ 1) ↔
      (if ℓ.1 then 0 < η'.2 (φ ℓ.2.1) else η'.2 (φ ℓ.2.1) ≤ 1)
    rw [h.2 ℓ.2.1 ℓ.2.2]
  · intro A truth
    by_cases ht : ∀ ℓ : Bool × {v : V // v ∈ S}, ℓ ∈ truth
    · refine ⟨(gamma / (Delta : ℝ)) ^ A.1.card *
        (1 - gamma / (Delta : ℝ)) ^ (S.card - A.1.card),
        mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _), ?_, ?_⟩
      · rw [← hmass A.1 A.2]
        apply measure_congr
        filter_upwards [hpos] with η hη
        have hall : ∀ ℓ : Bool × {v : V // v ∈ S},
            (if ℓ.1 then 0 < η.2 ℓ.2.1 else η.2 ℓ.2.1 ≤ 1) ↔ ℓ ∈ truth := by
          intro ℓ
          apply iff_of_true _ (ht ℓ)
          cases ℓ.1
          · exact (hη ℓ.2.1).2
          · exact (hη ℓ.2.1).1
        exact propext ⟨fun h => ⟨h, hall⟩, fun h => h.1⟩
      · rw [← hmass' A.1 A.2]
        apply measure_congr
        filter_upwards [hpos'] with η hη
        have hall : ∀ ℓ : Bool × {v : V // v ∈ S},
            (if ℓ.1 then 0 < η.2 (φ ℓ.2.1) else η.2 (φ ℓ.2.1) ≤ 1) ↔ ℓ ∈ truth := by
          intro ℓ
          apply iff_of_true _ (ht ℓ)
          cases ℓ.1
          · exact (hη (φ ℓ.2.1)).2
          · exact (hη (φ ℓ.2.1)).1
        exact propext ⟨fun h => ⟨h, hall⟩, fun h => h.1⟩
    · obtain ⟨ℓ, hℓ⟩ := not_forall.mp ht
      refine ⟨0, le_rfl, ?_, ?_⟩ <;> rw [ENNReal.ofReal_zero]
      · symm
        apply compl_mem_ae_iff.mp
        filter_upwards [hpos] with η hη
        intro h
        apply hℓ
        apply (h.2 ℓ).mp
        cases ℓ.1
        · exact (hη ℓ.2.1).2
        · exact (hη ℓ.2.1).1
      · symm
        apply compl_mem_ae_iff.mp
        filter_upwards [hpos'] with η hη
        intro h
        apply hℓ
        apply (h.2 ℓ).mp
        cases ℓ.1
        · exact (hη (φ ℓ.2.1)).2
        · exact (hη (φ ℓ.2.1)).1
  · intro η _
    exact ⟨⟨η.1 ∩ S, Finset.inter_subset_right⟩, rfl⟩
  · intro η _
    refine ⟨⟨S.filter (fun v => φ v ∈ η.1), Finset.filter_subset _ _⟩, ?_⟩
    change η.1 ∩ S' = (S.filter (fun v => φ v ∈ η.1)).image φ
    rw [hS]
    ext v
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hv, w, hw, rfl⟩
      exact ⟨w, ⟨hw, hv⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hv⟩, rfl⟩
      exact ⟨hv, w, hw, rfl⟩
  · apply compl_mem_ae_iff.mp
    filter_upwards [hpos] with η hη
    exact not_not.mpr (fun v => ⟨(hη v).1.le, (hη v).2⟩)
  · apply compl_mem_ae_iff.mp
    filter_upwards [hpos'] with η hη
    exact not_not.mpr (fun v => ⟨(hη v).1.le, (hη v).2⟩)
