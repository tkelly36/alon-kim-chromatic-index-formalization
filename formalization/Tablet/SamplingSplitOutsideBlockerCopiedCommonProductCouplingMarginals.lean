import Tablet.SamplingSplitOutsideBlockerProductRealization
import Tablet.SamplingCopiedCommonTags
import Tablet.SamplingInjectiveCoordinateDecodeLaws
import Tablet.SamplingActivationRectangleMeasureUniqueness

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerCopiedCommonProductCouplingMarginals]
theorem SamplingSplitOutsideBlockerCopiedCommonProductCouplingMarginals :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'],
      ∀ Delta : ℕ, ∀ gamma : ℝ,
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
            (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
              ν' {ω |
                ω.1 = A ∧
                  ∀ v' : V', 0 ≤ ω.2 v' ∧ ω.2 v' ≤ t v'} =
                ν' {ω | ω.1 = A} *
                  ENNReal.ofReal (∏ v' : V', t v')) →
          ∀ (φ : V → V') (sourceCoord : Finset V)
            (targetCommonCoord : Finset V'),
            Function.Injective φ →
            targetCommonCoord = sourceCoord.image φ →
            ∃ pairedMeasure :
              @MeasureTheory.Measure
                ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
                (MeasurableSpace.prod
                  (MeasurableSpace.prod ⊤ inferInstance)
                  (MeasurableSpace.prod ⊤ inferInstance)),
              pairedMeasure {ζ |
                ¬ (ζ.2.1 ∩ targetCommonCoord =
                    (ζ.1.1 ∩ sourceCoord).image φ ∧
                  ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v)} = 0 ∧
              (∀ E : Set (Finset V × (V → ℝ)),
                @MeasurableSet (Finset V × (V → ℝ))
                  (MeasurableSpace.prod ⊤ inferInstance) E →
                  pairedMeasure {ζ | ζ.1 ∈ E} = ν E) ∧
              (∀ E' : Set (Finset V' × (V' → ℝ)),
                @MeasurableSet (Finset V' × (V' → ℝ))
                  (MeasurableSpace.prod ⊤ inferInstance) E' →
                  pairedMeasure {ζ | ζ.2 ∈ E'} = ν' E') ∧
              Nonempty (SamplingSplitOutsideBlockerProductRealization
                (gamma / (Delta : ℝ)) φ sourceCoord pairedMeasure) := by
-- BODY
  classical
  intro V V' _ _ _ _ Delta gamma ν ν' hp hp1 ha hr ha' hr' φ S S' hφ hS'
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  obtain ⟨T, fT, s, t, hs, ht, hover, hcover⟩ := SamplingCopiedCommonTags φ S hφ
  letI : Fintype T := fT
  let m : Measure (T → ℝ × ℝ) := Measure.pi fun _ : T =>
    ((ENNReal.ofReal (gamma / (Delta : ℝ)) • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - gamma / (Delta : ℝ)) • Measure.dirac (0 : ℝ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1)))
  let D := SamplingSplitOutsideBlockerProductDecode s t
  have hDs := SamplingCoordinateDecodeMeasurable s
  have hDt := SamplingCoordinateDecodeMeasurable t
  have hD : Measurable D := hDs.prodMk hDt
  let paired := m.map D
  have hsource : paired.map Prod.fst = ν := by
    have hl := SamplingInjectiveCoordinateDecodeLaws s hs _ hp hp1
    have he : paired.map Prod.fst = m.map (fun q =>
        (Finset.univ.filter (fun v => (q (s v)).1 = 1), fun v => (q (s v)).2)) := by
      exact Measure.map_map measurable_fst hD
    rw [he]
    apply SamplingActivationRectangleMeasureUniqueness _ ν
      (fun A => ENNReal.ofReal ((gamma / (Delta : ℝ)) ^ A.card *
        (1 - gamma / (Delta : ℝ)) ^ (Fintype.card V - A.card)))
      (fun _ => ENNReal.ofReal_ne_top) hl.1
    · simpa only [Finset.card_univ] using ha
    · exact hl.2
    · exact hr
  have htarget : paired.map Prod.snd = ν' := by
    have hl := SamplingInjectiveCoordinateDecodeLaws t ht _ hp hp1
    have he : paired.map Prod.snd = m.map (fun q =>
        (Finset.univ.filter (fun v => (q (t v)).1 = 1), fun v => (q (t v)).2)) := by
      exact Measure.map_map measurable_snd hD
    rw [he]
    apply SamplingActivationRectangleMeasureUniqueness _ ν'
      (fun A => ENNReal.ofReal ((gamma / (Delta : ℝ)) ^ A.card *
        (1 - gamma / (Delta : ℝ)) ^ (Fintype.card V' - A.card)))
      (fun _ => ENNReal.ofReal_ne_top) hl.1
    · simpa only [Finset.card_univ] using ha'
    · exact hl.2
    · exact hr'
  have hsync (q : T → ℝ × ℝ) :
      (D q).2.1 ∩ S' = ((D q).1.1 ∩ S).image φ ∧
        ∀ v, v ∈ S → (D q).2.2 (φ v) = (D q).1.2 v := by
    have hc (v : V) (hv : v ∈ S) : s v = t (φ v) :=
      (hover v (φ v)).2 ⟨hv, rfl⟩
    constructor
    · ext w
      simp only [D, SamplingSplitOutsideBlockerProductDecode, Finset.mem_inter,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hS']
      constructor
      · rintro ⟨hw, v, hv, rfl⟩
        exact ⟨v, ⟨by simpa only [hc v hv] using hw, hv⟩, rfl⟩
      · rintro ⟨v, ⟨hvq, hv⟩, rfl⟩
        exact ⟨by simpa only [hc v hv] using hvq, v, hv, rfl⟩
    · intro v hv
      change (q (t (φ v))).2 = (q (s v)).2
      rw [hc v hv]
  have hbad : MeasurableSet {ζ : (Finset V × (V → ℝ)) ×
      (Finset V' × (V' → ℝ)) | ¬ (ζ.2.1 ∩ S' = (ζ.1.1 ∩ S).image φ ∧
        ∀ v, v ∈ S → ζ.2.2 (φ v) = ζ.1.2 v)} := by
    have haM : Measurable (fun ζ : (Finset V × (V → ℝ)) ×
        (Finset V' × (V' → ℝ)) => ζ.2.1 ∩ S' = (ζ.1.1 ∩ S).image φ) :=
      (measurable_of_finite (fun AB : Finset V × Finset V' =>
        AB.2 ∩ S' = (AB.1 ∩ S).image φ)).comp
          ((measurable_fst.comp measurable_fst).prodMk
            (measurable_fst.comp measurable_snd))
    apply Measurable.setOf
    apply Measurable.not
    apply haM.and
    apply Measurable.forall
    intro v
    apply measurable_const.imp
    exact measurableSet_setOf.mp
      (measurableSet_eq_fun ((measurable_pi_apply (φ v)).comp (measurable_snd.comp measurable_snd))
        ((measurable_pi_apply v).comp (measurable_snd.comp measurable_fst)))
  refine ⟨paired, ?_, ?_, ?_, ?_⟩
  · rw [show paired = m.map D from rfl, Measure.map_apply hD hbad]
    have hempty : D ⁻¹' {ζ | ¬ (ζ.2.1 ∩ S' = (ζ.1.1 ∩ S).image φ ∧
        ∀ v, v ∈ S → ζ.2.2 (φ v) = ζ.1.2 v)} = ∅ := by
      ext q
      exact iff_of_false (fun h => h (hsync q)) (fun h => h)
    rw [hempty, measure_empty]
  · intro E hE
    rw [← hsource, Measure.map_apply measurable_fst hE]
    rfl
  · intro E hE
    rw [← htarget, Measure.map_apply measurable_snd hE]
    rfl
  · exact ⟨{
      Tag := T
      finiteTag := fT
      sourceTag := s
      targetTag := t
      source_injective := hs
      target_injective := ht
      overlap := hover
      covers := hcover
      decode_measurable := hD
      measure_eq := rfl }⟩
