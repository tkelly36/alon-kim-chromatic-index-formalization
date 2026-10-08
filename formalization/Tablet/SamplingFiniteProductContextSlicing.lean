import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

-- [TABLET NODE: SamplingFiniteProductContextSlicing]
theorem SamplingFiniteProductContextSlicing
    {T : Type*} [Fintype T] [DecidableEq T]
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (J : Finset T) :
    let ρ := (ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))
    let μ := Measure.pi (fun _ : T => ρ)
    let τ := Measure.pi (fun _ : {i : T // i ∉ J} => ρ)
    let κ := Measure.pi (fun _ : {i : T // i ∈ J} => ρ)
    let splice := fun (t : {i : T // i ∉ J} → ℝ × ℝ)
      (c : {i : T // i ∈ J} → ℝ × ℝ) (i : T) =>
        if hi : i ∈ J then c ⟨i, hi⟩ else t ⟨i, hi⟩
    Measurable (fun tc : (({i : T // i ∉ J} → ℝ × ℝ) ×
      ({i : T // i ∈ J} → ℝ × ℝ)) => splice tc.1 tc.2) ∧
      Measurable (fun t => splice t (fun _ => (0, 0))) ∧
      μ Set.univ = 1 ∧ τ Set.univ = 1 ∧ κ Set.univ = 1 ∧
      (∀ᵐ t ∂τ, ∀ i, (t i).2 ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ E : Set (T → ℝ × ℝ), MeasurableSet E →
        Measurable (fun t => κ {c | splice t c ∈ E}) ∧
          μ E = ∫⁻ t, κ {c | splice t c ∈ E} ∂τ) := by
-- BODY
  classical
  dsimp only
  let β := ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
  let υ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let ρ := β.prod υ
  let μ := Measure.pi (fun _ : T => ρ)
  let τ := Measure.pi (fun _ : {i : T // i ∉ J} => ρ)
  let κ := Measure.pi (fun _ : {i : T // i ∈ J} => ρ)
  have hβ : β Set.univ = 1 := by
    simp [β, ← ENNReal.ofReal_add hp (sub_nonneg.mpr hp')]
  have hυ : υ Set.univ = 1 := by simp [υ]
  letI : IsProbabilityMeasure β := ⟨hβ⟩
  letI : IsProbabilityMeasure υ := ⟨hυ⟩
  letI : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (β.prod υ))
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : T => ℝ × ℝ)
    (fun i => i ∈ J)
  let F := fun tc : (({i : T // i ∉ J} → ℝ × ℝ) ×
      ({i : T // i ∈ J} → ℝ × ℝ)) => e.symm (Prod.swap tc)
  have hsplit : MeasurePreserving e μ (κ.prod τ) := by
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : T => ρ)
      (fun i => i ∈ J) using 1
    congr 1
    dsimp only [κ]
    congr 1
    exact Subsingleton.elim _ _
  have hF : MeasurePreserving F (τ.prod κ) μ :=
    (hsplit.symm e).comp (Measure.measurePreserving_swap (μ := τ) (ν := κ))
  change Measurable F ∧ Measurable (fun t => F (t, fun _ => (0, 0))) ∧
    μ Set.univ = 1 ∧ τ Set.univ = 1 ∧ κ Set.univ = 1 ∧ _
  refine ⟨hF.measurable, hF.measurable.comp (measurable_id.prodMk measurable_const),
    measure_univ, measure_univ, measure_univ, ?_, ?_⟩
  · have hs : ∀ᵐ z ∂ρ, z.2 ∈ Set.Icc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
    exact ae_all_iff.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : {i : T // i ∉ J} => ρ) (i := i)) hs)
  · intro E hE
    have hpre : MeasurableSet (F ⁻¹' E) := hE.preimage hF.measurable
    refine ⟨measurable_measure_prodMk_left hpre, ?_⟩
    exact (hF.measure_preimage hE.nullMeasurableSet).symm.trans (Measure.prod_apply hpre)
