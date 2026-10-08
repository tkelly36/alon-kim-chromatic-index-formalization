import Tablet.SamplingCoordinateDecodeMeasurable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

-- [TABLET NODE: SamplingInjectiveCoordinateDecodeLaws]
theorem SamplingInjectiveCoordinateDecodeLaws
    {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
    (s : V → T) (hs : Function.Injective s) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let μ := @Measure.map (T → ℝ × ℝ) (Finset V × (V → ℝ))
      inferInstance (MeasurableSpace.prod ⊤ inferInstance)
      (fun q => (Finset.univ.filter (fun v => (q (s v)).1 = 1),
        fun v => (q (s v)).2))
      (Measure.pi fun _ : T =>
        ((ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
          ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (∀ A : Finset V, μ {ω | ω.1 = A} =
      ENNReal.ofReal (p ^ A.card * (1 - p) ^ (Fintype.card V - A.card))) ∧
    (∀ (A : Finset V) (t : V → ℝ), (∀ v, t v ∈ Set.Icc (0 : ℝ) 1) →
      μ {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
        μ {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  let β := ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
  let υ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let ρ := β.prod υ
  let m := Measure.pi (fun _ : T => ρ)
  let d := fun q : T → ℝ × ℝ =>
    (Finset.univ.filter (fun v => (q (s v)).1 = 1), fun v => (q (s v)).2)
  have hd : Measurable d := SamplingCoordinateDecodeMeasurable s
  have hβ : β Set.univ = 1 := by
    simp [β, ← ENNReal.ofReal_add hp (sub_nonneg.mpr hp1)]
  have hυ : υ Set.univ = 1 := by simp [υ]
  letI : IsProbabilityMeasure β := ⟨hβ⟩
  letI : IsProbabilityMeasure υ := ⟨hυ⟩
  letI : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (β.prod υ))
  have hrect (D : V → Set (ℝ × ℝ)) :
      m {q | ∀ v, q (s v) ∈ D v} = ∏ v, ρ (D v) := by
    let E : T → Set (ℝ × ℝ) := fun i =>
      if h : ∃ v, s v = i then D h.choose else Set.univ
    have hE (v : V) : E (s v) = D v := by
      dsimp only [E]
      rw [dif_pos ⟨v, rfl⟩]
      congr 1
      exact hs (Exists.choose_spec (show ∃ w, s w = s v from ⟨v, rfl⟩))
    have he : {q : T → ℝ × ℝ | ∀ v, q (s v) ∈ D v} = Set.univ.pi E := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h i
        by_cases hi : ∃ v, s v = i
        · dsimp only [E]
          rw [dif_pos hi]
          simpa only [hi.choose_spec] using h hi.choose
        · simp [E, hi]
      · intro h v
        simpa only [hE] using h (s v)
    rw [he, Measure.pi_pi]
    calc
      ∏ i, ρ (E i) = ∏ i ∈ Finset.univ.image s, ρ (E i) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        have hi' : ¬ ∃ v, s v = i := by simpa using hi
        simp [E, hi']
      _ = ∏ v, ρ (D v) := by
        rw [Finset.prod_image (fun _ _ _ _ h => hs h)]
        simp only [hE]
  let C : Finset V → V → Set ℝ := fun A v => if v ∈ A then {1} else {1}ᶜ
  have hC (A : Finset V) (v : V) :
      β (C A v) = if v ∈ A then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
    by_cases hv : v ∈ A <;> simp [C, hv, β]
  have hact (A : Finset V) (q : T → ℝ × ℝ) :
      (d q).1 = A ↔ ∀ v, (q (s v)).1 ∈ C A v := by
    simp only [d, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro v
    by_cases hv : v ∈ A <;> simp [C, hv]
  have hprod (A : Finset V) :
      (∏ v, β (C A v)) =
        ENNReal.ofReal (p ^ A.card * (1 - p) ^ (Fintype.card V - A.card)) := by
    simp only [hC]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hf : Finset.univ.filter (fun v : V => v ∉ A) = Finset.univ \ A := by
      ext v
      simp
    rw [hf]
    simp [Finset.card_sdiff, ← ENNReal.ofReal_pow hp,
      ← ENNReal.ofReal_pow (sub_nonneg.mpr hp1), ← ENNReal.ofReal_mul (pow_nonneg hp _)]
  have hmeas (A : Finset V) : MeasurableSet {ω : Finset V × (V → ℝ) | ω.1 = A} :=
    measurable_fst (measurableSet_singleton A)
  have hmass (A : Finset V) : (m.map d) {ω | ω.1 = A} =
      ENNReal.ofReal (p ^ A.card * (1 - p) ^ (Fintype.card V - A.card)) := by
    rw [Measure.map_apply hd (hmeas A)]
    have he : d ⁻¹' {ω | ω.1 = A} =
        {q | ∀ v, q (s v) ∈ C A v ×ˢ Set.univ} := by
      ext q
      simpa only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
        Set.mem_univ, and_true] using hact A q
    rw [he, hrect]
    simpa only [ρ, Measure.prod_prod, measure_univ, mul_one] using hprod A
  change (∀ A, (m.map d) {ω | ω.1 = A} = _) ∧ _
  refine ⟨hmass, ?_⟩
  intro A t ht
  have hm : MeasurableSet {ω : Finset V × (V → ℝ) |
      ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} := by
    refine (hmeas A).inter ?_
    change MeasurableSet {ω : Finset V × (V → ℝ) | ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun v =>
      (measurable_pi_apply v |>.comp measurable_snd) measurableSet_Icc)
  rw [Measure.map_apply hd hm]
  have he : d ⁻¹' {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
      {q | ∀ v, q (s v) ∈ C A v ×ˢ Set.Icc 0 (t v)} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hact, Set.mem_prod, Set.mem_Icc]
    exact forall_and.symm
  rw [he, hrect]
  have hu (v : V) : υ (Set.Icc 0 (t v)) = ENNReal.ofReal (t v) := by
    have hi : Set.Icc 0 (t v) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (t v) :=
      Set.inter_eq_left.mpr (fun _ h => ⟨h.1, h.2.trans (ht v).2⟩)
    simp [υ, Measure.restrict_apply measurableSet_Icc, hi]
  simp only [ρ, Measure.prod_prod, hu, Finset.prod_mul_distrib]
  rw [hprod, hmass, ENNReal.ofReal_prod_of_nonneg (fun v _ => (ht v).1)]
