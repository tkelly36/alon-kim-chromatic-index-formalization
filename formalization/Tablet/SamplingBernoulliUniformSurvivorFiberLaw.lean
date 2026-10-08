import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

-- [TABLET NODE: SamplingBernoulliUniformSurvivorFiberLaw]
theorem SamplingBernoulliUniformSurvivorFiberLaw
    {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (K : Finset A) (q : A → ℝ) (hq : ∀ a ∈ K, q a ∈ Set.Icc (0 : ℝ) 1) :
    let ρ := (ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))
    let μ := Measure.pi (fun _ : Option A => ρ)
    let L := {f : Option A → ℝ × ℝ | ∃ a ∈ K,
      ¬ ((f none).1 = 1 ∧ q a < (f none).2 ∧ (f none).2 ∈ Set.Icc (0 : ℝ) 1)}
    let R := {f : Option A → ℝ × ℝ | ∃ a ∈ K,
      ¬ ((f (some a)).1 = 1 ∧ q a < (f (some a)).2 ∧
        (f (some a)).2 ∈ Set.Icc (0 : ℝ) 1)}
    MeasurableSet L ∧ MeasurableSet R ∧ μ Set.univ = 1 ∧
      (K = ∅ → μ L = 0) ∧
      (∀ a ∈ K, (∀ b ∈ K, q b ≤ q a) →
        μ L = ENNReal.ofReal (1 - p * (1 - q a))) ∧
      μ R = ENNReal.ofReal (1 - ∏ a ∈ K, (p * (1 - q a))) ∧
      μ L ≤ μ R := by
-- BODY
  classical
  dsimp only
  let β := ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
  let υ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let ρ := β.prod υ
  let μ := Measure.pi (fun _ : Option A => ρ)
  let F := fun a => {z : ℝ × ℝ | z.1 = 1 ∧ q a < z.2 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1}
  have hβ : β Set.univ = 1 := by
    simp [β, ← ENNReal.ofReal_add hp (sub_nonneg.mpr hp')]
  have hυ : υ Set.univ = 1 := by simp [υ]
  letI : IsProbabilityMeasure β := ⟨hβ⟩
  letI : IsProbabilityMeasure υ := ⟨hυ⟩
  letI : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (β.prod υ))
  have hF : ∀ a, MeasurableSet (F a) := by
    intro a
    exact (measurable_fst (measurableSet_singleton 1)).inter
      ((measurable_snd measurableSet_Ioi).inter (measurable_snd measurableSet_Icc))
  have hmass : ∀ a ∈ K, ρ (F a) = ENNReal.ofReal (p * (1 - q a)) := by
    intro a ha
    have hset : F a = ({1} : Set ℝ) ×ˢ Set.Ioc (q a) 1 := by
      ext z
      simp only [F, Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff,
        Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h, hq, h0, h1⟩; exact ⟨h, hq, h1⟩
      · rintro ⟨h, hlt, h1⟩; exact ⟨h, hlt, (hq a ha).1.trans hlt.le, h1⟩
    rw [hset, Measure.prod_prod]
    have hi : Set.Ioc (q a) 1 ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (q a) 1 :=
      Set.inter_eq_left.mpr (fun _ h => ⟨(hq a ha).1.trans h.1.le, h.2⟩)
    simp [β, υ, Measure.restrict_apply measurableSet_Ioc, hi,
      ← ENNReal.ofReal_mul hp]
  let L := {f : Option A → ℝ × ℝ | ∃ a ∈ K, f none ∉ F a}
  let R := {f : Option A → ℝ × ℝ | ∃ a ∈ K, f (some a) ∉ F a}
  change MeasurableSet L ∧ MeasurableSet R ∧ μ Set.univ = 1 ∧ _
  have hL : MeasurableSet L := by
    have hh : MeasurableSet (⋃ a ∈ K,
        ((fun f : Option A → ℝ × ℝ => f none) ⁻¹' F a)ᶜ) :=
      .biUnion K.finite_toSet.countable (fun a _ => ((hF a).preimage (measurable_pi_apply none)).compl)
    convert hh using 1
    ext f
    simp [L]
  have hR : MeasurableSet R := by
    have hh : MeasurableSet (⋃ a ∈ K,
        ((fun f : Option A → ℝ × ℝ => f (some a)) ⁻¹' F a)ᶜ) :=
      .biUnion K.finite_toSet.countable (fun a _ => ((hF a).preimage (measurable_pi_apply (some a))).compl)
    convert hh using 1
    ext f
    simp [R]
  have hmax : ∀ a ∈ K, (∀ b ∈ K, q b ≤ q a) →
      μ L = ENNReal.ofReal (1 - p * (1 - q a)) := by
    intro a ha hqa
    have he : L = (Function.eval none ⁻¹' F a)ᶜ := by
      ext f
      simp only [L, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Function.eval]
      constructor
      · rintro ⟨b, hb, hf⟩ hfa
        exact hf ⟨hfa.1, (hqa b hb).trans_lt hfa.2.1, hfa.2.2⟩
      · exact fun hf => ⟨a, ha, hf⟩
    rw [he, measure_compl ((hF a).preimage (measurable_pi_apply none)) (measure_ne_top _ _)]
    rw [(measurePreserving_eval (fun _ : Option A => ρ) none).measure_preimage (hF a).nullMeasurableSet,
      hmass a ha]
    simp only [measure_univ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (mul_nonneg hp (sub_nonneg.mpr (hq a ha).2))]
  have hrmass : μ R = ENNReal.ofReal (1 - ∏ a ∈ K, (p * (1 - q a))) := by
    let D : Option A → Set (ℝ × ℝ) := fun i => match i with
      | none => Set.univ
      | some a => if a ∈ K then F a else Set.univ
    have he : Rᶜ = Set.univ.pi D := by
      ext f
      simp only [R, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, Set.mem_pi,
        Set.mem_univ, true_implies]
      constructor
      · intro h i; cases i with
        | none => trivial
        | some a => simpa [D] using h a
      · intro h a ha; simpa [D, ha] using h (some a)
    have hm : μ Rᶜ = ENNReal.ofReal (∏ a ∈ K, (p * (1 - q a))) := by
      rw [he, Measure.pi_pi]
      simp only [D, Fintype.prod_option, measure_univ, one_mul, apply_ite]
      rw [Finset.prod_ite_mem, Finset.univ_inter]
      rw [ENNReal.ofReal_prod_of_nonneg (fun a ha => mul_nonneg hp (sub_nonneg.mpr (hq a ha).2))]
      exact Finset.prod_congr rfl hmass
    rw [← compl_compl R, measure_compl hR.compl (measure_ne_top _ _), hm]
    simp only [measure_univ, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (Finset.prod_nonneg (fun a ha => mul_nonneg hp (sub_nonneg.mpr (hq a ha).2)))]
  refine ⟨hL, hR, measure_univ, ?_, hmax, hrmass, ?_⟩
  · intro he; simp [L, he]
  · change μ L ≤ μ R
    by_cases he : K = ∅
    · simp [L, he]
    · obtain ⟨a, ha, hqa⟩ := K.exists_max_image q (Finset.nonempty_iff_ne_empty.mpr he)
      rw [hmax a ha hqa, hrmass]
      apply ENNReal.ofReal_le_ofReal
      have hb : ∀ b ∈ K, 0 ≤ p * (1 - q b) ∧ p * (1 - q b) ≤ 1 := by
        intro b hb
        constructor
        · exact mul_nonneg hp (sub_nonneg.mpr (hq b hb).2)
        · nlinarith [(hq b hb).1, (hq b hb).2]
      have hh : ∏ b ∈ K.erase a, (p * (1 - q b)) ≤ 1 :=
        Finset.prod_le_one (fun b hb' => (hb b (Finset.mem_of_mem_erase hb')).1)
          (fun b hb' => (hb b (Finset.mem_of_mem_erase hb')).2)
      have hh' := mul_le_mul_of_nonneg_left hh (hb a ha).1
      rw [mul_one, Finset.mul_prod_erase K (fun b => p * (1 - q b)) ha] at hh'
      linarith
