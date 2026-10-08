import Tablet.Preamble
import Tablet.BernoulliChernoffRateLowerBound
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory

-- [TABLET NODE: FiniteIndependentBernoulliCountTail]
theorem FiniteIndependentBernoulliCountTail
    {Ω A K : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype K]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : K → Ω → A) (hX : ∀ a, Measurable (X a)) (hind : iIndepFun X ν)
    (s : Finset K) (R : K → A → Prop) [∀ a, DecidablePred (R a)]
    (t : ℝ) (ht : 0 < t) :
    let Z := fun ω => ((s.filter fun a => R a (X a ω)).card : ℝ)
    let μ := ∫ ω, Z ω ∂ν
    0 ≤ μ ∧ μ ≤ s.card ∧
    ν {ω | μ + t ≤ Z ω} ≤
      ENNReal.ofReal (Real.exp (-(t^2 / (2 * μ + t)))) := by
-- BODY
  classical
  let B : K → Ω → ℝ := fun a ω => if R a (X a ω) then 1 else 0
  have hBm : ∀ a, Measurable (B a) := fun a =>
    (measurable_of_finite (fun x => if R a x then (1 : ℝ) else 0)).comp (hX a)
  have hB0 : ∀ a ω, 0 ≤ B a ω := by intros; simp only [B]; split <;> norm_num
  have hB1 : ∀ a ω, B a ω ≤ 1 := by intros; simp only [B]; split <;> norm_num
  have hBi : ∀ a, Integrable (B a) ν := fun a =>
    (integrable_const (1 : ℝ)).mono' (hBm a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hB0 a ω)]; exact hB1 a ω)
  let Z : Ω → ℝ := fun ω => ((s.filter fun a => R a (X a ω)).card : ℝ)
  have hZ : Z = fun ω => ∑ a ∈ s, B a ω := by
    funext ω
    exact (Finset.sum_boole (fun a => R a (X a ω)) s).symm
  have hZm : Measurable Z := by rw [hZ]; exact Finset.measurable_sum _ (fun a _ => hBm a)
  have hZi : Integrable Z ν := by rw [hZ]; exact integrable_finset_sum _ (fun a _ => hBi a)
  have hZ0 : ∀ ω, 0 ≤ Z ω := by intro ω; exact Nat.cast_nonneg _
  have hZn : ∀ ω, Z ω ≤ s.card := by
    intro ω
    dsimp [Z]
    exact_mod_cast Finset.card_filter_le s (fun a => R a (X a ω))
  let μ := ∫ ω, Z ω ∂ν
  have hμ0 : 0 ≤ μ := integral_nonneg hZ0
  have hμn : μ ≤ s.card := by
    simpa using integral_mono hZi (integrable_const (s.card : ℝ)) hZn
  refine ⟨hμ0, hμn, ?_⟩
  change ν {ω | μ + t ≤ Z ω} ≤ _
  by_cases hμ : μ = 0
  · have hz : Z =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hZ0 hZi).1 hμ
    have hn : ν {ω | μ + t ≤ Z ω} = 0 := by
      apply measure_mono_null (t := {ω | Z ω ≠ 0})
      · intro ω hω
        simp only [Set.mem_setOf_eq] at *
        intro hh
        rw [hμ, hh] at hω
        linarith
      · exact ae_iff.mp hz
    rw [hn]
    exact zero_le _
  have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
  have hBind : iIndepFun B ν := hind.comp
    (fun a x => if R a x then (1 : ℝ) else 0) (fun _ => measurable_of_finite _)
  have hmgf : ∀ u : ℝ, mgf Z ν u ≤ Real.exp (μ * (Real.exp u - 1)) := by
    as_aux_lemma =>
    intro u
    have hsingle : ∀ a, mgf (B a) ν u = 1 + (∫ ω, B a ω ∂ν) * (Real.exp u - 1) := by
      intro a
      unfold mgf
      have hf : (fun ω => Real.exp (u * B a ω)) =
          (fun ω => (1 : ℝ) + B a ω * (Real.exp u - 1)) := by
        funext ω
        simp only [B]
        split <;> simp
      rw [hf, integral_add (integrable_const _) ((hBi a).mul_const _), integral_mul_const]
      simp
    have hmean : μ = ∑ a ∈ s, ∫ ω, B a ω ∂ν := by
      dsimp [μ]
      rw [hZ, integral_finset_sum _ (fun a _ => hBi a)]
    have hZfun : Z = ∑ a ∈ s, B a := by
      rw [hZ]
      funext ω
      simp only [Finset.sum_apply]
    rw [hZfun, hBind.mgf_sum hBm]
    calc
      ∏ a ∈ s, mgf (B a) ν u ≤
          ∏ a ∈ s, Real.exp ((∫ ω, B a ω ∂ν) * (Real.exp u - 1)) := by
        apply Finset.prod_le_prod
        · intro a _; exact integral_nonneg (fun ω => (Real.exp_pos _).le)
        · intro a _
          rw [hsingle]
          linarith [Real.add_one_le_exp ((∫ ω, B a ω ∂ν) * (Real.exp u - 1))]
      _ = Real.exp (μ * (Real.exp u - 1)) := by
        rw [← Real.exp_sum, ← Finset.sum_mul, ← hmean]
  let u := Real.log (1 + t / μ)
  have hrpos : 0 < t / μ := div_pos ht hμpos
  have hu : 0 < u := Real.log_pos (by linarith)
  have hexp : Real.exp u = 1 + t / μ := Real.exp_log (by linarith)
  have hei : Integrable (fun ω => Real.exp (u * Z ω)) ν :=
    (integrable_const (Real.exp (u * s.card))).mono'
      (hZm.const_mul u).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hZn ω) hu.le))
  have htail := measure_ge_le_exp_mul_mgf (μ + t) hu.le hei
  have hbound : ν.real {ω | μ + t ≤ Z ω} ≤
      Real.exp (-(t ^ 2 / (2 * μ + t))) := by
    calc
      _ ≤ Real.exp (-u * (μ + t)) * Real.exp (μ * (Real.exp u - 1)) :=
        htail.trans (mul_le_mul_of_nonneg_left (hmgf u) (Real.exp_pos _).le)
      _ = Real.exp (-u * (μ + t) + μ * (Real.exp u - 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hr := BernoulliChernoffRateLowerBound (t / μ) (div_nonneg ht.le hμpos.le)
        have hm := mul_le_mul_of_nonneg_left hr hμpos.le
        rw [hexp]
        dsimp [u]
        have heq : μ * ((t / μ) ^ 2 / (2 + t / μ)) = t ^ 2 / (2 * μ + t) := by
          field_simp
        have hmul : μ * ((1 + t / μ) * Real.log (1 + t / μ) - t / μ) =
            (μ + t) * Real.log (1 + t / μ) - t := by
          field_simp
        rw [heq, hmul] at hm
        have htμ : μ * (t / μ) = t := mul_div_cancel₀ t hμ
        nlinarith
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans_le
    (ENNReal.ofReal_le_ofReal hbound)
