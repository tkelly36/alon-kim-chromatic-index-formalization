import Tablet.Preamble
import Tablet.FiniteAveragedCoordinateSubgaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory

-- [TABLET NODE: FiniteIndependentBoundedDifferences]
theorem FiniteIndependentBoundedDifferences
    {Ω A K : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype K]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : K → Ω → A) (hX : ∀ a, Measurable (X a)) (hind : iIndepFun X ν)
    (P : A → Prop) (hsupport : ∀ ω a, P (X a ω))
    (f : (K → A) → ℝ)
    (hchange : ∀ I J : K → A, (∀ a, P (I a)) → (∀ a, P (J a)) →
      ∀ a, (∀ b, b ≠ a → I b = J b) → |f I - f J| ≤ 1)
    (hm : 0 < Fintype.card K) (t : ℝ) (ht : 0 < t) :
    ν {ω | (∫ ω, f (fun a => X a ω) ∂ν) + t ≤ f (fun a => X a ω)} ≤
      ENNReal.ofReal (Real.exp (-2 * t^2 / Fintype.card K)) := by
-- BODY
  classical
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  haveI : Nonempty K := Fintype.card_pos_iff.mp hm
  let B := {v : A // P v}
  letI : Fintype B := Fintype.ofFinite B
  let b₀ : B := ⟨X (Classical.arbitrary K) (Classical.arbitrary Ω),
    hsupport _ _⟩
  let r : A → B := fun v => if h : P v then ⟨v, h⟩ else b₀
  let Y : K → Ω → B := fun a => r ∘ X a
  have hY (a : K) : Measurable (Y a) := (measurable_of_finite r).comp (hX a)
  have hval (a : K) (ω : Ω) : (Y a ω).val = X a ω := by
    simp [Y, r, hsupport ω a]
  have hindY : iIndepFun Y ν := hind.comp (fun _ => r) (fun _ => measurable_of_finite r)
  let p : K → Measure B := fun a => ν.map (Y a)
  haveI (a : K) : IsProbabilityMeasure (p a) :=
    Measure.isProbabilityMeasure_map (hY a).aemeasurable
  let μ := Measure.pi p
  let F : (K → B) → ℝ := fun I => f (fun a => (I a).val)
  let Z : Ω → (K → B) := fun ω a => Y a ω
  have hZ : Measurable Z := measurable_pi_lambda _ hY
  have hlaw : ν.map Z = μ :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun a => (hY a).aemeasurable)).mp hindY
  have hFZ (ω : Ω) : F (Z ω) = f (fun a => X a ω) := by
    change f (fun a => (Y a ω).val) = _
    congr 1
    funext a
    exact hval a ω
  have hmean : (∫ I, F I ∂μ) = ∫ ω, f (fun a => X a ω) ∂ν := by
    rw [← hlaw, integral_map hZ.aemeasurable
      (measurable_of_finite F).aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ hFZ)
  have htail : ν {ω | (∫ ω, f (fun a => X a ω) ∂ν) + t ≤
      f (fun a => X a ω)} = μ {I | (∫ I, F I ∂μ) + t ≤ F I} := by
    rw [← hlaw, Measure.map_apply hZ (Set.toFinite _).measurableSet]
    congr 1
    ext ω
    change _ ↔ (∫ I, F I ∂ν.map Z) + t ≤ F (Z ω)
    rw [hlaw, hmean, hFZ]
    rfl
  rw [htail]
  have hmgf : HasSubgaussianMGF (fun I => F I - ∫ J, F J ∂μ)
      ((Fintype.card K : NNReal) / 4) μ := by
    -- Split off one coordinate; the remaining slice bound is uniform in its value.
    have hfin : ∀ (n : ℕ) (p : Fin n → Measure B) [∀ i, IsProbabilityMeasure (p i)]
        (F : (Fin n → B) → ℝ),
        (∀ I J a, (∀ b, b ≠ a → I b = J b) → |F I - F J| ≤ 1) →
        HasSubgaussianMGF (fun I => F I - ∫ J, F J ∂Measure.pi p)
          ((n : NNReal) / 4) (Measure.pi p) := by
      intro n
      induction n with
      | zero =>
        intro p hp F hF
        have hc : ∀ I J : Fin 0 → B, I = J := fun _ _ => Subsingleton.elim _ _
        have hz : (fun I => F I - ∫ J, F J ∂Measure.pi p) = fun _ => 0 := by
          funext I
          simp_rw [hc _ I]
          simp
        rw [hz]
        simpa using (hasSubgaussianMGF_zero (μ := Measure.pi p))
      | succ n ih =>
        intro p hp F hF
        let q := Measure.pi (fun i : Fin n => p i.succ)
        let g := fun a (J : Fin n → B) => F (Fin.cons a J)
        let M := fun a => ∫ J, g a J ∂q
        have split (H : (Fin (n+1) → B) → ℝ) :
            (∫ I, H I ∂Measure.pi p) = ∫ a, ∫ J, H (Fin.cons a J) ∂q ∂p 0 := by
          rw [← (measurePreserving_piFinSuccAbove p 0).symm.integral_comp']
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.insertNth_zero, Fin.zero_succAbove]
          exact integral_prod _ ((MemLp.of_discrete (p := 1)).integrable le_rfl)
        have hs (a : B) := ih (fun i => p i.succ) (g a) (by
          intro I J i hij
          apply hF _ _ i.succ
          intro b
          refine Fin.cases ?_ (fun j hb => ?_) b
          · intro _; rfl
          · simp only [Fin.cons_succ]
            exact hij j (fun he => hb (congrArg Fin.succ he)))
        have ha := (FiniteAveragedCoordinateSubgaussian (p 0) q g (by
          intro a a' J
          apply hF _ _ 0
          intro b
          refine Fin.cases ?_ (fun j _ => ?_) b
          · intro hb; exact (hb rfl).elim
          · rfl)).2
        refine ⟨fun t => (MemLp.of_discrete (p := 1)).integrable le_rfl, ?_⟩
        intro t
        change (∫ I, Real.exp (t * (F I - ∫ J, F J ∂Measure.pi p)) ∂Measure.pi p) ≤ _
        rw [split, split F]
        change (∫ a, ∫ J, Real.exp (t * (g a J - ∫ a, M a ∂p 0)) ∂q ∂p 0) ≤ _
        have factor (a : B) :
            (∫ J, Real.exp (t * (g a J - ∫ a, M a ∂p 0)) ∂q) =
            Real.exp (t * (M a - ∫ a, M a ∂p 0)) *
              mgf (fun J => g a J - M a) q t := by
          simp only [mgf]
          rw [← integral_const_mul]
          congr 1
          funext J
          rw [← Real.exp_add]
          congr 1
          ring
        simp_rw [factor]
        calc
          _ ≤ ∫ a, Real.exp (t * (M a - ∫ a, M a ∂p 0)) *
              Real.exp (((n : NNReal) / 4 : NNReal) * t^2 / 2) ∂p 0 := by
            apply integral_mono ((MemLp.of_discrete (p := 1)).integrable le_rfl)
              ((MemLp.of_discrete (p := 1)).integrable le_rfl)
            intro a
            exact mul_le_mul_of_nonneg_left ((hs a).mgf_le t) (Real.exp_pos _).le
          _ = mgf (fun a => M a - ∫ a, M a ∂p 0) (p 0) t *
              Real.exp (((n : NNReal) / 4 : NNReal) * t^2 / 2) := integral_mul_const _ _
          _ ≤ Real.exp ((1 / 4 : NNReal) * t^2 / 2) *
              Real.exp (((n : NNReal) / 4 : NNReal) * t^2 / 2) :=
            mul_le_mul_of_nonneg_right (ha.mgf_le t) (Real.exp_pos _).le
          _ = _ := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring
    let e := (Fintype.equivFin K).symm
    let E := MeasurableEquiv.piCongrLeft (fun _ : K => B) e
    have hp := measurePreserving_piCongrLeft p e
    have hmean' : (∫ J, F (E J) ∂Measure.pi (fun i => p (e i))) =
        ∫ J, F J ∂μ := hp.integral_comp' F
    have h := hfin (Fintype.card K) (fun i => p (e i)) (fun I => F (E I)) (by
      intro I J a hij
      apply hchange _ _ (fun b => Subtype.property _) (fun b => Subtype.property _) (e a)
      intro b hb
      change (E I b).val = (E J b).val
      congr 1
      simp only [E, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
        eq_rec_constant]
      apply hij
      intro he
      apply hb
      exact e.symm.injective (by simpa using he))
    rw [hmean'] at h
    refine ⟨fun t => (MemLp.of_discrete (p := 1)).integrable le_rfl, ?_⟩
    intro t
    convert h.mgf_le t using 1
    exact (hp.integral_comp' (fun I => Real.exp (t * (F I - ∫ J, F J ∂μ)))).symm
  have hbound := hmgf.measure_ge_le ht.le
  have hevent : {I | t ≤ F I - ∫ J, F J ∂μ} =
      {I | (∫ J, F J ∂μ) + t ≤ F I} := by
    ext I
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hevent] at hbound
  have hexponent : -t ^ 2 / (2 * (((Fintype.card K : NNReal) / 4 : NNReal) : ℝ)) =
      -2 * t ^ 2 / (Fintype.card K : ℝ) := by
    push_cast
    ring
  rw [hexponent] at hbound
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact hbound
