import Tablet.Preamble
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory

-- [TABLET NODE: FiniteAveragedCoordinateSubgaussian]
theorem FiniteAveragedCoordinateSubgaussian
    {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (p : Measure A) (q : Measure B) [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    (g : A → B → ℝ) (hchange : ∀ a a' b, |g a b - g a' b| ≤ 1) :
    let M := fun a => ∫ b, g a b ∂q
    (∃ u : ℝ, ∀ a, M a ∈ Set.Icc u (u + 1)) ∧
      HasSubgaussianMGF (fun a => M a - ∫ a', M a' ∂p) (1 / 4) p := by
-- BODY
  classical
  let M := fun a => ∫ b, g a b ∂q
  have hi (a : A) : Integrable (g a) q := (MemLp.of_discrete (p := 1)).integrable le_rfl
  have hdiff (a a' : A) : M a - M a' ≤ 1 := by
    rw [show M a - M a' = ∫ b, g a b - g a' b ∂q from
      (integral_sub (hi a) (hi a')).symm]
    calc
      _ ≤ ∫ _ : B, (1 : ℝ) ∂q := integral_mono ((hi a).sub (hi a'))
        (integrable_const 1) (fun b => (le_abs_self _).trans (hchange a a' b))
      _ = 1 := by simp
  haveI : Nonempty A := nonempty_of_isProbabilityMeasure p
  obtain ⟨a₀, hmin⟩ := Finite.exists_min M
  have hrange (a : A) : M a ∈ Set.Icc (M a₀) (M a₀ + 1) :=
    ⟨hmin a, by have := hdiff a a₀; linarith⟩
  refine ⟨⟨M a₀, hrange⟩, ?_⟩
  have hM : Integrable M p := (MemLp.of_discrete (p := 1)).integrable le_rfl
  have hzero : (∫ a, M a - ∫ a', M a' ∂p ∂p) = 0 := by
    rw [integral_sub hM (integrable_const _)]
    simp
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun a => M a - ∫ a', M a' ∂p)
    (a := M a₀ - ∫ a', M a' ∂p) (b := M a₀ + 1 - ∫ a', M a' ∂p)
    (measurable_of_finite _).aemeasurable
    (ae_of_all _ fun a => ⟨sub_le_sub_right (hrange a).1 _,
      sub_le_sub_right (hrange a).2 _⟩) hzero
  have hwidth : (M a₀ + 1 - ∫ a', M a' ∂p) - (M a₀ - ∫ a', M a' ∂p) = 1 := by ring
  norm_num [hwidth] at h
  exact h
