import Tablet.SamplingOneVertexAnalyticEstimate

open BigOperators

-- [TABLET NODE: SamplingOneVertexChangeVariables]
theorem SamplingOneVertexChangeVariables (Delta : ℕ) (gamma : ℝ)
    (hDelta : 0 < (Delta : ℝ)) :
    (gamma / (Delta : ℝ)) *
        (∫ a in (0 : ℝ)..1, (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta) =
      (1 / (Delta : ℝ)) *
        ∫ x in (0 : ℝ)..gamma, (1 - x / (Delta : ℝ)) ^ Delta := by
-- BODY
  let f : ℝ → ℝ := fun x => (1 - x / (Delta : ℝ)) ^ Delta
  by_cases hgamma : gamma = 0
  · subst gamma
    simp
  · have hsub :
        (∫ a in (0 : ℝ)..1, f (gamma - gamma * a)) =
          gamma⁻¹ * ∫ x in (0 : ℝ)..gamma, f x := by
      simpa using
        (intervalIntegral.integral_comp_sub_mul
          (f := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := gamma) (d := gamma) hgamma)
    have hleft_integrand :
        (fun a : ℝ => (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta) =
          fun a => f (gamma - gamma * a) := by
      funext a
      dsimp [f]
      congr 1
      have hDne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta
      field_simp [hDne]
    rw [hleft_integrand, hsub]
    dsimp [f]
    have hDne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta
    field_simp [hDne, hgamma]
