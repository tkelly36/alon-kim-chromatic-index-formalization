import Tablet.Preamble

open BigOperators

universe u

-- [TABLET NODE: SamplingNonadjacentPairActivationAvoidanceProduct]
theorem SamplingNonadjacentPairActivationAvoidanceProduct :
    ∀ {V : Type u} [Fintype V],
      ∀ (S T : Finset V), ∀ Delta : ℕ, ∀ gamma x y : ℝ,
        gamma ≠ 0 →
          (∏ _w ∈ S,
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * (1 - x / gamma))) *
            (∏ _w ∈ T,
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * (1 - y / gamma))) =
              (∏ _w ∈ S, (1 - x / (Delta : ℝ))) *
                (∏ _w ∈ T, (1 - y / (Delta : ℝ))) := by
-- BODY
  classical
  intro V _ S T Delta gamma x y hgamma_ne
  have hx :
      ((1 - gamma / (Delta : ℝ)) +
          (gamma / (Delta : ℝ)) * (1 - x / gamma)) =
        (1 - x / (Delta : ℝ)) := by
    by_cases hDelta : (Delta : ℝ) = 0
    · simp [hDelta]
    · field_simp [hgamma_ne, hDelta]
      ring
  have hy :
      ((1 - gamma / (Delta : ℝ)) +
          (gamma / (Delta : ℝ)) * (1 - y / gamma)) =
        (1 - y / (Delta : ℝ)) := by
    by_cases hDelta : (Delta : ℝ) = 0
    · simp [hDelta]
    · field_simp [hgamma_ne, hDelta]
      ring
  simp [hx, hy]
