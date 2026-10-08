import Tablet.Preamble

open BigOperators

-- [TABLET NODE: FiniteProbabilityMass]
def FiniteProbabilityMass {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : Prop :=
-- BODY
  (∀ ω : Ω, 0 ≤ μ ω) ∧ (∑ ω, μ ω) = 1
