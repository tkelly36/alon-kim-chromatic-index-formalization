import Tablet.SamplingNonadjacentPairChamberIntegral

open BigOperators

universe u

-- [TABLET NODE: SamplingRegularGraphSamplingLawExists]
theorem SamplingRegularGraphSamplingLawExists :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, ∀ gamma : ℝ,
            (∀ v : V, G.degree v = Delta) →
            0 < gamma → gamma ≤ (Delta : ℝ) →
            ∃ μ : Finset V → ℝ, RandomIndependentSetSampling G Delta gamma μ := by
-- BODY
  classical
  intro V _ _ G _ Delta gamma hregular hgamma_pos hgamma_le
  obtain ⟨ν, hν_univ, hactivation, hcube, hrect, hsingle⟩ :=
    SamplingFiniteProductPriorityLawExists G Delta gamma hgamma_pos hgamma_le
  obtain ⟨μ, hμ_basic, hpush, hindependent⟩ :=
    SamplingActivationPriorityPushForwardSupport G ν hν_univ
  refine ⟨μ, ?_⟩
  refine ⟨hgamma_pos, ?_⟩
  constructor
  · constructor
    · exact hμ_basic.1
    · constructor
      · exact hμ_basic.2
      · intro hregular' u v huv hnonadj
        exact
          SamplingNonadjacentPairChamberIntegral G Delta gamma μ ν hgamma_pos hgamma_le
            hμ_basic.1 hregular' hν_univ hactivation hcube hrect hsingle hpush
            u v huv hnonadj
  · exact ⟨ν, hν_univ, hactivation, hcube, hrect, hsingle, hpush, hindependent⟩
