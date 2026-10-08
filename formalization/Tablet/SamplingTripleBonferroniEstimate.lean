import Tablet.LocalBParameter
import Tablet.RandomIndependentSetSampling
import Tablet.SamplingFiniteBonferroniUnionBound
import Tablet.SamplingFirstMomentNeighborSetBound
import Tablet.SamplingInducedNeighborhoodLocalBParameter
import Tablet.SamplingOneVertexEstimate
import Tablet.SamplingPairTripleBonferroniCore

open BigOperators

-- [TABLET NODE: SamplingTripleBonferroniEstimate]
theorem SamplingTripleBonferroniEstimate (eta : ℝ) (heta : 0 < eta) :
    ∃ Delta0 gamma0 : ℕ, ∀ Delta : ℕ, ∀ gamma : ℝ,
      Delta0 ≤ Delta → (gamma0 : ℝ) ≤ gamma →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              (∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
                ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w) →
              (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
                SamplingInducedNeighborhoodLocalBParameter G Delta r X + eta := by
-- BODY
  classical
  have heta_half : 0 < eta / 2 := by positivity
  rcases SamplingPairTripleBonferroniCore (eta / 2) heta_half with
    ⟨DeltaCore, gammaCore, hcore⟩
  rcases SamplingFirstMomentNeighborSetBound (eta / 2) heta_half with
    ⟨DeltaFirst, gammaFirst, hfirst⟩
  refine ⟨max DeltaCore DeltaFirst, max gammaCore gammaFirst, ?_⟩
  intro Delta gamma hDelta hgamma V _instFintype _instDecEq G _instDecRel hregular μ hsampling
    r X hX hclean
  have hDeltaCore : DeltaCore ≤ Delta := (le_max_left _ _).trans hDelta
  have hDeltaFirst : DeltaFirst ≤ Delta := (le_max_right _ _).trans hDelta
  have hgamma_real : (max gammaCore gammaFirst : ℝ) ≤ gamma := by
    simpa [Nat.cast_max] using hgamma
  have hgammaCore : (gammaCore : ℝ) ≤ gamma := by
    exact (by exact_mod_cast le_max_left gammaCore gammaFirst : (gammaCore : ℝ) ≤
      (max gammaCore gammaFirst : ℝ)).trans hgamma_real
  have hgammaFirst : (gammaFirst : ℝ) ≤ gamma := by
    exact (by exact_mod_cast le_max_right gammaCore gammaFirst : (gammaFirst : ℝ) ≤
      (max gammaCore gammaFirst : ℝ)).trans hgamma_real
  have hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S := hsampling.2.1.1
  let J2 : Finset (Finset V) :=
    (Finset.univ.filter fun P : Finset V =>
      P.card = 2 ∧ P ⊆ X ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
  let J3 : Finset (Finset V) :=
    (Finset.univ.filter fun P : Finset V =>
      P.card = 3 ∧ P ⊆ X ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
  have hbonf :
      (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
        (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) -
          (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) +
            (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) :=
    SamplingFiniteBonferroniUnionBound μ hμ_nonneg X
  have hfirst_bound :
      (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) ≤
        (X.card : ℝ) / (Delta : ℝ) + eta / 2 :=
    hfirst Delta gamma hDeltaFirst hgammaFirst G hregular μ hsampling r X hX
  have hcore_bound :
      (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) -
          (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) ≥
        (J2.card : ℝ) / (Delta : ℝ)^2 -
          (J3.card : ℝ) / (Delta : ℝ)^3 - eta / 2 := by
    simpa [J2, J3] using
      (hcore Delta gamma hDeltaCore hgammaCore G hregular μ hsampling r X hX hclean)
  have hparam :
      SamplingInducedNeighborhoodLocalBParameter G Delta r X =
        (X.card : ℝ) / (Delta : ℝ) - (J2.card : ℝ) / (Delta : ℝ)^2 +
          (J3.card : ℝ) / (Delta : ℝ)^3 := by
    simp [SamplingInducedNeighborhoodLocalBParameter, J2, J3]
  calc
    (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0)
        ≤ (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) -
          (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) +
            (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) := hbonf
    _ ≤ SamplingInducedNeighborhoodLocalBParameter G Delta r X + eta := by
      rw [hparam]
      linarith
