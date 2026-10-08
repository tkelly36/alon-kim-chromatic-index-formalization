import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Tablet.SamplingOneVertexActivationDecisionProduct
import Tablet.SamplingOneVertexActivationIntegralSum
import Tablet.SamplingOneVertexAnalyticEstimate
import Tablet.SamplingOneVertexChangeVariables
import Tablet.SamplingOneVertexComparisonPartition
import Tablet.SamplingOneVertexFixedThresholdProduct
import Tablet.SamplingOneVertexNeighborRectangle
import Tablet.SamplingOneVertexOutputMembership
import Tablet.SamplingOneVertexPriorityRectangle
import Tablet.SamplingOneVertexPrioritySlice
import Tablet.SamplingOneVertexPrioritySliceExact
import Tablet.SamplingOneVertexPushForwardEvent
import Tablet.SamplingFiniteSetActivationPartition

open BigOperators

-- [TABLET NODE: SamplingOneVertexEstimate]
theorem SamplingOneVertexEstimate :
    ∀ᶠ Delta : ℕ in Filter.atTop, ∀ gamma : ℝ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ v : V,
              (∑ S : Finset V, if v ∈ S then μ S else 0) =
                  (1 / (Delta : ℝ)) *
                    ∫ x in (0 : ℝ)..gamma, (1 - x / (Delta : ℝ)) ^ Delta ∧
                abs ((∑ S : Finset V, if v ∈ S then μ S else 0) -
                    (1 - Real.exp (-gamma)) / (Delta : ℝ)) ≤
                    2 / (Delta : ℝ)^2 := by
-- BODY
  classical
  filter_upwards [Filter.eventually_ge_atTop 1] with Delta hDelta
  intro gamma V _ _ G _ hregular μ hsamp v
  have hD : 0 < Delta := by omega
  have hDr : 0 < (Delta : ℝ) := by exact_mod_cast hD
  have hgamma := hsamp.1
  have hle := RandomIndependentSetSamplingGammaLeDelta G ⟨v⟩ hD hsamp
  rcases hsamp with ⟨_, hμ, ν, hν, hact, hsupp, _, hint, hpush, _⟩
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let mass : Finset V → ℝ := fun A =>
    (gamma / (Delta : ℝ)) ^ A.card *
      (1 - gamma / (Delta : ℝ)) ^ ((Finset.univ : Finset V).card - A.card)
  let integ : Finset V → ℝ := fun A => ∫ a in (0 : ℝ)..1,
    a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)
  have hm (A : Finset V) : 0 ≤ mass A := by
    dsimp [mass]
    apply mul_nonneg (pow_nonneg (div_nonneg hgamma.le hDr.le) _)
    exact pow_nonneg (sub_nonneg.mpr ((div_le_one hDr).mpr hle)) _
  have hi (A : Finset V) : 0 ≤ integ A := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact pow_nonneg hx.1 _
  have hfixed (A : Finset V) (hv : v ∈ A) :
      ν {ω | ω.1 = A ∧ ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v} =
        ENNReal.ofReal (mass A * integ A) := by
    have hs : MeasurableSet {ω : Finset V × (V → ℝ) |
        ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v} := by measurability
    have heq := MeasureTheory.Measure.measure_inter_eq_of_measure_eq hs (hsupp A)
      (fun ω h => h.1) (by rw [hsupp A, hact A]; exact ENNReal.ofReal_ne_top)
    have heq' :
        ν {ω | ω.1 = A ∧
          (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v} =
        ν {ω | ω.1 = A ∧ ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v} := by
      simpa only [← Set.setOf_and, and_assoc] using heq
    rw [← heq', hint A v hv, hact A, ENNReal.ofReal_mul (hm A)]
  have hsurvival : (∑ S : Finset V, if v ∈ S then μ S else 0) =
      ∑ A : Finset V, if v ∈ A then mass A * integ A else 0 := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (Finset.sum_nonneg fun S _ => by split_ifs; exact hμ.1 S; exact le_rfl)
      (Finset.sum_nonneg fun A _ => by split_ifs; exact mul_nonneg (hm A) (hi A); exact le_rfl)).mp
    rw [SamplingOneVertexPushForwardEvent G μ ν hμ.1 hpush v]
    have hp := (SamplingFiniteSetActivationPartition G ν {v}).1
    simp only [Finset.singleton_subset_iff, Finset.mem_singleton, forall_eq] at hp
    rw [hp, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro A _
      by_cases hv : v ∈ A
      · simp only [hv, if_true]
        exact hfixed A hv
      · simp [hv]
    · intro A _
      split_ifs
      · exact mul_nonneg (hm A) (hi A)
      · exact le_rfl
  have hidentity : (∑ S : Finset V, if v ∈ S then μ S else 0) =
      (1 / (Delta : ℝ)) * ∫ x in (0 : ℝ)..gamma, (1 - x / (Delta : ℝ)) ^ Delta := by
    rw [hsurvival]
    exact (SamplingOneVertexActivationIntegralSum G Delta gamma v hregular).trans
      (SamplingOneVertexChangeVariables Delta gamma hDr)
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  exact SamplingOneVertexAnalyticEstimate Delta gamma hDr hgamma.le hle
