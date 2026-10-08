import Tablet.SamplingFiniteSetPushForwardEvent
import Tablet.SamplingPairOutputMembership

open BigOperators

-- [TABLET NODE: SamplingPairPushForwardEvent]
theorem SamplingPairPushForwardEvent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : Finset V → ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S)
    (hpush : ∀ S : Finset V,
      ENNReal.ofReal (μ S) =
        ν {ω |
          S =
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)})
    (u v : V) :
    ENNReal.ofReal (∑ S : Finset V, if ({u, v} : Finset V) ⊆ S then μ S else 0) =
        ν {ω |
          ({u, v} : Finset V) ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} := by
-- BODY
  exact SamplingFiniteSetPushForwardEvent G μ ν hμ_nonneg hpush {u, v}
