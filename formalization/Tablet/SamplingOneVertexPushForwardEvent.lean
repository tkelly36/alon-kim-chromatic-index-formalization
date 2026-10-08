import Tablet.SamplingFiniteSetPushForwardEvent

open BigOperators

-- [TABLET NODE: SamplingOneVertexPushForwardEvent]
theorem SamplingOneVertexPushForwardEvent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : Finset V → ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S)
    (hpush : ∀ S : Finset V,
      ENNReal.ofReal (μ S) =
        ν {ω |
          S =
            (Finset.univ.filter fun u : V =>
              u ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u)})
    (v : V) :
    ENNReal.ofReal (∑ S : Finset V, if v ∈ S then μ S else 0) =
        ν {ω |
          v ∈
            (Finset.univ.filter fun u : V =>
              u ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u)} := by
-- BODY
  simpa only [Finset.singleton_subset_iff] using
    SamplingFiniteSetPushForwardEvent G μ ν hμ_nonneg hpush {v}
