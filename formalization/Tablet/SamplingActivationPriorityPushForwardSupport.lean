import Tablet.SamplingFiniteProductPriorityLawExists

open BigOperators

universe u

-- [TABLET NODE: SamplingActivationPriorityPushForwardSupport]
theorem SamplingActivationPriorityPushForwardSupport :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
          ν Set.univ = 1 →
            ∃ μ : Finset V → ℝ,
              ((∀ S : Finset V, 0 ≤ μ S) ∧ (∑ S : Finset V, μ S) = 1) ∧
                (∀ S : Finset V,
                  ENNReal.ofReal (μ S) =
                    ν {ω |
                      S =
                        (Finset.univ.filter fun v : V =>
                          v ∈ ω.1 ∧
                            ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v)}) ∧
                ∀ S : Finset V, μ S ≠ 0 →
                  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v := by
-- BODY
  intro V _ _ G _ ν hν
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let out : Finset V × (V → ℝ) → Finset V :=
    fun ω =>
      Finset.univ.filter fun v : V =>
        v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v
  let μ : Finset V → ℝ := fun S => (ν {ω | S = out ω}).toReal
  have hfiber_meas : ∀ S : Finset V, MeasurableSet {ω | S = out ω} := by
    intro S
    classical
    have hset :
        ({ω : Finset V × (V → ℝ) | S = out ω}) =
          ⋂ v ∈ (Finset.univ : Finset V),
        if v ∈ S then
              {ω : Finset V × (V → ℝ) |
                v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v}
            else
              {ω : Finset V × (V → ℝ) |
                ¬ (v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hω v _hv
        by_cases hvS : v ∈ S
        · have hvout : v ∈ out ω := by
            simpa [hω] using hvS
          simpa [hvS, out] using hvout
        · have hvout : v ∉ out ω := by
            simpa [hω] using hvS
          simpa [hvS, out] using hvout
      · intro hω
        ext v
        by_cases hvS : v ∈ S
        · have hv := hω v (Finset.mem_univ v)
          simpa [out, hvS] using hv
        · have hv := hω v (Finset.mem_univ v)
          simpa [out, hvS] using hv
    rw [hset]
    refine MeasurableSet.biInter ?_ ?_
    · exact (Finset.finite_toSet _).countable
    · intro v hv
      by_cases hvS : v ∈ S
      · simp only [hvS, ↓reduceIte]
        measurability
      · simp only [hvS, ↓reduceIte]
        measurability
  refine ⟨μ, ?_, ?_, ?_⟩
  · constructor
    · intro S
      exact ENNReal.toReal_nonneg
    · have hfinite : ∀ S : Finset V, ν {ω | S = out ω} ≠ ⊤ := by
        intro S
        have hle : ν {ω | S = out ω} ≤ (1 : ENNReal) := by
          calc
            ν {ω | S = out ω} ≤ ν Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
            _ = 1 := hν
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have hcover :
          (Set.univ : Set (Finset V × (V → ℝ))) =
            ⋃ S ∈ (Finset.univ : Finset (Finset V)), {ω | S = out ω} := by
        ext ω
        simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_univ, Set.mem_setOf_eq, true_iff]
        exact ⟨out ω, trivial, rfl⟩
      have hpart :
          ν (Set.univ : Set (Finset V × (V → ℝ))) =
            ∑ S : Finset V, ν {ω | S = out ω} := by
        rw [hcover, MeasureTheory.measure_biUnion_finset]
        · intro S _ T _ hne
          rw [Function.onFun, Set.disjoint_left]
          intro ω hωS hωT
          exact hne (hωS.trans hωT.symm)
        · intro S _hS
          exact hfiber_meas S
      have hpart' : (∑ S : Finset V, ν {ω | S = out ω}) = 1 := by
        simpa [hν] using hpart.symm
      have htoReal :
          (∑ S : Finset V, ν {ω | S = out ω}).toReal =
            ∑ S : Finset V, (ν {ω | S = out ω}).toReal := by
        simpa using
          (ENNReal.toReal_sum
            (s := (Finset.univ : Finset (Finset V)))
            (f := fun S => ν {ω | S = out ω})
            (by
              intro S _hS
              exact hfinite S))
      calc
        (∑ S : Finset V, μ S)
            = (∑ S : Finset V, ν {ω | S = out ω}).toReal := by
                exact htoReal.symm
        _ = (1 : ENNReal).toReal := by rw [hpart']
        _ = 1 := ENNReal.toReal_one
  · intro S
    have hfinite : ν {ω | S = out ω} ≠ ⊤ := by
      have hle : ν {ω | S = out ω} ≤ (1 : ENNReal) := by
        calc
          ν {ω | S = out ω} ≤ ν Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
          _ = 1 := hν
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    exact ENNReal.ofReal_toReal hfinite
  · intro S hμS u v hu hv huv hAdj
    apply hμS
    change (ν {ω | S = out ω}).toReal = 0
    have hempty : {ω | S = out ω} = (∅ : Set (Finset V × (V → ℝ))) := by
      ext ω
      constructor
      · intro hω
        have huout : u ∈ out ω := by
          rw [← hω]
          exact hu
        have hvout : v ∈ out ω := by
          rw [← hω]
          exact hv
        have hu_surv :
            u ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u := by
          simpa [out] using huout
        have hv_surv :
            v ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v := by
          simpa [out] using hvout
        have hv_lt_hu : ω.2 v < ω.2 u := hu_surv.2 v hv_surv.1 hAdj
        have hu_lt_hv : ω.2 u < ω.2 v := hv_surv.2 u hu_surv.1 (G.symm hAdj)
        exact (lt_asymm hu_lt_hv hv_lt_hu).elim
      · intro hω
        exact False.elim hω
    simp [hempty]
