import Tablet.SamplingFiniteProductPriorityLawExists
import Tablet.SamplingFiniteCoordinateCellExtensionMass

open BigOperators

-- [TABLET NODE: SamplingFiniteProductPriorityCoordinateExtensionLaw]
theorem SamplingFiniteProductPriorityCoordinateExtensionLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (hgamma : 0 < gamma) (hle : gamma ≤ (Delta : ℝ)) :
    ∃ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
      ν Set.univ = 1 ∧
        (∀ A : Finset V,
          ν {ω | ω.1 = A} =
            ENNReal.ofReal
              ((gamma / (Delta : ℝ)) ^ A.card *
                (1 - gamma / (Delta : ℝ)) ^
                  ((Finset.univ : Finset V).card - A.card))) ∧
        (∀ A : Finset V, ∀ t : V → ℝ,
          (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
            ν {ω |
              ω.1 = A ∧
                ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
              ν {ω | ω.1 = A} *
                ENNReal.ofReal (∏ v : V, t v)) ∧
        ∀ (C D A0 AD L U K : Finset V) (t : V → ℝ),
          Disjoint C D →
          A0 ⊆ C → AD ⊆ D →
          L ⊆ C → U ⊆ C → K ⊆ D →
          Disjoint L U → Disjoint K U → Disjoint L K →
          (∀ v : V, v ∈ (L ∪ K) ∪ U → 0 ≤ t v) →
          (∀ v : V, v ∈ (L ∪ K) ∪ U → t v ≤ 1) →
          ∃ wBase wExt : ℝ,
            0 ≤ wBase ∧ 0 ≤ wExt ∧
            ENNReal.ofReal wBase =
              ν {ω |
                ω.1 ∩ C = A0 ∧
                  (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                    ∀ v : V, v ∈ U → t v < ω.2 v} ∧
            ENNReal.ofReal wExt =
              ν {ω |
                ω.1 ∩ (C ∪ D) = A0 ∪ AD ∧
                  (∀ v : V, v ∈ L ∪ K → ω.2 v ≤ t v) ∧
                    ∀ v : V, v ∈ U → t v < ω.2 v} ∧
            wExt =
              wBase *
                ((gamma / (Delta : ℝ)) ^ AD.card *
                  (1 - gamma / (Delta : ℝ)) ^ (D.card - AD.card)) *
                  (∏ v : V, if v ∈ K then t v else 1) := by
-- BODY
  classical
  rcases SamplingFiniteProductPriorityLawExists G Delta gamma hgamma hle with
    ⟨ν, hν_univ, hν_atom, _hν_unit, hν_rect, _hν_vertex⟩
  refine ⟨ν, hν_univ, hν_atom, hν_rect, ?_⟩
  intro C D A0 AD L U K t hCD hA0 hAD hL hU hK hLU hKU hLK ht0 ht1
  have hp0 : 0 ≤ gamma / (Delta : ℝ) := by
    exact div_nonneg (le_of_lt hgamma) (by exact_mod_cast Nat.zero_le Delta)
  have hDelta_pos : 0 < (Delta : ℝ) :=
    lt_of_lt_of_le hgamma hle
  have hp1 : gamma / (Delta : ℝ) ≤ 1 := by
    exact (div_le_one hDelta_pos).2 hle
  exact
    SamplingFiniteCoordinateCellExtensionMass ν (gamma / (Delta : ℝ))
      C D A0 AD L U K t hp0 hp1 hCD hA0 hAD hL hU hK hLU hKU hLK
      ht0 ht1 hν_atom hν_rect
