import Tablet.RandomIndependentSetSampling
import Tablet.SamplingFiniteProductMatchedCoordinateExtensionMass

open BigOperators

universe u

-- [TABLET NODE: SamplingRandomIndependentSetMatchedCoordinateExtensionLaw]
theorem SamplingRandomIndependentSetMatchedCoordinateExtensionLaw :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ, ∀ μ : Finset V → ℝ, ∀ μ' : Finset V' → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            RandomIndependentSetSampling G' Delta gamma μ' →
            0 ≤ gamma / (Delta : ℝ) →
            gamma / (Delta : ℝ) ≤ 1 →
            ∃ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ))
                  (MeasurableSpace.prod ⊤ inferInstance))
              (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ))
                  (MeasurableSpace.prod ⊤ inferInstance)),
              ν Set.univ = 1 ∧
              ν' Set.univ = 1 ∧
              ∀ (sourceC sourceD sourceA0 sourceAD sourceL sourceU sourceK : Finset V)
                (targetC targetD targetA0 targetAD targetL targetU targetK : Finset V')
                (sourceThreshold : V → ℝ) (targetThreshold : V' → ℝ),
                Disjoint sourceC sourceD →
                sourceA0 ⊆ sourceC → sourceAD ⊆ sourceD →
                sourceL ⊆ sourceC → sourceU ⊆ sourceC → sourceK ⊆ sourceD →
                Disjoint sourceL sourceU →
                Disjoint sourceK sourceU →
                Disjoint sourceL sourceK →
                (∀ v : V, v ∈ (sourceL ∪ sourceK) ∪ sourceU →
                  0 ≤ sourceThreshold v) →
                (∀ v : V, v ∈ (sourceL ∪ sourceK) ∪ sourceU →
                  sourceThreshold v ≤ 1) →
                Disjoint targetC targetD →
                targetA0 ⊆ targetC → targetAD ⊆ targetD →
                targetL ⊆ targetC → targetU ⊆ targetC → targetK ⊆ targetD →
                Disjoint targetL targetU →
                Disjoint targetK targetU →
                Disjoint targetL targetK →
                (∀ v' : V', v' ∈ (targetL ∪ targetK) ∪ targetU →
                  0 ≤ targetThreshold v') →
                (∀ v' : V', v' ∈ (targetL ∪ targetK) ∪ targetU →
                  targetThreshold v' ≤ 1) →
                (∀ sourceBase targetBase : ℝ,
                  0 ≤ sourceBase → 0 ≤ targetBase →
                    ENNReal.ofReal sourceBase =
                      ν {ω |
                        ω.1 ∩ sourceC = sourceA0 ∧
                          (∀ v : V, v ∈ sourceL → ω.2 v ≤ sourceThreshold v) ∧
                            ∀ v : V, v ∈ sourceU → sourceThreshold v < ω.2 v} →
                    ENNReal.ofReal targetBase =
                      ν' {ω |
                        ω.1 ∩ targetC = targetA0 ∧
                          (∀ v' : V', v' ∈ targetL →
                            ω.2 v' ≤ targetThreshold v') ∧
                            ∀ v' : V', v' ∈ targetU →
                              targetThreshold v' < ω.2 v'} →
                      sourceBase = targetBase) →
                ((gamma / (Delta : ℝ)) ^ sourceAD.card *
                    (1 - gamma / (Delta : ℝ)) ^ (sourceD.card - sourceAD.card) =
                  (gamma / (Delta : ℝ)) ^ targetAD.card *
                    (1 - gamma / (Delta : ℝ)) ^ (targetD.card - targetAD.card)) →
                ((∏ v : V,
                    if v ∈ sourceK then sourceThreshold v else 1) =
                  (∏ v' : V',
                    if v' ∈ targetK then targetThreshold v' else 1)) →
                ∃ sourceExt targetExt : ℝ,
                  0 ≤ sourceExt ∧ 0 ≤ targetExt ∧
                  ENNReal.ofReal sourceExt =
                    ν {ω |
                      ω.1 ∩ (sourceC ∪ sourceD) = sourceA0 ∪ sourceAD ∧
                        (∀ v : V, v ∈ sourceL ∪ sourceK →
                          ω.2 v ≤ sourceThreshold v) ∧
                          ∀ v : V, v ∈ sourceU →
                            sourceThreshold v < ω.2 v} ∧
                  ENNReal.ofReal targetExt =
                    ν' {ω |
                      ω.1 ∩ (targetC ∪ targetD) = targetA0 ∪ targetAD ∧
                        (∀ v' : V', v' ∈ targetL ∪ targetK →
                          ω.2 v' ≤ targetThreshold v') ∧
                          ∀ v' : V', v' ∈ targetU →
                            targetThreshold v' < ω.2 v'} ∧
                  sourceExt = targetExt := by
-- BODY
  classical
  intro V V' _ _ _ _ G _ G' _ Delta gamma μ μ' hsamp hsamp' hp0 hp1
  rcases hsamp with
    ⟨_hgamma, _hμ, ν, hν_univ, hν_atom, _hν_unit, hν_rect, _hν_vertex,
      _hpush, _hind⟩
  rcases hsamp' with
    ⟨_hgamma', _hμ', ν', hν'_univ, hν'_atom, _hν'_unit, hν'_rect,
      _hν'_vertex, _hpush', _hind'⟩
  refine ⟨ν, ν', hν_univ, hν'_univ, ?_⟩
  intro sourceC sourceD sourceA0 sourceAD sourceL sourceU sourceK
    targetC targetD targetA0 targetAD targetL targetU targetK sourceThreshold
    targetThreshold hsourceCD hsourceA0 hsourceAD hsourceL hsourceU hsourceK
    hsourceLU hsourceKU hsourceLK hsourceT0 hsourceT1 htargetCD htargetA0
    htargetAD htargetL htargetU htargetK htargetLU htargetKU htargetLK
    htargetT0 htargetT1 hbase hactivation hpriority
  exact
    SamplingFiniteProductMatchedCoordinateExtensionMass ν ν'
      (gamma / (Delta : ℝ)) sourceC sourceD sourceA0 sourceAD sourceL
      sourceU sourceK targetC targetD targetA0 targetAD targetL targetU
      targetK sourceThreshold targetThreshold hp0 hp1 hsourceCD hsourceA0
      hsourceAD hsourceL hsourceU hsourceK hsourceLU hsourceKU hsourceLK
      hsourceT0 hsourceT1 htargetCD htargetA0 htargetAD htargetL htargetU
      htargetK htargetLU htargetKU htargetLK htargetT0 htargetT1 hν_atom
      hν_rect hν'_atom hν'_rect hbase hactivation hpriority
