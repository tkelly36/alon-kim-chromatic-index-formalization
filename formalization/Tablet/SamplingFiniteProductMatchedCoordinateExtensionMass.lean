import Tablet.SamplingFiniteCoordinateCellExtensionMass
import Tablet.SamplingFiniteProductMatchedCoordinateExtensionTransport

open BigOperators

-- [TABLET NODE: SamplingFiniteProductMatchedCoordinateExtensionMass]
theorem SamplingFiniteProductMatchedCoordinateExtensionMass
    {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ)
    (sourceC sourceD sourceA0 sourceAD sourceL sourceU sourceK : Finset V)
    (targetC targetD targetA0 targetAD targetL targetU targetK : Finset V')
    (sourceThreshold : V → ℝ) (targetThreshold : V' → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsourceCD : Disjoint sourceC sourceD)
    (hsourceA0 : sourceA0 ⊆ sourceC) (hsourceAD : sourceAD ⊆ sourceD)
    (hsourceL : sourceL ⊆ sourceC) (hsourceU : sourceU ⊆ sourceC)
    (hsourceK : sourceK ⊆ sourceD)
    (hsourceLU : Disjoint sourceL sourceU)
    (hsourceKU : Disjoint sourceK sourceU)
    (hsourceLK : Disjoint sourceL sourceK)
    (hsourceT0 : ∀ v : V, v ∈ (sourceL ∪ sourceK) ∪ sourceU → 0 ≤ sourceThreshold v)
    (hsourceT1 : ∀ v : V, v ∈ (sourceL ∪ sourceK) ∪ sourceU → sourceThreshold v ≤ 1)
    (htargetCD : Disjoint targetC targetD)
    (htargetA0 : targetA0 ⊆ targetC) (htargetAD : targetAD ⊆ targetD)
    (htargetL : targetL ⊆ targetC) (htargetU : targetU ⊆ targetC)
    (htargetK : targetK ⊆ targetD)
    (htargetLU : Disjoint targetL targetU)
    (htargetKU : Disjoint targetK targetU)
    (htargetLK : Disjoint targetL targetK)
    (htargetT0 : ∀ v' : V', v' ∈ (targetL ∪ targetK) ∪ targetU → 0 ≤ targetThreshold v')
    (htargetT1 : ∀ v' : V', v' ∈ (targetL ∪ targetK) ∪ targetU → targetThreshold v' ≤ 1)
    (hν_atom : ∀ A : Finset V,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)))
    (hν_rect : ∀ A : Finset V, ∀ s : V → ℝ,
      (∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v : V, s v))
    (hν'_atom : ∀ A : Finset V',
      ν' {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V').card - A.card)))
    (hν'_rect : ∀ A : Finset V', ∀ s : V' → ℝ,
      (∀ v' : V', s v' ∈ Set.Icc (0 : ℝ) 1) →
        ν' {ω |
          ω.1 = A ∧ ∀ v' : V', 0 ≤ ω.2 v' ∧ ω.2 v' ≤ s v'} =
          ν' {ω | ω.1 = A} * ENNReal.ofReal (∏ v' : V', s v'))
    (hbase :
      ∀ sourceBase targetBase : ℝ,
        0 ≤ sourceBase → 0 ≤ targetBase →
          ENNReal.ofReal sourceBase =
            ν {ω |
              ω.1 ∩ sourceC = sourceA0 ∧
                (∀ v : V, v ∈ sourceL → ω.2 v ≤ sourceThreshold v) ∧
                  ∀ v : V, v ∈ sourceU → sourceThreshold v < ω.2 v} →
          ENNReal.ofReal targetBase =
            ν' {ω |
              ω.1 ∩ targetC = targetA0 ∧
                (∀ v' : V', v' ∈ targetL → ω.2 v' ≤ targetThreshold v') ∧
                  ∀ v' : V', v' ∈ targetU → targetThreshold v' < ω.2 v'} →
            sourceBase = targetBase)
    (hactivation :
      p ^ sourceAD.card * (1 - p) ^ (sourceD.card - sourceAD.card) =
        p ^ targetAD.card * (1 - p) ^ (targetD.card - targetAD.card))
    (hpriority :
      (∏ v : V, if v ∈ sourceK then sourceThreshold v else 1) =
        (∏ v' : V', if v' ∈ targetK then targetThreshold v' else 1)) :
    ∃ sourceExt targetExt : ℝ,
      0 ≤ sourceExt ∧ 0 ≤ targetExt ∧
      ENNReal.ofReal sourceExt =
        ν {ω |
          ω.1 ∩ (sourceC ∪ sourceD) = sourceA0 ∪ sourceAD ∧
            (∀ v : V, v ∈ sourceL ∪ sourceK → ω.2 v ≤ sourceThreshold v) ∧
              ∀ v : V, v ∈ sourceU → sourceThreshold v < ω.2 v} ∧
      ENNReal.ofReal targetExt =
        ν' {ω |
          ω.1 ∩ (targetC ∪ targetD) = targetA0 ∪ targetAD ∧
            (∀ v' : V', v' ∈ targetL ∪ targetK → ω.2 v' ≤ targetThreshold v') ∧
              ∀ v' : V', v' ∈ targetU → targetThreshold v' < ω.2 v'} ∧
      sourceExt = targetExt := by
-- BODY
  rcases
      SamplingFiniteCoordinateCellExtensionMass ν p sourceC sourceD sourceA0
        sourceAD sourceL sourceU sourceK sourceThreshold hp0 hp1 hsourceCD
        hsourceA0 hsourceAD hsourceL hsourceU hsourceK hsourceLU hsourceKU
        hsourceLK hsourceT0 hsourceT1 hν_atom hν_rect with
    ⟨sourceBase, sourceExt, hsourceBase_nonneg, hsourceExt_nonneg,
      hsourceBase_mass, hsourceExt_mass, hsourceFormula⟩
  rcases
      SamplingFiniteCoordinateCellExtensionMass ν' p targetC targetD targetA0
        targetAD targetL targetU targetK targetThreshold hp0 hp1 htargetCD
        htargetA0 htargetAD htargetL htargetU htargetK htargetLU htargetKU
        htargetLK htargetT0 htargetT1 hν'_atom hν'_rect with
    ⟨targetBase, targetExt, htargetBase_nonneg, htargetExt_nonneg,
      htargetBase_mass, htargetExt_mass, htargetFormula⟩
  have hbase_eq : sourceBase = targetBase :=
    hbase sourceBase targetBase hsourceBase_nonneg htargetBase_nonneg
      hsourceBase_mass htargetBase_mass
  have htargetFormula' :
      targetExt =
        sourceBase *
          (p ^ targetAD.card * (1 - p) ^ (targetD.card - targetAD.card)) *
            (∏ v' : V', if v' ∈ targetK then targetThreshold v' else 1) := by
    simpa [hbase_eq] using htargetFormula
  have heq :
      sourceExt = targetExt :=
    SamplingFiniteProductMatchedCoordinateExtensionTransport p sourceBase sourceExt
      targetExt sourceAD sourceD sourceK targetAD targetD targetK sourceThreshold
      targetThreshold hsourceFormula htargetFormula' hactivation hpriority
  exact
    ⟨sourceExt, targetExt, hsourceExt_nonneg, htargetExt_nonneg,
      hsourceExt_mass, htargetExt_mass, heq⟩
