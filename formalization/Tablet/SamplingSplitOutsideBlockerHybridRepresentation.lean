import Tablet.RandomIndependentSetSampling
import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Tablet.SamplingSplitOutsideBlockerActualHybridWitnessAssembly
import Tablet.SamplingSplitOutsideBlockerRefinedAtomSupportedProductCell

open BigOperators

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerHybridRepresentation]
theorem SamplingSplitOutsideBlockerHybridRepresentation :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ,
            (∀ v : V, G.degree v = Delta) →
            (∀ v' : V', G'.degree v' = Delta) →
            ∀ μ : Finset V → ℝ, ∀ μ' : Finset V' → ℝ,
              RandomIndependentSetSampling G Delta gamma μ →
              RandomIndependentSetSampling G' Delta gamma μ' →
              ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              (∀ A : Finset V,
                ν {ω | ω.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V).card - A.card))) →
              (∀ A : Finset V, ∀ t : V → ℝ,
                (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν {ω |
                    ω.1 = A ∧
                      ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                    ν {ω | ω.1 = A} *
                      ENNReal.ofReal (∏ v : V, t v)) →
              (∀ A : Finset V',
                ν' {ω | ω.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V').card - A.card))) →
              (∀ A : Finset V', ∀ t : V' → ℝ,
                (∀ v : V', t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν' {ω |
                    ω.1 = A ∧
                      ∀ v : V', 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                    ν' {ω | ω.1 = A} *
                      ENNReal.ofReal (∏ v : V', t v)) →
              ∀ (φ : V → V') (r : V) (X : Finset V),
                Function.Injective φ →
                (∀ x : V, x ∈ X → G.Adj r x) →
                (∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
                  (G.Adj a b ↔ G'.Adj (φ a) (φ b))) →
                ∀ (β :
                  (Σ x : {x : V // x ∈ X},
                    {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
                  Function.Injective β →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                    ∀ y : V, y ∈ insert r X →
                      β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ≠ φ y) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      G'.Adj (φ x)
                      (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                    ∀ y : V, y ∈ X →
                      G'.Adj (φ y) (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) → y = x) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      ¬ G'.Adj (φ r)
                        (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X, ∀ w' : V',
                    G'.Adj (φ x) w' →
                      (∃ y : V, y ∈ insert r X ∧ w' = φ y ∧ G.Adj x y) ∨
                        ∃ z : V, ∃ hz : z ∉ insert r X ∧ G.Adj x z,
                          w' = β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) →
                  ∃ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (sourceCoord sourceExtensionCoord : Finset V)
                    (targetCommonCoord targetExtensionCoord targetCoord : Finset V')
                    (Ω : Type u) (_ : Fintype Ω)
                    (cell : Ω → Set (Finset V × (V → ℝ)))
                    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                    (w : Ω → ℝ)
                    (sourceStage : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (targetStage : ℕ → Ω → Set (Finset V' × (V' → ℝ)))
                    (P : ℕ → Ω → ℝ),
                    Function.Injective zAt ∧
                    (∀ k : Fin n,
                      zAt k ∉ insert r X ∧
                        (∃ x : V, x ∈ X ∧ G.Adj x (zAt k))) ∧
                    (∀ z : V, z ∉ insert r X →
                      (∃ x : V, x ∈ X ∧ G.Adj x z) →
                        ∃ k : Fin n, zAt k = z) ∧
                    (∀ k : Fin n, ∀ x : V,
                      x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) ∧
                    (∀ k : Fin n, zAt k ∈ sourceExtensionCoord) ∧
                    Disjoint sourceCoord sourceExtensionCoord ∧
                    (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) ∧
                    targetCommonCoord = sourceCoord.image φ ∧
                    Disjoint targetCommonCoord targetExtensionCoord ∧
                    targetCoord = targetCommonCoord ∪ targetExtensionCoord ∧
                    (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) ∧
                    (∀ k : Fin n, ∀ x : V, ∀ hx : x ∈ X,
                      ∀ hz : zAt k ∉ insert r X ∧ G.Adj x (zAt k),
                        β ⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩ ∈ targetExtensionCoord) ∧
                    (∀ ω : Ω, 0 ≤ w ω) ∧
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) ∧
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) ∧
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) ∧
                    (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
                      Disjoint (targetCell ω₁) (targetCell ω₂)) ∧
                    (∀ η : Finset V × (V → ℝ),
                      (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
                        ∃ ω : Ω, η ∈ cell ω) ∧
                    (∀ η : Finset V' × (V' → ℝ),
                      (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1) →
                        ∃ ω : Ω, η ∈ targetCell ω) ∧
                    ν {η | ¬ (∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1)} = 0 ∧
                    ν' {η | ¬ (∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1)} = 0 ∧
                    (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
                      sourceStage j ω =
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ η.1 ∧
                              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                G.Adj x y → η.2 y < η.2 x) ∧
                              ∀ i : Fin n, j ≤ (i : ℕ) → x ∈ B i →
                                ¬ (zAt i ∈ η.1 ∧
                                  η.2 x < η.2 (zAt i) ∧
                                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) ∧
                    (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
                      targetStage j ω =
                        {η' : Finset V' × (V' → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            φ x ∈ η'.1 ∧
                              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                              ∀ i : Fin n, (i : ℕ) < j → x ∈ B i →
                                ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                    η'.2 (φ x) <
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                        Set.Icc (0 : ℝ) 1)}) ∧
                    (∀ j : ℕ, ∀ ω : Ω, 0 ≤ P j ω) ∧
                    (∀ j : ℕ, ∀ ω : Ω, w ω = 0 → P j ω = 0) ∧
                    (∀ ω : Ω,
                      ENNReal.ofReal (w ω * P 0 ω) =
                        ν ({η |
                          ((Finset.univ.filter fun z : V =>
                            z ∈ η.1 ∧
                              ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                              X).Nonempty} ∩ cell ω)) ∧
                    (∀ ω : Ω,
                      ENNReal.ofReal (w ω * P n ω) =
                        ν' ({η |
                          ((Finset.univ.filter fun z : V' =>
                            z ∈ η.1 ∧
                              ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                              X.image φ).Nonempty} ∩ targetCell ω)) ∧
                    ENNReal.ofReal (∑ ω : Ω, w ω * P 0 ω) =
                      ν {η |
                        ((Finset.univ.filter fun z : V =>
                          z ∈ η.1 ∧
                            ∀ y : V, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
                            X).Nonempty} ∧
                    ENNReal.ofReal (∑ ω : Ω, w ω * P n ω) =
                      ν' {η |
                        ((Finset.univ.filter fun z : V' =>
                          z ∈ η.1 ∧
                            ∀ y : V', y ∈ η.1 → G'.Adj z y → η.2 y < η.2 z) ∩
                            X.image φ).Nonempty} ∧
                    (∀ k : ℕ, k < n → ∀ ω : Ω, P k ω ≤ P (k + 1) ω) := by
-- BODY
  classical
  intro V V' _ _ _ _ G _ G' _ Delta gamma _hG_regular _hG'_regular μ μ'
    hsamp _hsamp' ν ν' hνact hνprio hν'act hν'prio φ r X hφ hX hadj β
    hβinj hβfresh hβadj hβunique hβnotr hβcover
  have hγnonneg : 0 ≤ gamma / (Delta : ℝ) := by
    by_cases hDelta : Delta = 0
    · simp [hDelta]
    · have hDelta_pos : 0 < (Delta : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hDelta
      have hgamma_pos : 0 < gamma := hsamp.1
      positivity
  have hγle : gamma / (Delta : ℝ) ≤ 1 := by
    by_cases hDelta : Delta = 0
    · simp [hDelta]
    · have hDelta_nat_pos : 0 < Delta := Nat.pos_of_ne_zero hDelta
      have hDelta_pos : 0 < (Delta : ℝ) := by
        exact_mod_cast hDelta_nat_pos
      have hgamma_le :
          gamma ≤ (Delta : ℝ) :=
        RandomIndependentSetSamplingGammaLeDelta G ⟨r⟩ hDelta_nat_pos hsamp
      exact (div_le_one hDelta_pos).2 hgamma_le
  exact
    SamplingSplitOutsideBlockerActualHybridWitnessAssembly G G' Delta gamma ν ν'
      hγnonneg hγle hνact hνprio hν'act hν'prio φ r X hφ hX hadj β
      hβinj hβfresh hβadj hβunique hβnotr hβcover
