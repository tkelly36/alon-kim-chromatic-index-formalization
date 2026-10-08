import Tablet.SamplingFiniteProductCandidateReplacementStep

open MeasureTheory
open BigOperators

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualOneStepMixedProductComparison]
theorem SamplingSplitOutsideBlockerActualOneStepMixedProductComparison :
    ∀ {V V' Ω α : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω]
      [Fintype α] [DecidableEq α] [Nonempty α],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ,
            ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
            ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
              0 ≤ gamma / (Delta : ℝ) →
              gamma / (Delta : ℝ) ≤ 1 →
              (∀ A : Finset V,
                ν {ξ | ξ.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V).card - A.card))) →
              (∀ A : Finset V, ∀ t : V → ℝ,
                (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν {ξ |
                    ξ.1 = A ∧
                      ∀ v : V, 0 ≤ ξ.2 v ∧ ξ.2 v ≤ t v} =
                    ν {ξ | ξ.1 = A} *
                      ENNReal.ofReal (∏ v : V, t v)) →
              (∀ A : Finset V',
                ν' {ξ | ξ.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V').card - A.card))) →
              (∀ A : Finset V', ∀ t : V' → ℝ,
                (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
                  ν' {ξ |
                    ξ.1 = A ∧
                      ∀ v' : V', 0 ≤ ξ.2 v' ∧ ξ.2 v' ≤ t v'} =
                    ν' {ξ | ξ.1 = A} *
                      ENNReal.ofReal (∏ v' : V', t v')) →
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
                  ∀ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                    (sourceCoord sourceExtensionCoord : Finset V)
                    (targetCommonCoord targetExtensionCoord targetCoord : Finset V')
                    (cell : Ω → Set (Finset V × (V → ℝ)))
                    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
                    (w : Ω → ℝ)
                    (sourceContext : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (targetContext : ℕ → Ω → Set (Finset V' × (V' → ℝ)))
                    (leftAdjacentEvent : ℕ → Ω → Set (Finset V × (V → ℝ)))
                    (rightAdjacentEvent : ℕ → Ω → Set (Finset V' × (V' → ℝ))),
                    Function.Injective zAt →
                    (∀ k : Fin n,
                      zAt k ∉ insert r X ∧
                        (∃ x : V, x ∈ X ∧ G.Adj x (zAt k))) →
                    (∀ k : Fin n, ∀ x : V,
                      x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) →
                    (∀ k : Fin n, (B k).Nonempty) →
                    (∀ k : Fin n, zAt k ∈ sourceExtensionCoord) →
                    Disjoint sourceCoord sourceExtensionCoord →
                    (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) →
                    targetCommonCoord = sourceCoord.image φ →
                    Disjoint targetCommonCoord targetExtensionCoord →
                    targetCoord = targetCommonCoord ∪ targetExtensionCoord →
                    (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) →
                    (∀ k : Fin n, ∀ x : V, ∀ hx : x ∈ X,
                      ∀ hz : zAt k ∉ insert r X ∧ G.Adj x (zAt k),
                        β ⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩ ∈ targetExtensionCoord) →
                    (∀ ω : Ω, 0 ≤ w ω) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) →
                    (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) →
                    ∀ (k : ℕ) (hk : k < n), ∀ ω : Ω,
                      sourceContext k ω =
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ η.1 ∧
                              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                                G.Adj x y → η.2 y < η.2 x) ∧
                              ∀ i : Fin n, k < (i : ℕ) → x ∈ B i →
                                ¬ (zAt i ∈ η.1 ∧
                                  η.2 x < η.2 (zAt i) ∧
                                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} →
                      targetContext k ω =
                        {η' : Finset V' × (V' → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            φ x ∈ η'.1 ∧
                              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                                G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                              ∀ i : Fin n, (i : ℕ) < k → x ∈ B i →
                                ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                                    η'.2 (φ x) <
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                      η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                        Set.Icc (0 : ℝ) 1)} →
                      leftAdjacentEvent k ω =
                        {η : Finset V × (V → ℝ) |
                          ∃ x : V, ∃ _hxX : x ∈ X,
                            x ∈ B ⟨k, hk⟩ ∧
                              ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                                η.2 x < η.2 (zAt ⟨k, hk⟩) ∧
                                  η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)} →
                      rightAdjacentEvent k ω =
                        {η' : Finset V' × (V' → ℝ) |
                          ∃ x : V, ∃ hxX : x ∈ X,
                            x ∈ B ⟨k, hk⟩ ∧
                              ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                                  G.Adj x (zAt ⟨k, hk⟩),
                                ¬ (β ⟨⟨x, hxX⟩,
                                  ⟨zAt ⟨k, hk⟩, hz⟩⟩ ∈ η'.1 ∧
                                  η'.2 (φ x) <
                                    η'.2 (β ⟨⟨x, hxX⟩,
                                      ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∧
                                    η'.2 (β ⟨⟨x, hxX⟩,
                                      ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∈
                                      Set.Icc (0 : ℝ) 1)} →
                      ∀ (candidateOf : α → V)
                        (hcandidate_mem :
                          ∀ a : α, candidateOf a ∈ B ⟨k, hk⟩)
                        (hcandidate_surj :
                          ∀ x : V, x ∈ B ⟨k, hk⟩ →
                            ∃ a : α, candidateOf a = x)
                        (priority : α → ℝ),
                        (∀ a : α, 0 ≤ priority a) →
                        (∀ a : α, priority a ≤ 1) →
                        (∀ a : α,
                          ∀ hx : candidateOf a ∈ X,
                          ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                              G.Adj (candidateOf a) (zAt ⟨k, hk⟩),
                            β ⟨⟨candidateOf a, hx⟩,
                              ⟨zAt ⟨k, hk⟩, hz⟩⟩ ∈
                                targetExtensionCoord) →
                        ∀ (η : @MeasureTheory.Measure (Bool × ℝ) ⊤)
                          (θ : @MeasureTheory.Measure (α → Bool × ℝ) ⊤),
                          η Set.univ = 1 →
                          η {ξ | ξ.1 = true ∧ ξ.2 ∈ Set.Icc (0 : ℝ) 1} =
                            ENNReal.ofReal (gamma / (Delta : ℝ)) →
                          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
                            η {ξ | ξ.1 = true ∧ 0 ≤ ξ.2 ∧ ξ.2 ≤ t} =
                              ENNReal.ofReal ((gamma / (Delta : ℝ)) * t)) →
                          θ Set.univ = 1 →
                          (∀ A : Finset α, ∀ t : α → ℝ,
                            (∀ a : α, a ∈ A → t a ∈ Set.Icc (0 : ℝ) 1) →
                              θ {ξ |
                                (∀ a : α, (ξ a).1 = decide (a ∈ A)) ∧
                                  ∀ a : α, a ∈ A →
                                    0 ≤ (ξ a).2 ∧ (ξ a).2 ≤ t a} =
                                ENNReal.ofReal
                                  ((gamma / (Delta : ℝ)) ^ A.card *
                                    (1 - gamma / (Delta : ℝ)) ^
                                      ((Finset.univ : Finset α).card - A.card) *
                                        ∏ a ∈ A, t a)) →
                          ∀ (Pleft Pright : ℝ),
                            0 ≤ Pleft →
                            0 ≤ Pright →
                            ENNReal.ofReal Pleft =
                              η {ξ |
                                ¬ (ξ.1 = true ∧
                                  (∀ a : α, priority a < ξ.2) ∧
                                    ξ.2 ∈ Set.Icc (0 : ℝ) 1)} →
                            ENNReal.ofReal Pright =
                              θ {ξ |
                                ∃ a : α,
                                  ¬ ((ξ a).1 = true ∧
                                    priority a < (ξ a).2 ∧
                                      (ξ a).2 ∈ Set.Icc (0 : ℝ) 1)} →
                            ENNReal.ofReal (w ω * Pleft) =
                              ν (leftAdjacentEvent k ω ∩
                                sourceContext k ω ∩ cell ω) →
                            ENNReal.ofReal (w ω * Pright) =
                              ν' (rightAdjacentEvent k ω ∩
                                targetContext k ω ∩ targetCell ω) →
                            Pleft ≤ Pright := by
-- BODY
  intro V V' Ω α _ _ _ _ _ _ _ _
  intro G _ G' _
  intro Delta gamma ν ν' hp0 hp1 _ _ _ _
  intro φ r X _ _ _ β _ _ _ _ _ _
  intro n zAt B sourceCoord sourceExtensionCoord targetCommonCoord targetExtensionCoord targetCoord
  intro cell targetCell w sourceContext targetContext leftAdjacentEvent rightAdjacentEvent
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro k hk ω _ _ _ _
  intro candidateOf hcandidate_mem hcandidate_surj priority hpriority0 hpriority1 hprivateCoord_current
  intro η θ hη_univ hη_active_unit hη_lower hθ_univ hθ_cylinder
  intro Pleft Pright hPleft_nonneg hPright_nonneg hPleft hPright _ _
  have hfinite :
      η {ξ |
          ¬ (ξ.1 = true ∧
            (∀ a : α, priority a < ξ.2) ∧
              ξ.2 ∈ Set.Icc (0 : ℝ) 1)} ≤
        θ {ξ |
          ∃ a : α,
            ¬ ((ξ a).1 = true ∧
              priority a < (ξ a).2 ∧
                (ξ a).2 ∈ Set.Icc (0 : ℝ) 1)} :=
    SamplingFiniteProductCandidateReplacementStep
      (p := gamma / (Delta : ℝ)) (π := priority) (η := η) (θ := θ)
      hp0 hp1 hpriority0 hpriority1 hη_univ hη_active_unit hη_lower
      hθ_univ hθ_cylinder
  have hofReal :
      ENNReal.ofReal Pleft ≤ ENNReal.ofReal Pright := by
    calc
      ENNReal.ofReal Pleft =
          η {ξ |
            ¬ (ξ.1 = true ∧
              (∀ a : α, priority a < ξ.2) ∧
                ξ.2 ∈ Set.Icc (0 : ℝ) 1)} := hPleft
      _ ≤ θ {ξ |
          ∃ a : α,
            ¬ ((ξ a).1 = true ∧
              priority a < (ξ a).2 ∧
                (ξ a).2 ∈ Set.Icc (0 : ℝ) 1)} := hfinite
      _ = ENNReal.ofReal Pright := hPright.symm
  exact (ENNReal.ofReal_le_ofReal_iff hPright_nonneg).mp hofReal
