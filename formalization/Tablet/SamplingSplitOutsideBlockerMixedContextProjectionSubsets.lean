import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMixedContextProjectionSubsets]
theorem SamplingSplitOutsideBlockerMixedContextProjectionSubsets :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj]
        (φ : V → V') (r : V) (X : Finset V)
        (n : ℕ) (zAt : Fin n → V)
        (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
        (β :
          (Σ x : {x : V // x ∈ X},
            {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
        (B : Fin n → Finset V)
        (sharedUnchangedContext :
          ℕ → Ω →
            Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))),
        (∀ k : Fin n, ∀ x : V,
          x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) →
        (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
          sharedUnchangedContext k ω =
            {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
              ∃ x : V, ∃ hxX : x ∈ X,
                G.Adj x (zAt ⟨k, hk⟩) ∧
                  x ∈ ζ.1.1 ∧
                  φ x ∈ ζ.2.1 ∧
                  (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
                    G.Adj x y → ζ.1.2 y < ζ.1.2 x) ∧
                  (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
                    G.Adj x y → ζ.2.2 (φ y) < ζ.2.2 (φ x)) ∧
                  (∀ i : Fin n, (i : ℕ) < k →
                    ∀ hzAdj : G.Adj x (zAt i),
                      ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈
                          ζ.2.1 ∧
                        ζ.2.2 (φ x) <
                          ζ.2.2
                            (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                        ζ.2.2
                          (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                          Set.Icc (0 : ℝ) 1)) ∧
                  (∀ i : Fin n, k < (i : ℕ) → G.Adj x (zAt i) →
                    ¬ (zAt i ∈ ζ.1.1 ∧
                      ζ.1.2 x < ζ.1.2 (zAt i) ∧
                        ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}) →
        ∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
          ∀ η : Finset V × (V → ℝ),
          ∀ η' : Finset V' × (V' → ℝ),
            (η, η') ∈ sharedUnchangedContext k ω →
              (η ∈
                {η : Finset V × (V → ℝ) |
                  ∃ x : V, ∃ hxX : x ∈ X,
                    x ∈ B ⟨k, hk⟩ ∧
                      x ∈ η.1 ∧
                      (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                        G.Adj x y → η.2 y < η.2 x) ∧
                      ∀ i : Fin n, k < (i : ℕ) → x ∈ B i →
                        ¬ (zAt i ∈ η.1 ∧
                          η.2 x < η.2 (zAt i) ∧
                            η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}) ∧
              (η' ∈
                {η' : Finset V' × (V' → ℝ) |
                  ∃ x : V, ∃ hxX : x ∈ X,
                    x ∈ B ⟨k, hk⟩ ∧
                      φ x ∈ η'.1 ∧
                      (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                        G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                      ∀ i : Fin n, (i : ℕ) < k → x ∈ B i →
                        ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                          ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                            η'.2 (φ x) <
                              η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                              η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                Set.Icc (0 : ℝ) 1)}) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ φ r X n zAt hOutside β B
    sharedUnchangedContext hB hshared k hk ω η η' hmem
  rw [hshared k hk ω] at hmem
  rcases hmem with
    ⟨x, hxX, hxAdjCurrent, hxη, hφxη', hsourceCore, htargetCore,
      hpastPrivate, hfutureCommon⟩
  have hxBk : x ∈ B ⟨k, hk⟩ := by
    exact (hB ⟨k, hk⟩ x).2 ⟨hxX, hxAdjCurrent⟩
  constructor
  · refine ⟨x, hxX, hxBk, hxη, hsourceCore, ?_⟩
    intro i hki hxiB
    have hAdj : G.Adj x (zAt i) := ((hB i x).1 hxiB).2
    exact hfutureCommon i hki hAdj
  · refine ⟨x, hxX, hxBk, hφxη', htargetCore, ?_⟩
    intro i hik hxiB hz
    exact hpastPrivate i hik hz.2
