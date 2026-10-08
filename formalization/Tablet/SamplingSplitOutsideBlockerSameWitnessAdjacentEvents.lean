import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerSameWitnessAdjacentEvents]
theorem SamplingSplitOutsideBlockerSameWitnessAdjacentEvents :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj]
        (φ : V → V') (r : V) (X : Finset V)
        (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
        (β :
          (Σ x : {x : V // x ∈ X},
            {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
        (cell : Ω → Set (Finset V × (V → ℝ)))
        (targetCell : Ω → Set (Finset V' × (V' → ℝ))),
        (∀ k : Fin n, zAt k ∉ insert r X ∧
          ∃ x : V, x ∈ X ∧ G.Adj x (zAt k)) →
        (∀ k : Fin n, ∀ x : V, x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) →
        ∃ (leftAdjacentEvent : ℕ → Ω → Set (Finset V × (V → ℝ)))
          (rightAdjacentEvent : ℕ → Ω → Set (Finset V' × (V' → ℝ)))
          (replacedBefore retainedFrom : ℕ → Finset (Fin n)),
          (∀ j : ℕ, ∀ i : Fin n, i ∈ replacedBefore j ↔ (i : ℕ) < j) ∧
          (∀ j : ℕ, ∀ i : Fin n, i ∈ retainedFrom j ↔ j ≤ (i : ℕ)) ∧
          (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
            leftAdjacentEvent k ω =
              {η : Finset V × (V → ℝ) |
                ∃ x : V, ∃ hxX : x ∈ X,
                  x ∈ η.1 ∧
                    (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                      G.Adj x y → η.2 y < η.2 x) ∧
                    (∀ i : Fin n, i ∈ retainedFrom k → i ≠ ⟨k, hk⟩ →
                      x ∈ B i →
                        ¬ (zAt i ∈ η.1 ∧
                          η.2 x < η.2 (zAt i) ∧
                            η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
                    x ∈ B ⟨k, hk⟩ ∧
                    ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                      η.2 x < η.2 (zAt ⟨k, hk⟩) ∧
                        η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}) ∧
          (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
            ∃ βFlat : V → V → V',
              (∀ x : V, ∀ hxX : x ∈ X,
                ∀ hxAdj : G.Adj x (zAt ⟨k, hk⟩),
                ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X,
                  βFlat x (zAt ⟨k, hk⟩) =
                    β ⟨⟨x, hxX⟩,
                      ⟨zAt ⟨k, hk⟩, ⟨hz, hxAdj⟩⟩⟩) ∧
              rightAdjacentEvent k ω =
                {η' : Finset V' × (V' → ℝ) |
                  ∃ x : V, ∃ hxX : x ∈ X,
                    φ x ∈ η'.1 ∧
                      (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                        G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
                      (∀ i : Fin n, i ∈ replacedBefore (k + 1) →
                        i ≠ ⟨k, hk⟩ → x ∈ B i →
                          ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                            ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                              η'.2 (φ x) <
                                η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                                η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                                  Set.Icc (0 : ℝ) 1)) ∧
                      x ∈ B ⟨k, hk⟩ ∧
                      ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                          G.Adj x (zAt ⟨k, hk⟩),
                        ¬ (βFlat x (zAt ⟨k, hk⟩) ∈ η'.1 ∧
                          η'.2 (φ x) <
                            η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∧
                            η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∈
                              Set.Icc (0 : ℝ) 1)}) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ φ r X n zAt B β cell targetCell hzAt hB
  let replacedBefore : ℕ → Finset (Fin n) := fun j => Finset.univ.filter (fun i => (i : ℕ) < j)
  let retainedFrom : ℕ → Finset (Fin n) := fun j => Finset.univ.filter (fun i => j ≤ (i : ℕ))
  let leftAdjacentEvent : ℕ → Ω → Set (Finset V × (V → ℝ)) :=
    fun k ω =>
      if hk : k < n then
        {η : Finset V × (V → ℝ) |
          ∃ x : V, ∃ hxX : x ∈ X,
            x ∈ η.1 ∧
              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                G.Adj x y → η.2 y < η.2 x) ∧
              (∀ i : Fin n, i ∈ retainedFrom k → i ≠ ⟨k, hk⟩ →
                x ∈ B i →
                  ¬ (zAt i ∈ η.1 ∧
                    η.2 x < η.2 (zAt i) ∧
                      η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
              x ∈ B ⟨k, hk⟩ ∧
              ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                η.2 x < η.2 (zAt ⟨k, hk⟩) ∧
                  η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}
      else Set.univ
  let rightAdjacentEvent : ℕ → Ω → Set (Finset V' × (V' → ℝ)) :=
    fun k ω =>
      if hk : k < n then
        let βFlat : V → V → V' :=
          fun x z =>
            if h : x ∈ X ∧ z = zAt ⟨k, hk⟩ ∧ G.Adj x z then
              β ⟨⟨x, h.1⟩,
                ⟨z, ⟨by simpa [h.2.1] using (hzAt ⟨k, hk⟩).1,
                  by simpa [h.2.1] using h.2.2⟩⟩⟩
            else φ x
        {η' : Finset V' × (V' → ℝ) |
          ∃ x : V, ∃ hxX : x ∈ X,
            φ x ∈ η'.1 ∧
              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
              (∀ i : Fin n, i ∈ replacedBefore (k + 1) →
                i ≠ ⟨k, hk⟩ → x ∈ B i →
                  ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                    ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                      η'.2 (φ x) <
                        η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                        η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                          Set.Icc (0 : ℝ) 1)) ∧
              x ∈ B ⟨k, hk⟩ ∧
              ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧ G.Adj x (zAt ⟨k, hk⟩),
                ¬ (βFlat x (zAt ⟨k, hk⟩) ∈ η'.1 ∧
                  η'.2 (φ x) <
                    η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∧
                    η'.2 (βFlat x (zAt ⟨k, hk⟩)) ∈ Set.Icc (0 : ℝ) 1)}
      else Set.univ
  refine ⟨leftAdjacentEvent, rightAdjacentEvent, replacedBefore, retainedFrom, ?_, ?_, ?_, ?_⟩
  · intro j i
    simp [replacedBefore]
  · intro j i
    simp [retainedFrom]
  · intro k hk ω
    simp [leftAdjacentEvent, hk]
  · intro k hk ω
    refine ⟨?_, ?_, ?_⟩
    · exact fun x z =>
        if h : x ∈ X ∧ z = zAt ⟨k, hk⟩ ∧ G.Adj x z then
          β ⟨⟨x, h.1⟩,
            ⟨z, ⟨by simpa [h.2.1] using (hzAt ⟨k, hk⟩).1,
              by simpa [h.2.1] using h.2.2⟩⟩⟩
        else φ x
    · intro x hxX hxAdj hz
      simp [hxX, hxAdj]
    · simp [rightAdjacentEvent, hk]
