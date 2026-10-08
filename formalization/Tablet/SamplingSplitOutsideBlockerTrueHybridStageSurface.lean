import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerTrueHybridStageSurface]
theorem SamplingSplitOutsideBlockerTrueHybridStageSurface :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj]
        (φ : V → V') (r : V) (X : Finset V)
        (n : ℕ) (zAt : Fin n → V)
        (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
        (β :
          (Σ x : {x : V // x ∈ X},
            {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
        ∃ (hybridStage sharedUnchangedContext
              sourceCurrentBoundary targetCurrentBoundary :
              ℕ → Ω →
                Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))))
          (replacedBefore retainedFrom : ℕ → Finset (Fin n)),
          (∀ j : ℕ, ∀ i : Fin n, i ∈ replacedBefore j ↔ (i : ℕ) < j) ∧
          (∀ j : ℕ, ∀ i : Fin n, i ∈ retainedFrom j ↔ j ≤ (i : ℕ)) ∧
          (∀ j : ℕ, j ≤ n → ∀ ω : Ω,
            hybridStage j ω =
              {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
                ∃ x : V, ∃ hxX : x ∈ X,
                  x ∈ ζ.1.1 ∧
                    φ x ∈ ζ.2.1 ∧
                    (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
                      G.Adj x y → ζ.1.2 y < ζ.1.2 x) ∧
                    (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
                      G.Adj x y → ζ.2.2 (φ y) < ζ.2.2 (φ x)) ∧
                    (∀ i : Fin n, i ∈ retainedFrom j → G.Adj x (zAt i) →
                      ¬ (zAt i ∈ ζ.1.1 ∧
                        ζ.1.2 x < ζ.1.2 (zAt i) ∧
                          ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
                    (∀ i : Fin n, i ∈ replacedBefore j →
                      ∀ hzAdj : G.Adj x (zAt i),
                        ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈
                            ζ.2.1 ∧
                          ζ.2.2 (φ x) <
                            ζ.2.2
                              (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                            ζ.2.2
                              (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                              Set.Icc (0 : ℝ) 1))}) ∧
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
                          ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}) ∧
          (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
            sourceCurrentBoundary k ω =
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
                          ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
                    ¬ (zAt ⟨k, hk⟩ ∈ ζ.1.1 ∧
                      ζ.1.2 x < ζ.1.2 (zAt ⟨k, hk⟩) ∧
                        ζ.1.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}) ∧
          (∀ k : ℕ, ∀ hk : k < n, ∀ ω : Ω,
            targetCurrentBoundary k ω =
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
                          ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
                    (∀ hzAdj : G.Adj x (zAt ⟨k, hk⟩),
                      ¬ (β ⟨⟨x, hxX⟩,
                            ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩ ∈
                          ζ.2.1 ∧
                        ζ.2.2 (φ x) <
                          ζ.2.2
                            (β ⟨⟨x, hxX⟩,
                              ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩) ∧
                          ζ.2.2
                            (β ⟨⟨x, hxX⟩,
                              ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩) ∈
                            Set.Icc (0 : ℝ) 1))}) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ φ r X n zAt hOutside β
  let replacedBefore : ℕ → Finset (Fin n) :=
    fun j => Finset.univ.filter fun i : Fin n => (i : ℕ) < j
  let retainedFrom : ℕ → Finset (Fin n) :=
    fun j => Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)
  let hybridStage :
      ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun j _ω =>
      {ζ |
        ∃ x : V, ∃ hxX : x ∈ X,
          x ∈ ζ.1.1 ∧
            φ x ∈ ζ.2.1 ∧
            (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
              G.Adj x y → ζ.1.2 y < ζ.1.2 x) ∧
            (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
              G.Adj x y → ζ.2.2 (φ y) < ζ.2.2 (φ x)) ∧
            (∀ i : Fin n, i ∈ retainedFrom j → G.Adj x (zAt i) →
              ¬ (zAt i ∈ ζ.1.1 ∧
                ζ.1.2 x < ζ.1.2 (zAt i) ∧
                  ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
            (∀ i : Fin n, i ∈ replacedBefore j →
              ∀ hzAdj : G.Adj x (zAt i),
                ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈ ζ.2.1 ∧
                  ζ.2.2 (φ x) <
                    ζ.2.2
                      (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                    ζ.2.2
                      (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1))}
  let sharedUnchangedContext :
      ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun k _ω =>
      if hk : k < n then
        {ζ |
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
                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈ ζ.2.1 ∧
                    ζ.2.2 (φ x) <
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                        Set.Icc (0 : ℝ) 1)) ∧
              (∀ i : Fin n, k < (i : ℕ) → G.Adj x (zAt i) →
                ¬ (zAt i ∈ ζ.1.1 ∧
                  ζ.1.2 x < ζ.1.2 (zAt i) ∧
                    ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}
      else Set.univ
  let sourceCurrentBoundary :
      ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun k _ω =>
      if hk : k < n then
        {ζ |
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
                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈ ζ.2.1 ∧
                    ζ.2.2 (φ x) <
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                        Set.Icc (0 : ℝ) 1)) ∧
              (∀ i : Fin n, k < (i : ℕ) → G.Adj x (zAt i) →
                ¬ (zAt i ∈ ζ.1.1 ∧
                  ζ.1.2 x < ζ.1.2 (zAt i) ∧
                    ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
              ¬ (zAt ⟨k, hk⟩ ∈ ζ.1.1 ∧
                ζ.1.2 x < ζ.1.2 (zAt ⟨k, hk⟩) ∧
                  ζ.1.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}
      else Set.univ
  let targetCurrentBoundary :
      ℕ → Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun k _ω =>
      if hk : k < n then
        {ζ |
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
                  ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩ ∈ ζ.2.1 ∧
                    ζ.2.2 (φ x) <
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∧
                      ζ.2.2
                        (β ⟨⟨x, hxX⟩, ⟨zAt i, ⟨hOutside i, hzAdj⟩⟩⟩) ∈
                        Set.Icc (0 : ℝ) 1)) ∧
              (∀ i : Fin n, k < (i : ℕ) → G.Adj x (zAt i) →
                ¬ (zAt i ∈ ζ.1.1 ∧
                  ζ.1.2 x < ζ.1.2 (zAt i) ∧
                    ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
              (∀ hzAdj : G.Adj x (zAt ⟨k, hk⟩),
                ¬ (β ⟨⟨x, hxX⟩,
                      ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩ ∈ ζ.2.1 ∧
                  ζ.2.2 (φ x) <
                    ζ.2.2
                      (β ⟨⟨x, hxX⟩,
                        ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩) ∧
                    ζ.2.2
                      (β ⟨⟨x, hxX⟩,
                        ⟨zAt ⟨k, hk⟩, ⟨hOutside ⟨k, hk⟩, hzAdj⟩⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1))}
      else Set.univ
  refine
    ⟨hybridStage, sharedUnchangedContext, sourceCurrentBoundary,
      targetCurrentBoundary, replacedBefore, retainedFrom, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro j i
    simp [replacedBefore]
  · intro j i
    simp [retainedFrom]
  · intro j hj ω
    rfl
  · intro k hk ω
    simp [sharedUnchangedContext, hk]
  · intro k hk ω
    simp [sourceCurrentBoundary, hk]
  · intro k hk ω
    simp [targetCurrentBoundary, hk]
