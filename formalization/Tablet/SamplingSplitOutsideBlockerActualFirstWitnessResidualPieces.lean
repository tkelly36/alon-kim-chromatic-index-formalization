import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces]
noncomputable def SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
    {V V' : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    [LinearOrder {x : V // x ∈ X}]
    (β :
      (Σ x : {x : V // x ∈ X},
        {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (k : ℕ) (hk : k < n) :
    ({x : V // x ∈ X} → Set (Finset V × (V → ℝ))) ×
      ({x : V // x ∈ X} → Set (Finset V' × (V' → ℝ))) :=
-- BODY
  let sourceCompleteWitness :
      {x : V // x ∈ X} → Set (Finset V × (V → ℝ)) :=
    fun x =>
      {η |
        x.1 ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 →
            G.Adj x.1 y → η.2 y < η.2 x.1) ∧
          ∀ i : Fin n, (k : ℕ) ≤ i → x.1 ∈ B i →
            ¬ (zAt i ∈ η.1 ∧
              η.2 x.1 < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)}
  let sourceBoundary : Set (Finset V × (V → ℝ)) :=
    {η |
      ∃ x : V, ∃ hxX : x ∈ X,
        x ∈ η.1 ∧
          (∀ y : V, y ∈ insert r X → y ∈ η.1 →
            G.Adj x y → η.2 y < η.2 x) ∧
          (∀ i : Fin n, (k : ℕ) ≤ i → i ≠ ⟨k, hk⟩ →
            x ∈ B i →
              ¬ (zAt i ∈ η.1 ∧
                η.2 x < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
          x ∈ B ⟨k, hk⟩ ∧
          ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
            η.2 x < η.2 (zAt ⟨k, hk⟩) ∧
              η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)}
  let sourceResidualWitness :
      {x : V // x ∈ X} → Set (Finset V × (V → ℝ)) :=
    fun x => sourceCompleteWitness x \ sourceBoundary
  let targetCompleteWitness :
      {x : V // x ∈ X} → Set (Finset V' × (V' → ℝ)) :=
    fun x =>
      {η' |
        φ x.1 ∈ η'.1 ∧
          (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
            G.Adj x.1 y → η'.2 (φ y) < η'.2 (φ x.1)) ∧
          ∀ i : Fin n, (i : ℕ) < k + 1 → x.1 ∈ B i →
            ∀ hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i),
              ¬ (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                η'.2 (φ x.1) <
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∧
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∈
                    Set.Icc (0 : ℝ) 1)}
  let targetBoundary : Set (Finset V' × (V' → ℝ)) :=
    {η' |
      ∃ x : V, ∃ hxX : x ∈ X,
        φ x ∈ η'.1 ∧
          (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
            G.Adj x y → η'.2 (φ y) < η'.2 (φ x)) ∧
          (∀ i : Fin n, (i : ℕ) < k + 1 →
            i ≠ ⟨k, hk⟩ → x ∈ B i →
              ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
                ¬ (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ x) <
                    η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∧
                    η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt i, hz⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1)) ∧
          x ∈ B ⟨k, hk⟩ ∧
          ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧ G.Adj x (zAt ⟨k, hk⟩),
            ¬ (β ⟨⟨x, hxX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩ ∈ η'.1 ∧
              η'.2 (φ x) <
                η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∧
                η'.2 (β ⟨⟨x, hxX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∈
                  Set.Icc (0 : ℝ) 1)}
  let targetResidualWitness :
      {x : V // x ∈ X} → Set (Finset V' × (V' → ℝ)) :=
    fun x => targetCompleteWitness x \ targetBoundary
  (fun x =>
      {η |
        η ∈ sourceResidualWitness x ∧
          ∀ y : {x : V // x ∈ X}, y < x → η ∉ sourceResidualWitness y},
    fun x =>
      {η' |
        η' ∈ targetResidualWitness x ∧
          ∀ y : {x : V // x ∈ X}, y < x → η' ∉ targetResidualWitness y})
