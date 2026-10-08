import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPairedCandidateEvent]
def SamplingSplitOutsideBlockerPairedCandidateEvent
    {V V' : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V']
    (G : SimpleGraph V) (φ : V → V') (r : V) (X : Finset V)
    {n : ℕ} (zAt : Fin n → V) (B : Fin n → Finset V)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (privateIndices retained : Finset (Fin n)) (x : {x : V // x ∈ X}) :
    Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
-- BODY
  {ζ | x.1 ∈ ζ.1.1 ∧ φ x.1 ∈ ζ.2.1 ∧
    (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
      G.Adj x.1 y → ζ.1.2 y < ζ.1.2 x.1) ∧
    (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
      G.Adj x.1 y → ζ.2.2 (φ y) < ζ.2.2 (φ x.1)) ∧
    (∀ i : Fin n, i ∈ privateIndices → x.1 ∈ B i →
      ∀ hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i),
        ¬ (β ⟨x, ⟨zAt i, hz⟩⟩ ∈ ζ.2.1 ∧
          ζ.2.2 (φ x.1) < ζ.2.2 (β ⟨x, ⟨zAt i, hz⟩⟩) ∧
          ζ.2.2 (β ⟨x, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)) ∧
    (∀ i : Fin n, i ∈ retained → x.1 ∈ B i →
      ¬ (zAt i ∈ ζ.1.1 ∧ ζ.1.2 x.1 < ζ.1.2 (zAt i) ∧
        ζ.1.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1))}
