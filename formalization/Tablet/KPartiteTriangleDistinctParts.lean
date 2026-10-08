import Tablet.Preamble

-- [TABLET NODE: KPartiteTriangleDistinctParts]
theorem KPartiteTriangleDistinctParts :
    ∀ k : ℕ, 0 < k →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
          ∀ part : V → Fin k,
            (∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
            ∀ s : Finset V,
              s.card = 3 →
              (∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v) →
              (s.image part).card = 3 := by
-- BODY
  intro k _ V _ _ G _ part hpart s hcard hclique
  have hinj : Set.InjOn part (fun x => x ∈ s) := by
    intro u hu v hv huv
    by_contra hne
    exact hpart (hclique hu hv hne) huv
  rw [← hcard]
  exact Finset.card_image_of_injOn hinj
