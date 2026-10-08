import Tablet.LocalBParameter

universe u v

-- [TABLET NODE: LocalBParameterNeighborhoodEmbeddingTransport]
theorem LocalBParameterNeighborhoodEmbeddingTransport :
    ∀ {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj]
        (G' : SimpleGraph β) [DecidableRel G'.Adj]
        (M : ℕ) (v : α) (w : β) (φ : α ↪ β),
        (∀ x : α, x ∈ G.neighborFinset v → φ x ∈ G'.neighborFinset w) →
        (∀ y : β, y ∈ G'.neighborFinset w →
          ∃ x : α, x ∈ G.neighborFinset v ∧ φ x = y) →
        (∀ ⦃x : α⦄, x ∈ G.neighborFinset v →
          ∀ ⦃y : α⦄, y ∈ G.neighborFinset v →
            (G.Adj x y ↔ G'.Adj (φ x) (φ y))) →
        LocalBParameter G M v = LocalBParameter G' M w := by
-- BODY
  classical
  intro α β instFintypeα instDecidableEqα instFintypeβ instDecidableEqβ
    G instDecidableRelG G' instDecidableRelG' M v w φ hmap hsurj hadj
  have hdegree_eq : G.degree v = G'.degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree G v,
      ← SimpleGraph.card_neighborFinset_eq_degree G' w]
    refine Finset.card_bij'
      (fun x _hx => φ x)
      (fun y hy => Classical.choose (hsurj y hy))
      ?_ ?_ ?_ ?_
    · intro x hx
      exact hmap x hx
    · intro y hy
      exact (Classical.choose_spec (hsurj y hy)).1
    · intro x hx
      exact φ.injective (Classical.choose_spec (hsurj (φ x) (hmap x hx))).2
    · intro y hy
      exact (Classical.choose_spec (hsurj y hy)).2
  have hcount_eq (n : ℕ) :
      ((Finset.univ : Finset (Finset α)).filter (fun S =>
        S.card = n ∧ S ⊆ G.neighborFinset v ∧
          ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)).card =
      ((Finset.univ : Finset (Finset β)).filter (fun T =>
        T.card = n ∧ T ⊆ G'.neighborFinset w ∧
          ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x ≠ y → ¬ G'.Adj x y)).card := by
    let A : Finset (Finset α) :=
      (Finset.univ : Finset (Finset α)).filter (fun S =>
        S.card = n ∧ S ⊆ G.neighborFinset v ∧
          ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
    let B : Finset (Finset β) :=
      (Finset.univ : Finset (Finset β)).filter (fun T =>
        T.card = n ∧ T ⊆ G'.neighborFinset w ∧
          ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x ≠ y → ¬ G'.Adj x y)
    let pull (T : Finset β) : Finset α :=
      (Finset.univ : Finset α).filter (fun x => φ x ∈ T)
    change A.card = B.card
    refine Finset.card_bij'
      (fun S _hS => S.image (fun x => φ x))
      (fun T _hT => pull T)
      ?_ ?_ ?_ ?_
    · intro S hS
      dsimp [A, B] at hS ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      rcases hS with ⟨hcard, hsub, hind⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injOn]
        · exact hcard
        · intro x _hx y _hy hxy
          exact φ.injective hxy
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        exact hmap x (hsub hx)
      · intro x hx y hy hxy hxyAdj
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y0, hy0, hyval⟩
        subst hyval
        have hx0n : x0 ∈ G.neighborFinset v := hsub hx0
        have hy0n : y0 ∈ G.neighborFinset v := hsub hy0
        have hne0 : x0 ≠ y0 := by
          intro h
          exact hxy (by rw [h])
        exact hind hx0 hy0 hne0 ((hadj hx0n hy0n).mpr hxyAdj)
    · intro T hT
      dsimp [A, B] at hT ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      rcases hT with ⟨hcard, hsub, hind⟩
      have hImage_pull : (pull T).image (fun x => φ x) = T := by
        apply Finset.ext
        intro y
        constructor
        · intro hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          dsimp [pull] at hx
          exact (Finset.mem_filter.mp hx).2
        · intro hy
          have hyn : y ∈ G'.neighborFinset w := hsub hy
          rcases hsurj y hyn with ⟨x, _hxn, hxy⟩
          exact Finset.mem_image.mpr ⟨x, by
            dsimp [pull]
            simp [hy, hxy], hxy⟩
      refine ⟨?_, ?_, ?_⟩
      · have hcard_image : ((pull T).image (fun x => φ x)).card = (pull T).card := by
          rw [Finset.card_image_of_injOn]
          intro x _hx y _hy hxy
          exact φ.injective hxy
        rw [← hcard_image, hImage_pull, hcard]
      · intro x hx
        dsimp [pull] at hx
        have hφxT : φ x ∈ T := (Finset.mem_filter.mp hx).2
        have hφxn : φ x ∈ G'.neighborFinset w := hsub hφxT
        rcases hsurj (φ x) hφxn with ⟨z, hzn, hz⟩
        have hzx : z = x := φ.injective hz
        simpa [hzx] using hzn
      · intro x hx y hy hxy hxyAdj
        have hxn : x ∈ G.neighborFinset v := by
          dsimp [pull] at hx
          have hφxT : φ x ∈ T := (Finset.mem_filter.mp hx).2
          have hφxn : φ x ∈ G'.neighborFinset w := hsub hφxT
          rcases hsurj (φ x) hφxn with ⟨z, hzn, hz⟩
          have hzx : z = x := φ.injective hz
          simpa [hzx] using hzn
        have hyn : y ∈ G.neighborFinset v := by
          dsimp [pull] at hy
          have hφyT : φ y ∈ T := (Finset.mem_filter.mp hy).2
          have hφyn : φ y ∈ G'.neighborFinset w := hsub hφyT
          rcases hsurj (φ y) hφyn with ⟨z, hzn, hz⟩
          have hzy : z = y := φ.injective hz
          simpa [hzy] using hzn
        have hφxT : φ x ∈ T := by
          dsimp [pull] at hx
          exact (Finset.mem_filter.mp hx).2
        have hφyT : φ y ∈ T := by
          dsimp [pull] at hy
          exact (Finset.mem_filter.mp hy).2
        have hφne : φ x ≠ φ y := by
          intro hφ
          exact hxy (φ.injective hφ)
        exact hind hφxT hφyT hφne ((hadj hxn hyn).mp hxyAdj)
    · intro S hS
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨_hxu, hximage⟩
        rcases Finset.mem_image.mp hximage with ⟨y, hy, hyx⟩
        have hxy : y = x := φ.injective hyx
        simpa [hxy] using hy
      · intro hx
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    · intro T hT
      dsimp [B] at hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      have hsub : T ⊆ G'.neighborFinset w := hT.2.1
      apply Finset.ext
      intro y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        dsimp [pull] at hx
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        have hyn : y ∈ G'.neighborFinset w := hsub hy
        rcases hsurj y hyn with ⟨x, _hxn, hxy⟩
        exact Finset.mem_image.mpr ⟨x, by
          dsimp [pull]
          simp [hy, hxy], hxy⟩
  have hpair_eq :
      IndependentPairCount G v = IndependentPairCount G' w := by
    unfold IndependentPairCount
    exact hcount_eq 2
  have htriple_eq :
      IndependentTripleCount G v = IndependentTripleCount G' w := by
    unfold IndependentTripleCount
    exact hcount_eq 3
  unfold LocalBParameter
  rw [hdegree_eq, hpair_eq, htriple_eq]
