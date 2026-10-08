import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingSplitOutsideBlockerTargetEndpointEquivalence]
theorem SamplingSplitOutsideBlockerTargetEndpointEquivalence
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (C coord : Finset W)
    (hcover : ∀ x : W, x ∈ C → ∀ y : W, G.Adj x y → y ∈ coord) :
    ∀ A : Finset W, ∀ π : W → ℝ,
      (((Finset.univ.filter fun z : W =>
        z ∈ A ∧ ∀ y : W, y ∈ A → G.Adj z y → π y < π z) ∩ C).Nonempty ↔
        ∃ x : W, x ∈ C ∧ x ∈ A ∧
          ∀ y : W, y ∈ A → G.Adj x y → y ∈ coord → π y < π x) := by
-- BODY
  intro A π
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    have hxC : x ∈ C := (Finset.mem_inter.mp hx).2
    have hxfilter :
        x ∈ Finset.univ.filter (fun z : W =>
          z ∈ A ∧ ∀ y : W, y ∈ A → G.Adj z y → π y < π z) :=
      (Finset.mem_inter.mp hx).1
    have hxsurv :
        x ∈ A ∧ ∀ y : W, y ∈ A → G.Adj x y → π y < π x :=
      (Finset.mem_filter.mp hxfilter).2
    refine ⟨x, hxC, hxsurv.1, ?_⟩
    intro y hyA hxy _hycoord
    exact hxsurv.2 y hyA hxy
  · rintro ⟨x, hxC, hxA, hlocal⟩
    refine ⟨x, ?_⟩
    rw [Finset.mem_inter]
    constructor
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ x
      · constructor
        · exact hxA
        · intro y hyA hxy
          exact hlocal y hyA hxy (hcover x hxC y hxy)
    · exact hxC
