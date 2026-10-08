import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Lattice
import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerFirstWitnessFiniteRefinement]
theorem SamplingSplitOutsideBlockerFirstWitnessFiniteRefinement :
    ∀ {ι α : Type u} [Fintype ι] [LinearOrder ι]
      (U : Set α) (W : ι → Set α),
      U = ⋃ i, W i →
      ∃ P : ι → Set α,
        (∀ i : ι, P i = {a : α | a ∈ W i ∧ ∀ j : ι, j < i → a ∉ W j}) ∧
        U = ⋃ i, P i ∧
        Set.Pairwise (Set.univ : Set ι) (Function.onFun Disjoint P) := by
-- BODY
  classical
  intro ι α _ _ U W hU
  let P : ι → Set α := fun i =>
    {a : α | a ∈ W i ∧ ∀ j : ι, j < i → a ∉ W j}
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    rfl
  · ext a
    constructor
    · intro ha
      have hsome : ∃ i, a ∈ W i := by
        simpa [hU] using ha
      let s : Finset ι := Finset.univ.filter fun i => a ∈ W i
      have hs : s.Nonempty := by
        rcases hsome with ⟨i, hi⟩
        exact ⟨i, by simp [s, hi]⟩
      refine Set.mem_iUnion.2 ⟨s.min' hs, ?_⟩
      constructor
      · have hmem : s.min' hs ∈ s := Finset.min'_mem s hs
        simpa [P, s] using hmem
      · intro j hj hWj
        have hjmem : j ∈ s := by
          simp [s, hWj]
        exact not_lt_of_ge (Finset.min'_le s j hjmem) hj
    · intro ha
      rcases Set.mem_iUnion.1 ha with ⟨i, hi⟩
      have hWi : a ∈ W i := hi.1
      have : a ∈ ⋃ i, W i := Set.mem_iUnion.2 ⟨i, hWi⟩
      simpa [hU] using this
  · intro i _hi j _hj hij
    rw [Function.onFun]
    refine Set.disjoint_left.2 ?_
    intro a hai haj
    have hcmp : j < i ∨ i < j := lt_or_gt_of_ne hij.symm
    rcases hcmp with hji | hij'
    · exact hai.2 j hji haj.1
    · exact haj.2 i hij' hai.1
