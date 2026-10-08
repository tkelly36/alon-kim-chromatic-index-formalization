import Tablet.SamplingSplitOutsideBlockerFirstWitnessFiniteRefinement
import Mathlib.MeasureTheory.Measure.AEDisjoint

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerFirstWitnessCellRefinement]
theorem SamplingSplitOutsideBlockerFirstWitnessCellRefinement :
    ∀ {ι α : Type u} [Fintype ι] [LinearOrder ι] [MeasurableSpace α],
      ∀ (ν : MeasureTheory.Measure α) (U C : Set α) (W : ι → Set α),
        U = ⋃ i, W i →
        (∀ i : ι, MeasureTheory.NullMeasurableSet (W i) ν) →
        MeasureTheory.NullMeasurableSet C ν →
        ∃ P : ι → Set α,
          (∀ i : ι,
            P i = {a : α | a ∈ W i ∧ ∀ j : ι, j < i → a ∉ W j}) ∧
          U ∩ C = ⋃ i ∈ (Finset.univ : Finset ι), P i ∩ C ∧
          Set.Pairwise (Set.univ : Set ι)
            (Function.onFun (MeasureTheory.AEDisjoint ν) (fun i => P i ∩ C)) ∧
          (∀ i : ι, MeasureTheory.NullMeasurableSet (P i ∩ C) ν) := by
-- BODY
  classical
  intro ι α _ _ _ ν U C W hU hW hC
  obtain ⟨P, hP_def, hP_union, hP_disjoint⟩ :=
    SamplingSplitOutsideBlockerFirstWitnessFiniteRefinement U W hU
  refine ⟨P, hP_def, ?_, ?_, ?_⟩
  · ext a
    constructor
    · intro ha
      rcases Set.mem_iUnion.mp (by simpa [hP_union] using ha.1) with ⟨i, hi⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      refine Set.mem_iUnion.mpr ⟨by simp, ?_⟩
      exact ⟨hi, ha.2⟩
    · intro ha
      rcases Set.mem_iUnion.mp ha with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨_hiuniv, hia⟩
      exact ⟨by
        rw [hP_union]
        exact Set.mem_iUnion.mpr ⟨i, hia.1⟩, hia.2⟩
  · intro i _hi j _hj hij
    apply Disjoint.aedisjoint
    exact (hP_disjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono
      (by intro a ha; exact ha.1) (by intro a ha; exact ha.1)
  · intro i
    have hPi : MeasureTheory.NullMeasurableSet (P i) ν := by
      rw [hP_def i]
      have hExcl :
          MeasureTheory.NullMeasurableSet
            {a : α | ∀ j : ι, j < i → a ∉ W j} ν := by
        convert
          (MeasureTheory.NullMeasurableSet.iInter fun j : ι =>
          MeasureTheory.NullMeasurableSet.iInter fun _hji : j < i =>
            (hW j).compl) using 1
        ext a
        simp
      exact (hW i).inter hExcl
    exact hPi.inter hC
