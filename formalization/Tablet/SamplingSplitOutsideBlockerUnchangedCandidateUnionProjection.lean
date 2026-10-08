import Mathlib.MeasureTheory.Measure.AEDisjoint
import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerUnchangedCandidateUnionProjection]
theorem SamplingSplitOutsideBlockerUnchangedCandidateUnionProjection :
    ∀ {ι Source Target : Type u} [Fintype ι]
      [MeasurableSpace Source] [MeasurableSpace Target],
      ∀ (ν : MeasureTheory.Measure Source) (ν' : MeasureTheory.Measure Target)
        (sourceUnion : Set Source) (targetUnion : Set Target)
        (sourcePiece : ι → Set Source) (targetPiece : ι → Set Target),
        sourceUnion = ⋃ i ∈ (Finset.univ : Finset ι), sourcePiece i →
        targetUnion = ⋃ i ∈ (Finset.univ : Finset ι), targetPiece i →
        Set.Pairwise (Set.univ : Set ι)
          (Function.onFun (MeasureTheory.AEDisjoint ν) sourcePiece) →
        Set.Pairwise (Set.univ : Set ι)
          (Function.onFun (MeasureTheory.AEDisjoint ν') targetPiece) →
        (∀ i : ι, MeasureTheory.NullMeasurableSet (sourcePiece i) ν) →
        (∀ i : ι, MeasureTheory.NullMeasurableSet (targetPiece i) ν') →
        (∀ i : ι, ν (sourcePiece i) = ν' (targetPiece i)) →
        ν sourceUnion = ν' targetUnion := by
-- BODY
  classical
  intro ι Source Target _ _ _ ν ν' sourceUnion targetUnion sourcePiece
    targetPiece hsourceUnion htargetUnion hsourcePair htargetPair hsourceNull
    htargetNull hpiece
  rw [hsourceUnion, htargetUnion]
  rw [MeasureTheory.measure_biUnion_finset₀
      (by
        intro i _hi j _hj hij
        exact hsourcePair (Set.mem_univ i) (Set.mem_univ j) hij)
      (by intro i _hi; exact hsourceNull i)]
  rw [MeasureTheory.measure_biUnion_finset₀
      (by
        intro i _hi j _hj hij
        exact htargetPair (Set.mem_univ i) (Set.mem_univ j) hij)
      (by intro i _hi; exact htargetNull i)]
  simp_rw [hpiece]
