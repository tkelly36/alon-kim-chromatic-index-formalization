import Mathlib.MeasureTheory.Measure.AEDisjoint
import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingFiniteBooleanAtomPartition]
theorem SamplingFiniteBooleanAtomPartition :
    ∀ {Λ α : Type u} [Fintype Λ] [DecidableEq Λ] [MeasurableSpace α],
      ∀ (ν : MeasureTheory.Measure α) (base : Set α) (label : Λ → Set α),
        NullMeasurableSet base ν →
        (∀ ℓ : Λ, NullMeasurableSet (label ℓ) ν) →
        ∃ atom : Finset Λ → Set α,
          (∀ truth : Finset Λ,
            atom truth =
              base ∩ {a : α | ∀ ℓ : Λ, (a ∈ label ℓ ↔ ℓ ∈ truth)}) ∧
          base = ⋃ truth : Finset Λ, atom truth ∧
          Set.Pairwise (Set.univ : Set (Finset Λ))
            (Function.onFun (AEDisjoint ν) atom) ∧
          (∀ truth : Finset Λ, NullMeasurableSet (atom truth) ν) := by
-- BODY
  classical
  intro Λ α _ _ _ ν base label hbase hlabel
  let atom : Finset Λ → Set α := fun truth =>
    base ∩ {a : α | ∀ ℓ : Λ, (a ∈ label ℓ ↔ ℓ ∈ truth)}
  refine ⟨atom, ?_, ?_, ?_, ?_⟩
  · intro truth
    rfl
  · ext a
    constructor
    · intro ha
      let truth : Finset Λ := (Finset.univ : Finset Λ).filter fun ℓ => a ∈ label ℓ
      refine Set.mem_iUnion.mpr ⟨truth, ?_⟩
      refine ⟨ha, ?_⟩
      intro ℓ
      simp [truth]
    · intro ha
      rcases Set.mem_iUnion.mp ha with ⟨truth, htruth⟩
      exact htruth.1
  · intro truth₁ _htruth₁ truth₂ _htruth₂ hneq
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro a ha₁ ha₂
    have hnot : ¬ ∀ ℓ : Λ, (ℓ ∈ truth₁ ↔ ℓ ∈ truth₂) := by
      intro h
      exact hneq (Finset.ext h)
    push_neg at hnot
    rcases hnot with ⟨ℓ, hℓ⟩
    have h₁ : a ∈ label ℓ ↔ ℓ ∈ truth₁ := ha₁.2 ℓ
    have h₂ : a ∈ label ℓ ↔ ℓ ∈ truth₂ := ha₂.2 ℓ
    have hequiv : ℓ ∈ truth₁ ↔ ℓ ∈ truth₂ := h₁.symm.trans h₂
    rcases hℓ with ⟨hmem, hnotmem⟩ | ⟨hnotmem, hmem⟩
    · exact hnotmem (hequiv.mp hmem)
    · exact hnotmem (hequiv.mpr hmem)
  · intro truth
    have htruth :
        NullMeasurableSet
          ({a : α | ∀ ℓ : Λ, (a ∈ label ℓ ↔ ℓ ∈ truth)}) ν := by
      have hset :
          ({a : α | ∀ ℓ : Λ, (a ∈ label ℓ ↔ ℓ ∈ truth)}) =
            ⋂ ℓ : Λ, (if ℓ ∈ truth then label ℓ else (label ℓ)ᶜ) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h ℓ
          by_cases hℓ : ℓ ∈ truth
          · simpa [hℓ] using (h ℓ).2 hℓ
          · simpa [hℓ] using fun hmem => hℓ ((h ℓ).1 hmem)
        · intro h ℓ
          constructor
          · intro hmem
            by_contra hnot
            have hcompl := h ℓ
            simpa [hnot, hmem] using hcompl
          · intro hmem
            have hset := h ℓ
            simpa [hmem] using hset
      rw [hset]
      exact NullMeasurableSet.iInter fun ℓ =>
        by
          by_cases hℓ : ℓ ∈ truth
          · simpa [hℓ] using hlabel ℓ
          · simpa [hℓ] using (hlabel ℓ).compl
    exact hbase.inter htruth
