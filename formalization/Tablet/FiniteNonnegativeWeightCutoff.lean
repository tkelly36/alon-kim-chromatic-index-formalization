import Tablet.Preamble
import Mathlib.Data.Finset.Max

open scoped BigOperators

-- [TABLET NODE: FiniteNonnegativeWeightCutoff]
theorem FiniteNonnegativeWeightCutoff {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ t ⊆ s, (∑ x ∈ t, w x) ≤ b ∧
      (∀ y ∈ s \ t, b < (∑ x ∈ t, w x) + w y) ∧
      (∀ x ∈ t, ∀ y ∈ s \ t, w x ≤ w y) := by
-- BODY
  classical
  induction s using Finset.strongInductionOn generalizing b with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image w hs
      by_cases hab : w a ≤ b
      · obtain ⟨t, ht, hsum, hmax, hord⟩ := ih (s.erase a)
          (Finset.erase_ssubset ha)
          (fun x hx => hw x (Finset.mem_of_mem_erase hx))
          (b - w a) (sub_nonneg.mpr hab)
        have hat : a ∉ t := fun h => (Finset.mem_erase.mp (ht h)).1 rfl
        refine ⟨insert a t, Finset.insert_subset_iff.mpr
          ⟨ha, ht.trans (Finset.erase_subset _ _)⟩, ?_, ?_, ?_⟩
        · rw [Finset.sum_insert hat]
          linarith
        · intro y hy
          obtain ⟨hys, hyat⟩ := Finset.mem_sdiff.mp hy
          have hyt : y ∈ s.erase a \ t := by
            simp only [Finset.mem_sdiff, Finset.mem_erase]
            exact ⟨⟨fun h => hyat (h ▸ Finset.mem_insert_self a t), hys⟩,
              fun h => hyat (Finset.mem_insert_of_mem h)⟩
          have := hmax y hyt
          rw [Finset.sum_insert hat]
          linarith
        · intro x hx y hy
          obtain ⟨hys, hyat⟩ := Finset.mem_sdiff.mp hy
          rcases Finset.mem_insert.mp hx with rfl | hxt
          · exact hmin y hys
          · apply hord x hxt y
            simp only [Finset.mem_sdiff, Finset.mem_erase]
            exact ⟨⟨fun h => hyat (h ▸ Finset.mem_insert_self a t), hys⟩,
              fun h => hyat (Finset.mem_insert_of_mem h)⟩
      · refine ⟨∅, Finset.empty_subset _, by simpa using hb, ?_, by simp⟩
        intro y hy
        have := hmin y (Finset.mem_sdiff.mp hy).1
        simpa using lt_of_lt_of_le (lt_of_not_ge hab) this
    · have hs' := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨∅, by simp, by simpa using hb, by simp, by simp⟩
