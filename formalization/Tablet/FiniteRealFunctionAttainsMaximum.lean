import Tablet.Preamble

universe u

-- [TABLET NODE: FiniteRealFunctionAttainsMaximum]
theorem FiniteRealFunctionAttainsMaximum :
    ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (score : ι → ℝ),
      ∃ i : ι, ∀ j : ι, score j ≤ score i := by
-- BODY
  intro ι _ hnonempty score
  classical
  let s : Finset ℝ := Finset.univ.image score
  have hs : s.Nonempty := by
    rcases hnonempty with ⟨i⟩
    exact ⟨score i, by simp [s]⟩
  let m : ℝ := s.max' hs
  have hm : m ∈ s := Finset.max'_mem s hs
  rcases Finset.mem_image.mp hm with ⟨i, _hi, hi⟩
  refine ⟨i, ?_⟩
  intro j
  have hj : score j ∈ s := by
    simp [s]
  have hle : score j ≤ m := Finset.le_max' s (score j) hj
  simpa [m, hi] using hle
