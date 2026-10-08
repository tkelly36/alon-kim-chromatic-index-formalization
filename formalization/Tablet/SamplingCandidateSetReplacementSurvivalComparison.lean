import Tablet.SamplingOneBlockerProductInequality

open BigOperators

-- [TABLET NODE: SamplingCandidateSetReplacementSurvivalComparison]
theorem SamplingCandidateSetReplacementSurvivalComparison {α : Type*} [DecidableEq α]
    (C : Finset α) (p : ℝ) (π : α → ℝ)
    (hC : C.Nonempty) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ0 : ∀ x, x ∈ C → 0 ≤ π x) (hπ1 : ∀ x, x ∈ C → π x ≤ 1) :
    ∃ x0 : α, x0 ∈ C ∧ (∀ x, x ∈ C → π x ≤ π x0) ∧
      1 - p * (1 - π x0) ≤
        1 - (∏ x ∈ C, p * (1 - π x)) := by
-- BODY
  classical
  let scores : Finset ℝ := C.image π
  have hscores_nonempty : scores.Nonempty := by
    rcases hC with ⟨x, hx⟩
    exact ⟨π x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let m : ℝ := scores.max' hscores_nonempty
  have hm_mem : m ∈ scores := Finset.max'_mem scores hscores_nonempty
  rcases Finset.mem_image.mp hm_mem with ⟨x0, hx0, hx0_score⟩
  have hmax : ∀ x, x ∈ C → π x ≤ π x0 := by
    intro x hx
    have hπx_mem : π x ∈ scores := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hle : π x ≤ m := Finset.le_max' scores (π x) hπx_mem
    simpa [m, hx0_score] using hle
  have hprod :
      (∏ x ∈ C, p * (1 - π x)) ≤ p * (1 - π x0) := by
    exact SamplingOneBlockerProductInequality C p π x0 hx0 hp0 hp1 hπ0 hπ1
  refine ⟨x0, hx0, hmax, ?_⟩
  linarith
