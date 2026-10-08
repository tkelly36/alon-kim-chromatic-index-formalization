import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingOneBlockerProductInequality]
theorem SamplingOneBlockerProductInequality {α : Type*} [DecidableEq α]
    (C : Finset α) (p : ℝ) (π : α → ℝ) (x0 : α)
    (hx0 : x0 ∈ C) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ0 : ∀ x, x ∈ C → 0 ≤ π x) (hπ1 : ∀ x, x ∈ C → π x ≤ 1) :
    (∏ x ∈ C, p * (1 - π x)) ≤ p * (1 - π x0) := by
-- BODY
  classical
  have h0 : ∀ x ∈ C, 0 ≤ p * (1 - π x) := by
    intro x hx
    exact mul_nonneg hp0 (sub_nonneg.mpr (hπ1 x hx))
  have hle1 : ∀ x ∈ C, p * (1 - π x) ≤ 1 := by
    intro x hx
    have hq0 : 0 ≤ 1 - π x := sub_nonneg.mpr (hπ1 x hx)
    have hq1 : 1 - π x ≤ 1 := by
      linarith [hπ0 x hx]
    exact (mul_le_mul hp1 hq1 hq0 (by linarith)).trans (by norm_num)
  have hsubset : ({x0} : Finset α) ⊆ C := by
    intro y hy
    simpa [Finset.mem_singleton.mp hy]
  have hprod :=
    Finset.prod_le_prod_of_subset_of_le_one (s := ({x0} : Finset α)) (t := C)
      (f := fun x => p * (1 - π x)) hsubset h0 (by
        intro x hx _hnot
        exact hle1 x hx)
  simpa using hprod
