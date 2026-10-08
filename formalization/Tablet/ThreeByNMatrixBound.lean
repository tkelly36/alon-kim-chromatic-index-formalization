import Mathlib.LinearAlgebra.Matrix.Permanent
import Tablet.Preamble
import Tablet.ThreeByThreeCenteredColumnBound

open scoped BigOperators

-- [TABLET NODE: ThreeByNMatrixBound]
theorem ThreeByNMatrixBound :
    ∀ {n : ℕ} (hn : 3 ≤ n) (A : Matrix (Fin 3) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) →
      (let c : Fin n → ℝ := fun j => ∑ i : Fin 3, A i j;
        (∀ j, c j ≤ 1) →
        (∀ j k : Fin n, (j : ℕ) ≤ (k : ℕ) → c k ≤ c j) →
        (∑ j : Fin n, c j) ≤ 3 →
          (1 / 9 : ℝ) *
              (∑ j : Fin n,
                ∑ i : Fin 3, ∑ i' : Fin 3,
                  if i < i' then A i j * A i' j else 0)
            + (1 / 27 : ℝ) *
              Matrix.permanent (fun i j : Fin 3 => A i (Fin.castLE hn j))
            - (1 / 27 : ℝ) *
              (∑ i : Fin 3, ∑ j : Fin 3, A i (Fin.castLE hn j))
            ≤ 2 / (3 : ℝ) ^ 5) := by
-- BODY
  intro n hn A hA
  dsimp only
  intro hc hord htotal
  let c : Fin n → ℝ := fun j => ∑ i : Fin 3, A i j
  let q : Fin n → ℝ := fun j => ∑ i : Fin 3, ∑ i' : Fin 3,
    if i < i' then A i j * A i' j else 0
  let e : Fin 3 → Fin n := Fin.castLE hn
  let s : Finset (Fin n) := Finset.univ.image e
  let t : Finset (Fin n) := Finset.univ \ s
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin n => x.val) h
  have hsplit (f : Fin n → ℝ) :
      (∑ j, f j) = (∑ j : Fin 3, f (e j)) + ∑ j ∈ t, f j := by
    have him : (∑ j ∈ s, f j) = ∑ j : Fin 3, f (e j) :=
      Finset.sum_image (fun i _ j _ h => he h)
    have h := Finset.sum_sdiff (Finset.subset_univ s) (f := f)
    dsimp [t]
    rw [← him]
    linarith
  have hc0 (j) : 0 ≤ c j := Finset.sum_nonneg fun i _ => (hA i j).1
  have hq (j) : 3 * q j ≤ c j ^ 2 := by
    dsimp [q, c]
    simp [Fin.sum_univ_three]
    nlinarith [sq_nonneg (A 0 j - A 1 j), sq_nonneg (A 0 j - A 2 j),
      sq_nonneg (A 1 j - A 2 j)]
  have htail (j) (hj : j ∈ t) : c j ≤ c (e 2) := by
    apply hord
    have hnots : j ∉ s := (Finset.mem_sdiff.mp hj).2
    have hlarge : 3 ≤ j.val := by
      by_contra h
      have hj3 : j.val < 3 := by omega
      apply hnots
      apply Finset.mem_image.mpr
      exact ⟨⟨j.val, hj3⟩, Finset.mem_univ _, Fin.ext rfl⟩
    change 2 ≤ j.val
    omega
  have htailQ : 3 * (∑ j ∈ t, q j) ≤ c (e 2) * (∑ j ∈ t, c j) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact (hq j).trans (by nlinarith [mul_nonneg (hc0 j) (sub_nonneg.mpr (htail j hj))])
  have hlead := ThreeByThreeCenteredColumnBound (fun i j => A i (e j))
    (fun i j => (hA i (e j)).1) (fun j => hc (e j))
  change 3 * (∑ j : Fin 3, q (e j)) + _ ≤
    (∑ j : Fin 3, c (e j) ^ 2) + (2 / 9 : ℝ) * c (e 0) * c (e 1) * c (e 2) at hlead
  have hmass : (∑ j ∈ t, c j) ≤ 3 - (c (e 0) + c (e 1) + c (e 2)) := by
    have hs := hsplit c
    simp only [Fin.sum_univ_three] at hs
    change (∑ j, c j) ≤ 3 at htotal
    linarith
  have htailQ' := htailQ.trans (mul_le_mul_of_nonneg_left hmass (hc0 (e 2)))
  have hscalar : ∀ x y z : ℝ, 0 ≤ z → z ≤ y → y ≤ x → x ≤ 1 →
      x * (x - 1) + y * (y - 1) + z * (2 - x - y + (2 / 9) * x * y) ≤ 2 / 9 := by
    intro x y z hz hzy hyx hx
    have hy : 0 ≤ y := hz.trans hzy
    have hx0 : 0 ≤ x := hy.trans hyx
    have hy1 : y ≤ 1 := hyx.trans hx
    have hcoef : 0 ≤ 2 - x - y + (2 / 9) * x * y := by
      nlinarith [mul_nonneg hx0 hy]
    have hstep := mul_nonneg (sub_nonneg.mpr hzy) hcoef
    have hstep' := mul_nonneg (sub_nonneg.mpr hyx)
      (show 0 ≤ 1 - x + (2 / 9) * x * (x + y) from
        add_nonneg (sub_nonneg.mpr hx) (by positivity))
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hx3 : x ^ 3 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx2) hx0]
    nlinarith
  have hscalar' := hscalar (c (e 0)) (c (e 1)) (c (e 2))
    (hc0 _) (hord _ _ (by change 1 ≤ 2; omega))
    (hord _ _ (by change 0 ≤ 1; omega)) (hc _)
  have hqs := hsplit q
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, A i (e j)) =
      c (e 0) + c (e 1) + c (e 2) := by
    rw [Finset.sum_comm]
    exact Fin.sum_univ_three _
  change (1 / 9 : ℝ) * (∑ j, q j) + (1 / 27 : ℝ) *
    Matrix.permanent (fun i j => A i (e j)) -
    (1 / 27 : ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, A i (e j)) ≤ _
  rw [hsum]
  simp only [Fin.sum_univ_three] at hlead hqs
  norm_num only [pow_succ, pow_zero, mul_one]
  nlinarith
