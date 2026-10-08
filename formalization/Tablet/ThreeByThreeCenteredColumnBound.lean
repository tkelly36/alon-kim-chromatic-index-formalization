import Tablet.Preamble
import Mathlib.LinearAlgebra.Matrix.Permanent

open scoped BigOperators

-- [TABLET NODE: ThreeByThreeCenteredColumnBound]
theorem ThreeByThreeCenteredColumnBound (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hc : ∀ j, (∑ i : Fin 3, A i j) ≤ 1) :
    3 * (∑ j : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
      if i < i' then A i j * A i' j else 0) + Matrix.permanent A ≤
      (∑ j : Fin 3, (∑ i : Fin 3, A i j) ^ 2) +
        (2 / 9 : ℝ) * (∑ i : Fin 3, A i 0) *
          (∑ i : Fin 3, A i 1) * (∑ i : Fin 3, A i 2) := by
-- BODY
  let c := fun j => ∑ i : Fin 3, A i j
  let d := fun i j => A i j - c j / 3
  have hc0 (j) : 0 ≤ c j := Finset.sum_nonneg fun i _ => hA i j
  have hd (i j) : |d i j| ≤ 2 / 3 := by
    have ha : A i j ≤ c j := Finset.single_le_sum (fun k _ => hA k j) (Finset.mem_univ i)
    rw [abs_le]
    dsimp [d]
    constructor <;> linarith [hA i j, hc j, hc0 j]
  have bilin (u v t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      -(t / 3) * (u * v) ≤ (u ^ 2 + v ^ 2) / 6 := by
    have h := mul_le_mul_of_nonneg_left
      (show -(u * v) ≤ (u ^ 2 + v ^ 2) / 2 by nlinarith [sq_nonneg (u + v)]) ht0
    have h' := mul_nonneg (sub_nonneg.mpr ht1) (add_nonneg (sq_nonneg u) (sq_nonneg v))
    nlinarith
  have cubic (u v w : ℝ) (hw : |w| ≤ 2 / 3) :
      2 * (u * v * w) ≤ (2 / 3) * (u ^ 2 + v ^ 2) := by
    have huv : |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (u + v), sq_nonneg (u - v)]
    have h := mul_le_mul huv hw (abs_nonneg w)
      (by positivity : 0 ≤ (u ^ 2 + v ^ 2) / 2)
    rw [← abs_mul] at h
    linarith [le_abs_self (u * v * w)]
  let R := fun i => d i 0 ^ 2 + d i 1 ^ 2 + d i 2 ^ 2
  let E := fun i => -(c 2 / 3) * (d i 0 * d i 1) -
    (c 1 / 3) * (d i 0 * d i 2) - (c 0 / 3) * (d i 1 * d i 2) +
    2 * (d i 0 * d i 1 * d i 2)
  have herr (i) : E i ≤ R i := by
    dsimp [E, R]
    have h01 := bilin (d i 0) (d i 1) (c 2) (hc0 2) (hc 2)
    have h02 := bilin (d i 0) (d i 2) (c 1) (hc0 1) (hc 1)
    have h12 := bilin (d i 1) (d i 2) (c 0) (hc0 0) (hc 0)
    have h012 := cubic (d i 0) (d i 1) (d i 2) (hd i 2)
    nlinarith [sq_nonneg (d i 2)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => herr i)
  have hR : 0 ≤ ∑ i : Fin 3, R i := by
    apply Finset.sum_nonneg
    intro i _
    dsimp [R]
    positivity
  have hp : Matrix.permanent A =
      A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 2 1 * A 1 2 +
      A 1 0 * A 0 1 * A 2 2 + A 1 0 * A 2 1 * A 0 2 +
      A 2 0 * A 0 1 * A 1 2 + A 2 0 * A 1 1 * A 0 2 := by
    have h : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
        {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
          Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1} := by decide
    rw [Matrix.permanent, h]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Fin.prod_univ_succ, Equiv.swap_apply_def, Equiv.Perm.mul_apply]
    <;> ring
  have hid : 3 * (∑ j : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
        if i < i' then A i j * A i' j else 0) + Matrix.permanent A =
      (∑ j : Fin 3, c j ^ 2) + (2 / 9 : ℝ) * c 0 * c 1 * c 2 -
        (3 / 2) * (∑ i : Fin 3, R i) + ∑ i : Fin 3, E i := by
    rw [hp]
    simp [E, R, d, c, Fin.sum_univ_three]
    <;> ring
  change _ ≤ (∑ j : Fin 3, c j ^ 2) + (2 / 9 : ℝ) * c 0 * c 1 * c 2
  linarith
