import Tablet.BoundedSquaresInterval

open scoped BigOperators

-- [TABLET NODE: T2DegreeSquareAssembly]
theorem T2DegreeSquareAssembly {A : Type*} [Fintype A]
    (q c y : A → ℝ) (D eps m B Y : ℝ)
    (hD : 0 ≤ D) (he : 0 < eps) (he' : eps ≤ 1 / 2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 2 * D ∧ q i ≤ 2 * D - c i + y i)
    (hy : ∀ i, 0 ≤ y i) (hY : ∑ i, y i ≤ 2 * Y)
    (hc : ∀ i, |c i - (4 / 3) * D| ≤ eps * D)
    (hs : 2 * B - D * m ≤ ∑ i, c i) :
    (∑ i, q i ^ 2) ≤ ((20 / 9 : ℝ) + eps ^ 2) * Fintype.card A * D ^ 2 -
      (8 / 3 : ℝ) * D * B + (4 / 3 : ℝ) * m * D ^ 2 +
      ((16 / 3 : ℝ) + 2 * eps) * D * Y := by
-- BODY
  classical
  let d : A → ℝ := fun i => 2 * D - c i
  have hd (i : A) : ((2 / 3 : ℝ) - eps) * D ≤ d i ∧
      d i ≤ ((2 / 3 : ℝ) + eps) * D := by
    have := abs_le.mp (hc i)
    dsimp [d]
    constructor <;> linarith
  have hd0 (i : A) : 0 ≤ d i := by
    have := mul_nonneg (show 0 ≤ (2 / 3 : ℝ) - eps by linarith) hD
    linarith [(hd i).1]
  let e := (Fintype.equivFin A).symm
  have hb := BoundedSquaresInterval (((2 / 3 : ℝ) - eps) * D)
    (((2 / 3 : ℝ) + eps) * D) (fun i => d (e i))
    (by nlinarith [mul_nonneg (le_of_lt he) hD]) (fun i => hd (e i))
  rw [e.sum_comp (fun i => d i ^ 2), e.sum_comp d] at hb
  have hb' : (∑ i, d i ^ 2) ≤ (4 / 3 : ℝ) * D * (∑ i, d i) -
      (Fintype.card A : ℝ) * ((4 / 9 : ℝ) - eps ^ 2) * D ^ 2 := by
    nlinarith only [hb]
  have hp (i : A) : q i ^ 2 ≤ d i ^ 2 +
      (((2 / 3 : ℝ) + eps) * D + 2 * D) * y i := by
    have h1 := mul_le_mul_of_nonneg_right (hq i).2.2 (hq i).1
    have h2 := mul_le_mul_of_nonneg_left (hq i).2.2 (hd0 i)
    have h3 := mul_le_mul_of_nonneg_right (hd i).2 (hy i)
    have h4 := mul_le_mul_of_nonneg_left (hq i).2.1 (hy i)
    dsimp [d] at *
    nlinarith only [h1, h2, h3, h4]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hcoef : 0 ≤ (((2 / 3 : ℝ) + eps) * D + 2 * D) := by positivity
  have hyb := mul_le_mul_of_nonneg_left hY hcoef
  have hds : (∑ i, d i) ≤ 2 * D * Fintype.card A - 2 * B + D * m := by
    simp only [d, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    linarith
  have hds' := mul_le_mul_of_nonneg_left hds (show 0 ≤ (4 / 3 : ℝ) * D by positivity)
  nlinarith only [hsum, hyb, hb', hds']
