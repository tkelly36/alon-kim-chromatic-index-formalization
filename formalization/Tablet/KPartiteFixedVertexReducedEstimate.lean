import Tablet.Preamble
import Tablet.KPartitePairProductCauchyBound
import Mathlib.Algebra.Order.Chebyshev

-- [TABLET NODE: KPartiteFixedVertexReducedEstimate]
theorem KPartiteFixedVertexReducedEstimate :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι],
      ∀ u : ι → ℝ, ∀ v : ι → ι → ℝ,
        (∀ a, 0 ≤ u a) →
        (∀ a b, 0 ≤ v a b) →
        0 < Fintype.card ι →
        let pairs : Finset (ι × ι) :=
          (Finset.univ.filter (fun p : ι × ι => p.1 < p.2))
        pairs.sum (fun p => Real.sqrt (u p.1 * u p.2 * v p.1 p.2)) ≤
          (∑ a : ι, u a) *
            Real.sqrt
              ((((Fintype.card ι : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) *
                pairs.sum (fun p => v p.1 p.2)) := by
-- BODY
  intro ι _ _ _ u v hu hv hcard pairs
  classical
  let A : ℝ := pairs.sum (fun p => u p.1 * u p.2)
  let B : ℝ := pairs.sum (fun p => v p.1 p.2)
  let S : ℝ := ∑ a : ι, u a
  let c : ℝ := (((Fintype.card ι : ℝ) - 1) / (2 * (Fintype.card ι : ℝ)))
  have hf : ∀ p : ι × ι, 0 ≤ u p.1 * u p.2 := by
    intro p
    exact mul_nonneg (hu p.1) (hu p.2)
  have hg : ∀ p : ι × ι, 0 ≤ v p.1 p.2 := by
    intro p
    exact hv p.1 p.2
  have hcs :
      (∑ p ∈ pairs,
          Real.sqrt (u p.1 * u p.2) * Real.sqrt (v p.1 p.2)) ≤
        Real.sqrt A * Real.sqrt B := by
    dsimp [A, B]
    simpa using
      (Real.sum_sqrt_mul_sqrt_le pairs
        (f := fun p : ι × ι => u p.1 * u p.2)
        (g := fun p : ι × ι => v p.1 p.2) hf hg)
  have hrewrite :
      pairs.sum (fun p => Real.sqrt (u p.1 * u p.2 * v p.1 p.2)) =
        ∑ p ∈ pairs,
          Real.sqrt (u p.1 * u p.2) * Real.sqrt (v p.1 p.2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Real.sqrt_mul (hf p) (v p.1 p.2)]
  have hpair_bound : A ≤ c * S ^ 2 := by
    dsimp [A, c, S, pairs]
    simpa using
      (KPartitePairProductCauchyBound (u := u) hcard)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (by
      intro a ha
      exact hu a)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (by
      intro p hp
      exact hv p.1 p.2)
  have hcard_real_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast hcard
  have hcard_real_one : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Nat.succ_le_of_lt hcard)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (sub_nonneg.mpr hcard_real_one)
      (mul_nonneg (by norm_num) (le_of_lt hcard_real_pos))
  have hsqrtA_le :
      Real.sqrt A ≤ Real.sqrt (c * S ^ 2) := by
    exact Real.sqrt_le_sqrt hpair_bound
  have hsqrt_cS :
      Real.sqrt (c * S ^ 2) = S * Real.sqrt c := by
    calc
      Real.sqrt (c * S ^ 2)
          = Real.sqrt c * Real.sqrt (S ^ 2) := by
              rw [Real.sqrt_mul hc_nonneg (S ^ 2)]
      _ = Real.sqrt c * S := by
              rw [Real.sqrt_sq hS_nonneg]
      _ = S * Real.sqrt c := by
              ring
  have hsqrt_cB :
      Real.sqrt c * Real.sqrt B = Real.sqrt (c * B) := by
    rw [Real.sqrt_mul hc_nonneg B]
  rw [hrewrite]
  calc
    (∑ p ∈ pairs, Real.sqrt (u p.1 * u p.2) * Real.sqrt (v p.1 p.2))
        ≤ Real.sqrt A * Real.sqrt B := hcs
    _ ≤ Real.sqrt (c * S ^ 2) * Real.sqrt B := by
          exact mul_le_mul_of_nonneg_right hsqrtA_le (Real.sqrt_nonneg B)
    _ = S * Real.sqrt (c * B) := by
          rw [hsqrt_cS]
          calc
            (S * Real.sqrt c) * Real.sqrt B
                = S * (Real.sqrt c * Real.sqrt B) := by ring
            _ = S * Real.sqrt (c * B) := by rw [hsqrt_cB]
