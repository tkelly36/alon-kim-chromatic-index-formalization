import Tablet.SamplingFiniteProductPointwiseLower
import Tablet.SamplingPairHighOverlapWindowLower

open BigOperators

-- [TABLET NODE: SamplingPairHighOverlapFiniteProductWindowLower]
theorem SamplingPairHighOverlapFiniteProductWindowLower
    (Delta N : ℕ) (L alpha : ℝ)
    (hD : 0 < (Delta : ℝ))
    (hL : 0 ≤ L)
    (hL_lt : L < (Delta : ℝ))
    (halpha_pos : 0 < 1 - alpha)
    (hN_le : (N : ℝ) ≤ (Delta : ℝ))
    (hN_ratio_le : (N : ℝ) / (Delta : ℝ) ≤ alpha)
    (hlarge : L^2 / ((Delta : ℝ) - L) ≤ - Real.log (1 - alpha))
    (hmargin :
      (5 / 3 + 2 * alpha) ≤
        2 *
          (∫ x in (0 : ℝ)..L,
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y)))) :
    (2 / (Delta : ℝ)^2) *
        (∫ x in (0 : ℝ)..L,
          ∫ y in x..L,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta) ≥
      (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 := by
-- BODY
  have hD_nonneg : 0 ≤ (Delta : ℝ) := le_of_lt hD
  have halpha_nonneg : 0 ≤ alpha := by
    have hratio_nonneg : 0 ≤ (N : ℝ) / (Delta : ℝ) := by positivity
    exact hratio_nonneg.trans hN_ratio_le
  refine SamplingPairHighOverlapWindowLower Delta L alpha N hD hL ?_ ?_
    (le_of_lt halpha_pos) hmargin
  · intro x hx
    have hx_nonneg : 0 ≤ x := hx.1
    have hx_le : x ≤ L := hx.2
    have hfinite :=
      SamplingFiniteProductPointwiseLower Delta N alpha L x hD halpha_pos
        hx_nonneg hx_le hL_lt hN_le hlarge
    have hratio_nonneg : 0 ≤ (N : ℝ) / (Delta : ℝ) := by positivity
    have hmul_le : ((N : ℝ) / (Delta : ℝ)) * x ≤ alpha * L := by
      calc
        ((N : ℝ) / (Delta : ℝ)) * x ≤ alpha * x := by
          exact mul_le_mul_of_nonneg_right hN_ratio_le hx_nonneg
        _ ≤ alpha * L := by
          exact mul_le_mul_of_nonneg_left hx_le halpha_nonneg
    have hexp :
        Real.exp (-(((N : ℝ) / (Delta : ℝ)) * x)) ≥
          Real.exp (-(alpha * L)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hmul_le)
    have hscale_nonneg : 0 ≤ 1 - alpha := le_of_lt halpha_pos
    exact (mul_le_mul_of_nonneg_left hexp hscale_nonneg).trans hfinite
  · intro y hy
    have hy_nonneg : 0 ≤ y := hy.1
    have hy_le : y ≤ L := hy.2
    have hfinite :=
      SamplingFiniteProductPointwiseLower Delta Delta alpha L y hD halpha_pos
        hy_nonneg hy_le hL_lt (by simp) hlarge
    have hratio : ((Delta : ℝ) / (Delta : ℝ)) * y = y := by
      field_simp [ne_of_gt hD]
    simpa [hratio] using hfinite
