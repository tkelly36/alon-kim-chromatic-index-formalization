import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology

-- [TABLET NODE: ThreeUniformTwoSimpleEventualNumericalError]
theorem ThreeUniformTwoSimpleEventualNumericalError (eta : ℝ) (heta : 0 < eta) :
    ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      let t : ℝ := (D : ℝ) ^ (-(1 : ℝ) / 3)
      let r : ℝ := 1 + 18 * t
      (2 : ℝ) / 9 * t + 8 / (9 * (D : ℝ)) +
        r ^ 3 * (2 / (3 : ℝ) ^ 5) + (r ^ 2 - 1) * r / 9 ≤
        2 / (3 : ℝ) ^ 5 + eta := by
-- BODY
  have ht : Tendsto (fun D : ℕ => (D : ℝ) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 3)).comp
        tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun D : ℕ => (D : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun D : ℕ => 1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3))
      atTop (𝓝 1) := by
    convert tendsto_const_nhds.add (ht.const_mul 18) using 1 <;> norm_num
  have hlim : Tendsto (fun D : ℕ =>
      (2 : ℝ) / 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) + 8 / (9 * (D : ℝ)) +
      (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) ^ 3 * (2 / (3 : ℝ) ^ 5) +
      ((1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 - 1) *
        (1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)) / 9)
      atTop (𝓝 (2 / (3 : ℝ) ^ 5)) := by
    convert (((ht.const_mul ((2 : ℝ) / 9)).add (hu.const_mul ((8 : ℝ) / 9))).add
      ((hr.pow 3).mul_const (2 / (3 : ℝ) ^ 5))).add
        ((((hr.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).mul hr).div_const 9) using 1
    · ext D
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · norm_num
  obtain ⟨D0, hD0⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show 2 / (3 : ℝ) ^ 5 <
      2 / (3 : ℝ) ^ 5 + eta by linarith)))
  exact ⟨D0, fun D hD => (hD0 D hD).le⟩
