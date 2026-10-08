import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring

-- [TABLET NODE: NibbleCeilingPowerEstimate]
theorem NibbleCeilingPowerEstimate (iota gamma delta : ℝ)
    (hg : 1 ≤ gamma) (hd : 4 ≤ delta)
    (he : Real.exp (-gamma) ≤ min (1 / 4) (iota / 8))
    (hi : 1 / gamma ≤ iota / 4) (hiD : 2 / delta ≤ iota / 8) :
    (1 - (1 - Real.exp (-gamma)) / delta + 2 / delta ^ 2) ^
      Nat.ceil (delta / gamma) ≤ 1 - (1 - iota / 2) / gamma := by
-- BODY
  have hg0 : 0 < gamma := by linarith
  have hd0 : 0 < delta := by linarith
  let u := 1 - Real.exp (-gamma) - 2 / delta
  have hdiv : 2 / delta ≤ (1 / 2 : ℝ) := (div_le_iff₀ hd0).2 (by linarith)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [he.trans (min_le_left _ _)]
  have hu1 : u ≤ 1 := by
    dsimp [u]
    linarith [Real.exp_pos (-gamma), div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0.le]
  have hbase : 0 ≤ 1 - u / delta := by
    have : u / delta ≤ 1 := (div_le_iff₀ hd0).2 (by linarith)
    linarith
  have hrewrite : 1 - (1 - Real.exp (-gamma)) / delta + 2 / delta ^ 2 =
      1 - u / delta := by dsimp [u]; field_simp; ring
  have hceil : delta / gamma ≤ (Nat.ceil (delta / gamma) : ℝ) := Nat.le_ceil _
  have hpow : (1 - u / delta) ^ Nat.ceil (delta / gamma) ≤ Real.exp (-u / gamma) := by
    calc
      _ ≤ (Real.exp (-u / delta)) ^ Nat.ceil (delta / gamma) := by
        apply pow_le_pow_left₀ hbase
        have := Real.add_one_le_exp (-u / delta)
        simpa only [neg_div, sub_eq_add_neg, add_comm] using this
      _ = Real.exp ((Nat.ceil (delta / gamma) : ℝ) * (-u / delta)) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-u / gamma) := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (delta / gamma) * (-u / delta) :=
            mul_le_mul_of_nonpos_right hceil (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu0) hd0.le)
          _ = _ := by field_simp
  have hug : 0 ≤ u / gamma := div_nonneg hu0 hg0.le
  have hug1 : u / gamma ≤ 1 := (div_le_iff₀ hg0).2 (by linarith)
  have hexp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (x := -(u / gamma)) (by rw [abs_neg, abs_of_nonneg hug]; exact hug1))).2
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  have herr : Real.exp (-gamma) + 2 / delta + u ^ 2 / gamma ≤ iota / 2 := by
    have : u ^ 2 / gamma ≤ 1 / gamma := div_le_div_of_nonneg_right hu2 hg0.le
    linarith [he.trans (min_le_right _ _)]
  have hlast : 1 - u / gamma + (u / gamma) ^ 2 ≤ 1 - (1 - iota / 2) / gamma := by
    have := (div_le_div_of_nonneg_right herr hg0.le)
    dsimp [u] at *
    field_simp at this ⊢
    nlinarith
  rw [hrewrite]
  apply hpow.trans
  apply le_trans _ hlast
  rw [neg_div]
  nlinarith
