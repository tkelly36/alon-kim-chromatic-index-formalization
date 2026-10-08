import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Tablet.Preamble

open BigOperators Filter
open scoped Topology

-- [TABLET NODE: SamplingPairBonferroniParameterSelection]
theorem SamplingPairBonferroniParameterSelection (eta : ℝ) (heta : 0 < eta) :
    ∃ alpha L gamma0 : ℝ, ∃ Delta0 : ℕ,
      0 < alpha ∧ alpha ≤ 1 ∧ 0 < 1 - alpha ∧
      0 ≤ L ∧ 0 ≤ gamma0 ∧
      3 * alpha ≤ eta / 3 ∧
      Real.exp (-gamma0) * (1 + 1 / alpha) ≤ alpha ∧
      (5 / 3 + 2 * alpha) ≤
        2 * ((1 - alpha)^2 * Real.exp (-(alpha * L)) *
          (∫ x in (0 : ℝ)..L, Real.exp (-x) - Real.exp (-L))) ∧
      ∀ Delta : ℕ, Delta0 ≤ Delta →
        gamma0 < (Delta : ℝ) ∧ L < (Delta : ℝ) ∧
        gamma0^2 / ((Delta : ℝ) - gamma0) ≤ - Real.log (1 - alpha) ∧
        L^2 / ((Delta : ℝ) - L) ≤ - Real.log (1 - alpha) := by
-- BODY
  let alpha : ℝ := min (1 / 1000) (eta / 9)
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    exact lt_min (by norm_num) (by positivity)
  have halpha_le_small : alpha ≤ 1 / 1000 := by
    dsimp [alpha]
    exact min_le_left _ _
  have halpha_le_eta : alpha ≤ eta / 9 := by
    dsimp [alpha]
    exact min_le_right _ _
  have halpha_le_one : alpha ≤ 1 := by
    linarith
  have halpha_lt_one : alpha < 1 := lt_of_le_of_lt halpha_le_small (by norm_num)
  have halpha_one_pos : 0 < 1 - alpha := by linarith
  have hthree : 3 * alpha ≤ eta / 3 := by linarith
  have hlogpos : 0 < - Real.log (1 - alpha) := by
    have hlt : 1 - alpha < 1 := by linarith
    have hlogneg : Real.log (1 - alpha) < 0 := Real.log_neg halpha_one_pos hlt
    linarith
  have htail_event :
      ∀ᶠ t : ℝ in atTop, Real.exp (-t) * (1 + 1 / alpha) ≤ alpha := by
    have hcpos : 0 < alpha / (1 + 1 / alpha) := by positivity
    have htend := Real.tendsto_exp_neg_atTop_nhds_zero
    have hsmall : ∀ᶠ t : ℝ in atTop, Real.exp (-t) < alpha / (1 + 1 / alpha) := by
      rcases Metric.tendsto_atTop.mp htend (alpha / (1 + 1 / alpha)) hcpos with ⟨N, hN⟩
      exact eventually_atTop.mpr ⟨N, fun t ht => by
        have hd := hN t ht
        rwa [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at hd⟩
    filter_upwards [hsmall] with t ht
    have hden_pos : 0 < 1 + 1 / alpha := by positivity
    exact (le_of_lt ((lt_div_iff₀ hden_pos).mp ht))
  rcases eventually_atTop.mp htail_event with ⟨gamma0, hgamma0_tail_all⟩
  let gamma0' : ℝ := max gamma0 0
  have hgamma0_nonneg : 0 ≤ gamma0' := by dsimp [gamma0']; exact le_max_right _ _
  have htail : Real.exp (-gamma0') * (1 + 1 / alpha) ≤ alpha := by
    apply hgamma0_tail_all
    dsimp [gamma0']
    exact le_max_left _ _
  have hexp6_gt64 : (64 : ℝ) < Real.exp 6 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have hpow : (2 : ℝ)^6 < (Real.exp 1)^6 :=
      pow_lt_pow_left₀ h2 (by norm_num) (by norm_num)
    norm_num at hpow
    simpa [Real.exp_nat_mul, mul_comm] using hpow
  have hexp_neg6_le : Real.exp (-(6 : ℝ)) ≤ 1 / 64 := by
    rw [Real.exp_neg]
    simpa [one_div] using (inv_le_inv₀ (Real.exp_pos 6)
      (by norm_num : (0 : ℝ) < 64)).2 (le_of_lt hexp6_gt64)
  have hint_eq :
      (∫ x in (0 : ℝ)..(6 : ℝ), Real.exp (-x) - Real.exp (-(6 : ℝ))) =
        1 - 7 * Real.exp (-(6 : ℝ)) := by
    have hderiv : ∀ x : ℝ,
        HasDerivAt (fun t : ℝ => - Real.exp (-t) - t * Real.exp (-(6 : ℝ)))
          (Real.exp (-x) - Real.exp (-(6 : ℝ))) x := by
      intro x
      have hinner : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) x := by
        simpa using (hasDerivAt_id x).neg
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t))
          (Real.exp (-x) * (-1 : ℝ)) x := by
        simpa using (Real.hasDerivAt_exp (-x)).comp x hinner
      have h2 := h1.neg
      have h3 : HasDerivAt (fun t : ℝ => t * Real.exp (-(6 : ℝ)))
          (Real.exp (-(6 : ℝ))) x := by
        simpa [mul_comm] using (hasDerivAt_id x).const_mul (Real.exp (-(6 : ℝ)))
      simpa [sub_eq_add_neg] using h2.sub h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx => hderiv x)
      (((Real.continuous_exp.comp
        (by fun_prop : Continuous fun x : ℝ => -x)).sub continuous_const).intervalIntegrable 0 6)]
    simp [Real.exp_zero]
    ring
  have hint_lower :
      (57 / 64 : ℝ) ≤
        (∫ x in (0 : ℝ)..(6 : ℝ), Real.exp (-x) - Real.exp (-(6 : ℝ))) := by
    rw [hint_eq]
    nlinarith
  have hone_sub_sq_lower : (998001 / 1000000 : ℝ) ≤ (1 - alpha)^2 := by
    have h : (999 / 1000 : ℝ) ≤ 1 - alpha := by linarith
    nlinarith
  have hexp_alpha_lower : (497 / 500 : ℝ) ≤ Real.exp (-(alpha * 6)) := by
    have hbase : 1 - alpha * 6 ≤ Real.exp (-(alpha * 6)) := by
      linarith [Real.add_one_le_exp (-(alpha * 6))]
    have hlin : (497 / 500 : ℝ) ≤ 1 - alpha * 6 := by linarith
    exact hlin.trans hbase
  have hnumeric :
      (5 / 3 + 2 * alpha) ≤
        2 * ((1 - alpha)^2 * Real.exp (-(alpha * (6 : ℝ))) *
          (∫ x in (0 : ℝ)..(6 : ℝ), Real.exp (-x) - Real.exp (-(6 : ℝ)))) := by
    have hprod :
        (2 : ℝ) * ((998001 / 1000000) * (497 / 500) * (57 / 64)) ≤
          2 * ((1 - alpha)^2 * Real.exp (-(alpha * (6 : ℝ))) *
            (∫ x in (0 : ℝ)..(6 : ℝ), Real.exp (-x) - Real.exp (-(6 : ℝ)))) := by
      have hAB :
          (998001 / 1000000 : ℝ) * (497 / 500) ≤
            (1 - alpha)^2 * Real.exp (-(alpha * (6 : ℝ))) := by
        exact mul_le_mul hone_sub_sq_lower hexp_alpha_lower (by norm_num)
          (le_trans (by norm_num) hone_sub_sq_lower)
      have hABC :
          (998001 / 1000000 : ℝ) * (497 / 500) * (57 / 64) ≤
            (1 - alpha)^2 * Real.exp (-(alpha * (6 : ℝ))) *
              (∫ x in (0 : ℝ)..(6 : ℝ), Real.exp (-x) - Real.exp (-(6 : ℝ))) := by
        exact mul_le_mul hAB hint_lower (by norm_num)
          (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      nlinarith
    have hmargin : (5 / 3 + 2 * alpha) ≤
        (2 : ℝ) * ((998001 / 1000000) * (497 / 500) * (57 / 64)) := by
      nlinarith
    exact hmargin.trans hprod
  have hlarge_event :
      ∀ᶠ Delta : ℕ in atTop,
        gamma0' < (Delta : ℝ) ∧ (6 : ℝ) < (Delta : ℝ) ∧
        gamma0'^2 / ((Delta : ℝ) - gamma0') ≤ - Real.log (1 - alpha) ∧
        (6 : ℝ)^2 / ((Delta : ℝ) - (6 : ℝ)) ≤ - Real.log (1 - alpha) := by
    have hcast : Tendsto (fun Delta : ℕ => (Delta : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hgamma_lt : ∀ᶠ Delta : ℕ in atTop, gamma0' < (Delta : ℝ) :=
      hcast.eventually_gt_atTop gamma0'
    have hL_lt : ∀ᶠ Delta : ℕ in atTop, (6 : ℝ) < (Delta : ℝ) :=
      hcast.eventually_gt_atTop 6
    have hden_gamma : Tendsto (fun Delta : ℕ => (Delta : ℝ) - gamma0') atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-gamma0') hcast
    have hden_L : Tendsto (fun Delta : ℕ => (Delta : ℝ) - (6 : ℝ)) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(6 : ℝ)) hcast
    have hquot_gamma :
        Tendsto (fun Delta : ℕ => gamma0'^2 / ((Delta : ℝ) - gamma0')) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden_gamma
    have hquot_L :
        Tendsto (fun Delta : ℕ => (6 : ℝ)^2 / ((Delta : ℝ) - (6 : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden_L
    have hgamma_bound_lt :
        ∀ᶠ Delta : ℕ in atTop,
          gamma0'^2 / ((Delta : ℝ) - gamma0') < - Real.log (1 - alpha) :=
      (tendsto_order.1 hquot_gamma).2 _ hlogpos
    have hgamma_bound :
        ∀ᶠ Delta : ℕ in atTop,
          gamma0'^2 / ((Delta : ℝ) - gamma0') ≤ - Real.log (1 - alpha) :=
      hgamma_bound_lt.mono fun _ h => le_of_lt h
    have hL_bound_lt :
        ∀ᶠ Delta : ℕ in atTop,
          (6 : ℝ)^2 / ((Delta : ℝ) - (6 : ℝ)) < - Real.log (1 - alpha) :=
      (tendsto_order.1 hquot_L).2 _ hlogpos
    have hL_bound :
        ∀ᶠ Delta : ℕ in atTop,
          (6 : ℝ)^2 / ((Delta : ℝ) - (6 : ℝ)) ≤ - Real.log (1 - alpha) :=
      hL_bound_lt.mono fun _ h => le_of_lt h
    filter_upwards [hgamma_lt, hL_lt, hgamma_bound, hL_bound] with Delta hgt hLt hgb hLb
    exact ⟨hgt, hLt, hgb, hLb⟩
  rcases eventually_atTop.mp hlarge_event with ⟨Delta0, hDelta0⟩
  refine ⟨alpha, 6, gamma0', Delta0, halpha_pos, halpha_le_one, halpha_one_pos,
    by norm_num, hgamma0_nonneg, hthree, htail, ?_, ?_⟩
  · simpa using hnumeric
  · exact hDelta0
