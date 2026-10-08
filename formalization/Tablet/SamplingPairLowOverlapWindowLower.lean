import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Tablet.SamplingFiniteProductPointwiseLower

open BigOperators

-- [TABLET NODE: SamplingPairLowOverlapWindowLower]
theorem SamplingPairLowOverlapWindowLower
    (Delta N : ℕ) (gamma gamma0 alpha lambda : ℝ)
    (hD : 0 < (Delta : ℝ))
    (hgamma0_nonneg : 0 ≤ gamma0)
    (hgamma0_le_gamma : gamma0 ≤ gamma)
    (hgamma_le : gamma ≤ (Delta : ℝ))
    (hgamma0_lt : gamma0 < (Delta : ℝ))
    (halpha_pos : 0 < 1 - alpha)
    (hN_le : (N : ℝ) ≤ (Delta : ℝ))
    (hN_ratio : (N : ℝ) / (Delta : ℝ) = lambda)
    (hlarge : gamma0^2 / ((Delta : ℝ) - gamma0) ≤ - Real.log (1 - alpha))
    (hmargin :
      2 *
          (∫ x in (0 : ℝ)..gamma0,
            ∫ y in x..gamma0,
              ((1 - alpha) * Real.exp (-(lambda * x))) *
                ((1 - alpha) * Real.exp (-y))) ≥
        2 / (1 + lambda) - 6 * alpha) :
    (2 / (Delta : ℝ)^2) *
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta) ≥
      (2 / (1 + lambda) - 6 * alpha) / (Delta : ℝ)^2 := by
-- BODY
  let d : ℝ := (Delta : ℝ)
  have hd_pos : 0 < d := hD
  have hd_sq_pos : 0 < d ^ 2 := sq_pos_of_pos hd_pos
  have hgamma_nonneg : 0 ≤ gamma := hgamma0_nonneg.trans hgamma0_le_gamma
  have halpha_nonneg : 0 ≤ 1 - alpha := le_of_lt halpha_pos
  let F : ℝ → ℝ → ℝ := fun x y =>
    (1 - x / d) ^ N * (1 - y / d) ^ Delta
  let E : ℝ → ℝ → ℝ := fun x y =>
    ((1 - alpha) * Real.exp (-(lambda * x))) *
      ((1 - alpha) * Real.exp (-y))
  have hF_cont : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    dsimp [F, d]
    fun_prop
  have hE_cont : Continuous fun p : ℝ × ℝ => E p.1 p.2 := by
    dsimp [E]
    fun_prop
  have hF_inner_int (a b x : ℝ) :
      IntervalIntegrable (fun y : ℝ => F x y) MeasureTheory.volume a b := by
    exact ((hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable a b)
  have hE_inner_int (a b x : ℝ) :
      IntervalIntegrable (fun y : ℝ => E x y) MeasureTheory.volume a b := by
    exact ((hE_cont.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable a b)
  have hF_outer_cont (b : ℝ) :
      Continuous fun x : ℝ => ∫ y in x..b, F x y := by
    have htop : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..b, F x y :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
        (s := fun _x : ℝ => b) hF_cont (by fun_prop)
    have hbot : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..x, F x y :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
        (s := fun x : ℝ => x) hF_cont (by fun_prop)
    have heq :
        (fun x : ℝ => ∫ y in x..b, F x y) =
          fun x : ℝ => (∫ y in (0 : ℝ)..b, F x y) -
            ∫ y in (0 : ℝ)..x, F x y := by
      ext x
      exact (intervalIntegral.integral_interval_sub_left
        (hF_inner_int 0 b x) (hF_inner_int 0 x x)).symm
    rw [heq]
    exact htop.sub hbot
  have hE_outer_cont (b : ℝ) :
      Continuous fun x : ℝ => ∫ y in x..b, E x y := by
    have htop : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..b, E x y :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := E) (a₀ := (0 : ℝ))
        (s := fun _x : ℝ => b) hE_cont (by fun_prop)
    have hbot : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..x, E x y :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := E) (a₀ := (0 : ℝ))
        (s := fun x : ℝ => x) hE_cont (by fun_prop)
    have heq :
        (fun x : ℝ => ∫ y in x..b, E x y) =
          fun x : ℝ => (∫ y in (0 : ℝ)..b, E x y) -
            ∫ y in (0 : ℝ)..x, E x y := by
      ext x
      exact (intervalIntegral.integral_interval_sub_left
        (hE_inner_int 0 b x) (hE_inner_int 0 x x)).symm
    rw [heq]
    exact htop.sub hbot
  have hF_outer_int (a b c : ℝ) :
      IntervalIntegrable (fun x : ℝ => ∫ y in x..c, F x y)
        MeasureTheory.volume a b :=
    (hF_outer_cont c).intervalIntegrable a b
  have hE_outer_int (a b c : ℝ) :
      IntervalIntegrable (fun x : ℝ => ∫ y in x..c, E x y)
        MeasureTheory.volume a b :=
    (hE_outer_cont c).intervalIntegrable a b
  have hpoint :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) gamma0 →
        ∀ y : ℝ, y ∈ Set.Icc x gamma0 → E x y ≤ F x y := by
    intro x hx y hy
    have hx_nonneg : 0 ≤ x := hx.1
    have hx_le : x ≤ gamma0 := hx.2
    have hy_nonneg : 0 ≤ y := le_trans hx_nonneg hy.1
    have hy_le : y ≤ gamma0 := hy.2
    have hx_bound :=
      SamplingFiniteProductPointwiseLower Delta N alpha gamma0 x hD halpha_pos
        hx_nonneg hx_le hgamma0_lt hN_le hlarge
    have hy_bound :=
      SamplingFiniteProductPointwiseLower Delta Delta alpha gamma0 y hD halpha_pos
        hy_nonneg hy_le hgamma0_lt (by simp [d]) hlarge
    have hx_bound' :
        (1 - x / d) ^ N ≥ (1 - alpha) * Real.exp (-(lambda * x)) := by
      simpa [d, hN_ratio] using hx_bound
    have hy_bound' :
        (1 - y / d) ^ Delta ≥ (1 - alpha) * Real.exp (-y) := by
      have hratio : ((Delta : ℝ) / d) * y = y := by
        rw [show (Delta : ℝ) = d by rfl]
        field_simp [ne_of_gt hd_pos]
      simpa [d, hratio] using hy_bound
    have hEy_nonneg : 0 ≤ (1 - alpha) * Real.exp (-y) :=
      mul_nonneg halpha_nonneg (Real.exp_pos _).le
    have hEx_nonneg : 0 ≤ (1 - alpha) * Real.exp (-(lambda * x)) :=
      mul_nonneg halpha_nonneg (Real.exp_pos _).le
    exact mul_le_mul hx_bound' hy_bound' hEy_nonneg (le_trans hEx_nonneg hx_bound')
  have hwindow_exp_le_finite :
      (∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma0, E x y) ≤
        ∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma0, F x y := by
    refine intervalIntegral.integral_mono_on hgamma0_nonneg
      (hE_outer_int 0 gamma0 gamma0) (hF_outer_int 0 gamma0 gamma0) ?_
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) gamma0 := by simpa using hx
    refine intervalIntegral.integral_mono_on hx.2
      (hE_inner_int x gamma0 x) (hF_inner_int x gamma0 x) ?_
    intro y hy
    exact hpoint x hxI y (by simpa using hy)
  have hF_nonneg_on :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) gamma →
        0 ≤ ∫ y in x..gamma, F x y := by
    intro x hx
    refine intervalIntegral.integral_nonneg hx.2 ?_
    intro y hy
    have hx_le_d : x ≤ d := by
      exact hx.2.trans hgamma_le
    have hbase_x_nonneg : 0 ≤ 1 - x / d := by
      have hdiv : x / d ≤ 1 := (div_le_one hd_pos).2 hx_le_d
      linarith
    have hbase_y_nonneg : 0 ≤ 1 - y / d := by
      have hyd : y ≤ d := hy.2.trans hgamma_le
      have hdiv : y / d ≤ 1 := (div_le_one hd_pos).2 hyd
      linarith
    exact mul_nonneg (pow_nonneg hbase_x_nonneg _) (pow_nonneg hbase_y_nonneg _)
  have hwindow_finite_le_full :
      (∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma0, F x y) ≤
        ∫ x in (0 : ℝ)..gamma, ∫ y in x..gamma, F x y := by
    have hinner_mono :
        (∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma0, F x y) ≤
          ∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma, F x y := by
      refine intervalIntegral.integral_mono_on hgamma0_nonneg
        (hF_outer_int 0 gamma0 gamma0) (hF_outer_int 0 gamma0 gamma) ?_
      intro x hx
      refine intervalIntegral.integral_mono_interval
        (f := fun y : ℝ => F x y) (μ := MeasureTheory.volume)
        (a := x) (b := gamma0) (c := x) (d := gamma)
        le_rfl hx.2 hgamma0_le_gamma ?_ (hF_inner_int x gamma x)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
      have hx_nonneg : 0 ≤ x := hx.1
      have hbase_x_nonneg : 0 ≤ 1 - x / d := by
        have hx_lt_d : x < d := lt_of_le_of_lt hx.2 hgamma0_lt
        have hdiv : x / d ≤ 1 := (div_le_one hd_pos).2 (le_of_lt hx_lt_d)
        linarith
      have hbase_y_nonneg : 0 ≤ 1 - y / d := by
        have hyd : y ≤ d := hy.2.trans hgamma_le
        have hdiv : y / d ≤ 1 := (div_le_one hd_pos).2 hyd
        linarith
      exact mul_nonneg (pow_nonneg hbase_x_nonneg _) (pow_nonneg hbase_y_nonneg _)
    have houter_mono :
        (∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma, F x y) ≤
          ∫ x in (0 : ℝ)..gamma, ∫ y in x..gamma, F x y := by
      refine intervalIntegral.integral_mono_interval
        (f := fun x : ℝ => ∫ y in x..gamma, F x y) (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := gamma0) (c := (0 : ℝ)) (d := gamma)
        le_rfl hgamma0_nonneg hgamma0_le_gamma ?_ (hF_outer_int 0 gamma gamma)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact hF_nonneg_on x ⟨le_of_lt hx.1, hx.2⟩
    exact hinner_mono.trans houter_mono
  have hwindow :
      (∫ x in (0 : ℝ)..gamma0, ∫ y in x..gamma0, E x y) ≤
        ∫ x in (0 : ℝ)..gamma, ∫ y in x..gamma, F x y :=
    hwindow_exp_le_finite.trans hwindow_finite_le_full
  have hscaled :
      (2 / (1 + lambda) - 6 * alpha) / d ^ 2 ≤
        (2 / d ^ 2) *
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              F x y) := by
    calc
      (2 / (1 + lambda) - 6 * alpha) / d ^ 2
          ≤ (2 *
              (∫ x in (0 : ℝ)..gamma0,
                ∫ y in x..gamma0,
                  E x y)) / d ^ 2 := by
            exact div_le_div_of_nonneg_right hmargin hd_sq_pos.le
      _ ≤ (2 *
              (∫ x in (0 : ℝ)..gamma,
                ∫ y in x..gamma,
                  F x y)) / d ^ 2 := by
            gcongr
      _ = (2 / d ^ 2) *
              (∫ x in (0 : ℝ)..gamma,
                ∫ y in x..gamma,
                  F x y) := by
            ring
  simpa [F, d] using hscaled
