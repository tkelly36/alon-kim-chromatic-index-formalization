import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTripleSingleChamberIntegralEstimate]
theorem SamplingTripleSingleChamberIntegralEstimate
    (Delta : ℕ) (gamma : ℝ)
    (a rho : ℝ) (N L : ℕ)
    (hDelta_pos : 0 < (Delta : ℝ))
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (Delta : ℝ))
    (ha : 0 < a) (hrho : 0 ≤ rho)
    (hN : ((N : ℝ) / (Delta : ℝ)) = a)
    (hL : ((L : ℝ) / (Delta : ℝ)) = rho) :
    2 *
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N *
                  (1 - u / (Delta : ℝ)) ^ L) ≤
      2 / ((1 + a) * (1 + a + rho)) := by
-- BODY
  have hcont_left :
      ∀ f : ℝ → ℝ, Continuous f → Continuous (fun x : ℝ => ∫ y in x..gamma, f y) := by
    intro f hf
    have hprim : Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..x, f y) :=
      (intervalIntegral.differentiable_integral_of_continuous (a := (0 : ℝ)) hf).continuous
    have h :
        (fun x : ℝ => ∫ y in x..gamma, f y) =
          (fun x : ℝ => (∫ y in (0 : ℝ)..gamma, f y) - ∫ y in (0 : ℝ)..x, f y) := by
      ext x
      exact (intervalIntegral.integral_interval_sub_left
        (hf.intervalIntegrable 0 gamma) (hf.intervalIntegrable 0 x)).symm
    rw [h]
    continuity
  have hfinite_v_int :
      ∀ u : ℝ,
        IntervalIntegrable
          (fun v : ℝ =>
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N *
                  (1 - u / (Delta : ℝ)) ^ L)
          MeasureTheory.volume u gamma := by
    intro u
    let T : ℝ → ℝ :=
      fun v =>
        (∫ w in v..gamma, (1 - w / (Delta : ℝ)) ^ Delta) *
          (1 - v / (Delta : ℝ)) ^ N *
            (1 - u / (Delta : ℝ)) ^ L
    have hT : Continuous T := by
      dsimp [T]
      fun_prop (disch := first | exact hcont_left _ (by fun_prop) | fun_prop)
    have heq :
        (fun v : ℝ =>
          ∫ w in v..gamma,
            (1 - w / (Delta : ℝ)) ^ Delta *
              (1 - v / (Delta : ℝ)) ^ N *
                (1 - u / (Delta : ℝ)) ^ L) = T := by
      ext v
      dsimp [T]
      simp only [intervalIntegral.integral_mul_const, mul_assoc]
    rw [heq]
    exact hT.intervalIntegrable u gamma
  have hexp_v_int :
      ∀ u : ℝ,
        IntervalIntegrable
          (fun v : ℝ =>
            ∫ w in v..gamma,
              Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)))
          MeasureTheory.volume u gamma := by
    intro u
    let T : ℝ → ℝ :=
      fun v => (∫ w in v..gamma, Real.exp (-w)) * Real.exp (-(a * v)) *
        Real.exp (-(rho * u))
    have hT : Continuous T := by
      dsimp [T]
      fun_prop (disch := first | exact hcont_left _ (by fun_prop) | fun_prop)
    have heq :
        (fun v : ℝ =>
          ∫ w in v..gamma,
            Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u))) = T := by
      ext v
      dsimp [T]
      simp only [intervalIntegral.integral_mul_const, mul_assoc]
    rw [heq]
    exact hT.intervalIntegrable u gamma
  have hfinite_outer_int :
      IntervalIntegrable
        (fun u : ℝ =>
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N *
                  (1 - u / (Delta : ℝ)) ^ L)
        MeasureTheory.volume 0 gamma := by
    let Hfin : ℝ → ℝ :=
      fun v => (∫ w in v..gamma, (1 - w / (Delta : ℝ)) ^ Delta) *
        (1 - v / (Delta : ℝ)) ^ N
    have hHfin : Continuous Hfin := by
      dsimp [Hfin]
      fun_prop (disch := first | exact hcont_left _ (by fun_prop) | fun_prop)
    have houter :
        Continuous
          (fun u : ℝ => (∫ v in u..gamma, Hfin v) *
            (1 - u / (Delta : ℝ)) ^ L) := by
      fun_prop (disch := first | exact hcont_left _ hHfin | fun_prop)
    have heq :
        (fun u : ℝ =>
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N *
                  (1 - u / (Delta : ℝ)) ^ L) =
          (fun u : ℝ => (∫ v in u..gamma, Hfin v) *
            (1 - u / (Delta : ℝ)) ^ L) := by
      ext u
      dsimp [Hfin]
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [intervalIntegral.integral_mul_const, mul_assoc]
    rw [heq]
    exact houter.intervalIntegrable 0 gamma
  have hexp_outer_int :
      IntervalIntegrable
        (fun u : ℝ =>
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)))
        MeasureTheory.volume 0 gamma := by
    let Hexp : ℝ → ℝ :=
      fun v => (∫ w in v..gamma, Real.exp (-w)) * Real.exp (-(a * v))
    have hHexp : Continuous Hexp := by
      dsimp [Hexp]
      fun_prop (disch := first | exact hcont_left _ (by fun_prop) | fun_prop)
    have houter :
        Continuous
          (fun u : ℝ => (∫ v in u..gamma, Hexp v) * Real.exp (-(rho * u))) := by
      fun_prop (disch := first | exact hcont_left _ hHexp | fun_prop)
    have heq :
        (fun u : ℝ =>
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u))) =
          (fun u : ℝ => (∫ v in u..gamma, Hexp v) * Real.exp (-(rho * u))) := by
      ext u
      dsimp [Hexp]
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro v hv
      simp only [intervalIntegral.integral_mul_const, mul_assoc]
    rw [heq]
    exact houter.intervalIntegrable 0 gamma
  have hpointwise :
      ∀ u ∈ Set.Icc (0 : ℝ) gamma, ∀ v ∈ Set.Icc u gamma, ∀ w ∈ Set.Icc v gamma,
        (1 - w / (Delta : ℝ)) ^ Delta *
              (1 - v / (Delta : ℝ)) ^ N *
                (1 - u / (Delta : ℝ)) ^ L ≤
          Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)) := by
    intro u hu v hv w hw
    have hu_nonneg : 0 ≤ u := hu.1
    have huv : u ≤ v := hv.1
    have hvw : v ≤ w := hw.1
    have hwg : w ≤ gamma := hw.2
    have hwD : w ≤ (Delta : ℝ) := hwg.trans hgamma_le
    have hvD : v ≤ (Delta : ℝ) := hvw.trans hwD
    have huD : u ≤ (Delta : ℝ) := (huv.trans hvw).trans hwD
    have huD' : u / (Delta : ℝ) ≤ 1 := (div_le_one hDelta_pos).2 huD
    have hvD' : v / (Delta : ℝ) ≤ 1 := (div_le_one hDelta_pos).2 hvD
    have hwD' : w / (Delta : ℝ) ≤ 1 := (div_le_one hDelta_pos).2 hwD
    have hwu_nonneg : 0 ≤ 1 - w / (Delta : ℝ) := sub_nonneg.2 hwD'
    have hvu_nonneg : 0 ≤ 1 - v / (Delta : ℝ) := sub_nonneg.2 hvD'
    have huu_nonneg : 0 ≤ 1 - u / (Delta : ℝ) := sub_nonneg.2 huD'
    have hw_bound : (1 - w / (Delta : ℝ)) ^ Delta ≤ Real.exp (-w) := by
      have h := pow_le_pow_left₀ hwu_nonneg
        (Real.one_sub_le_exp_neg (w / (Delta : ℝ))) Delta
      refine h.trans_eq ?_
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hDelta_pos.ne']
    have hv_bound : (1 - v / (Delta : ℝ)) ^ N ≤ Real.exp (-(a * v)) := by
      have h := pow_le_pow_left₀ hvu_nonneg
        (Real.one_sub_le_exp_neg (v / (Delta : ℝ))) N
      refine h.trans_eq ?_
      rw [← Real.exp_nat_mul]
      congr 1
      rw [← hN]
      field_simp [hDelta_pos.ne']
    have hu_bound : (1 - u / (Delta : ℝ)) ^ L ≤ Real.exp (-(rho * u)) := by
      have h := pow_le_pow_left₀ huu_nonneg
        (Real.one_sub_le_exp_neg (u / (Delta : ℝ))) L
      refine h.trans_eq ?_
      rw [← Real.exp_nat_mul]
      congr 1
      rw [← hL]
      field_simp [hDelta_pos.ne']
    have hv_nonneg : 0 ≤ (1 - v / (Delta : ℝ)) ^ N := pow_nonneg hvu_nonneg N
    have hu_nonneg_pow : 0 ≤ (1 - u / (Delta : ℝ)) ^ L := pow_nonneg huu_nonneg L
    have hexpv_nonneg : 0 ≤ Real.exp (-(a * v)) := (Real.exp_pos _).le
    calc
      (1 - w / (Delta : ℝ)) ^ Delta *
              (1 - v / (Delta : ℝ)) ^ N *
                (1 - u / (Delta : ℝ)) ^ L
        ≤ Real.exp (-w) * (1 - v / (Delta : ℝ)) ^ N *
                (1 - u / (Delta : ℝ)) ^ L := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hw_bound hv_nonneg) hu_nonneg_pow
      _ ≤ Real.exp (-w) * Real.exp (-(a * v)) *
                (1 - u / (Delta : ℝ)) ^ L := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hv_bound (Real.exp_pos _).le) hu_nonneg_pow
      _ ≤ Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)) := by
          exact mul_le_mul_of_nonneg_left hu_bound
            (mul_nonneg (Real.exp_pos _).le hexpv_nonneg)
  have hfinite_le_exp :
      (∫ u in (0 : ℝ)..gamma,
        ∫ v in u..gamma,
          ∫ w in v..gamma,
            (1 - w / (Delta : ℝ)) ^ Delta *
              (1 - v / (Delta : ℝ)) ^ N *
                (1 - u / (Delta : ℝ)) ^ L) ≤
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u))) := by
    refine intervalIntegral.integral_mono_on hgamma_nonneg hfinite_outer_int hexp_outer_int ?_
    intro u hu
    refine intervalIntegral.integral_mono_on hu.2 (hfinite_v_int u) (hexp_v_int u) ?_
    intro v hv
    refine intervalIntegral.integral_mono_on hv.2 ?_ ?_ ?_
    · exact ((by fun_prop : Continuous fun w : ℝ =>
        (1 - w / (Delta : ℝ)) ^ Delta *
          (1 - v / (Delta : ℝ)) ^ N *
            (1 - u / (Delta : ℝ)) ^ L).intervalIntegrable v gamma)
    · exact ((by fun_prop : Continuous fun w : ℝ =>
        Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u))).intervalIntegrable v gamma)
    · intro w hw
      exact hpointwise u hu v hv w hw
  have htail_one : ∀ s g C : ℝ,
      (∫ x in s..g, Real.exp (-x) * C) = (Real.exp (-s) - Real.exp (-g)) * C := by
    intro s g C
    rw [intervalIntegral.integral_mul_const]
    have hderiv : ∀ x ∈ Set.uIcc s g,
        HasDerivAt (fun y : ℝ => -Real.exp (-y)) (Real.exp (-x)) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        simpa using ((hasDerivAt_id x).const_mul (-1 : ℝ))
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y))
          (Real.exp (-x) * (-1 : ℝ)) x := by
        simpa using h1.exp
      simpa using h2.neg
    have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-x)) MeasureTheory.volume s g := by
      exact (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => -x)).intervalIntegrable s g
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    ring
  have htail_c : ∀ c s g : ℝ, 0 < c →
      (∫ x in s..g, Real.exp (-(c * x))) =
        (Real.exp (-(c * s)) - Real.exp (-(c * g))) / c := by
    intro c s g hc
    have hderiv : ∀ x ∈ Set.uIcc s g,
        HasDerivAt (fun y : ℝ => -(1 / c) * Real.exp (-(c * y)))
          (Real.exp (-(c * x))) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
        simpa [neg_mul] using ((hasDerivAt_id x).const_mul (-c))
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(c * y)))
          (Real.exp (-(c * x)) * (-c)) x := by
        simpa using h1.exp
      have h3 := h2.const_mul (-(1 / c))
      convert h3 using 1
      field_simp [hc.ne']
    have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-(c * x)))
        MeasureTheory.volume s g := by
      exact (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => -(c * x))).intervalIntegrable s g
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    field_simp [hc.ne']
    ring
  have hexp_bound :
      (∫ u in (0 : ℝ)..gamma,
        ∫ v in u..gamma,
          ∫ w in v..gamma,
            Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)))
        ≤ 1 / ((1 + a) * (1 + a + rho)) := by
    have hinner_rewrite :
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u)))
          =
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            (Real.exp (-v) - Real.exp (-gamma)) *
              (Real.exp (-(a * v)) * Real.exp (-(rho * u)))) := by
      simp_rw [mul_assoc]
      simp_rw [htail_one]
    rw [hinner_rewrite]
    have hv_closed : ∀ u ∈ Set.Icc (0 : ℝ) gamma,
        (∫ v in u..gamma,
            (Real.exp (-v) - Real.exp (-gamma)) *
              (Real.exp (-(a * v)) * Real.exp (-(rho * u))))
          =
        (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
          - Real.exp (-gamma) *
            ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)) *
          Real.exp (-(rho * u)) := by
      intro u hu
      have hcont1 : IntervalIntegrable (fun v : ℝ => Real.exp (-((1 + a) * v)))
          MeasureTheory.volume u gamma := by
        exact (Real.continuous_exp.comp
          (by fun_prop : Continuous fun v : ℝ => -((1 + a) * v))).intervalIntegrable u gamma
      have hcont2 : IntervalIntegrable (fun v : ℝ => Real.exp (-gamma) * Real.exp (-(a * v)))
          MeasureTheory.volume u gamma := by
        exact ((continuous_const.mul (Real.continuous_exp.comp
          (by fun_prop : Continuous fun v : ℝ => -(a * v)))).intervalIntegrable u gamma)
      calc
        (∫ v in u..gamma,
            (Real.exp (-v) - Real.exp (-gamma)) *
              (Real.exp (-(a * v)) * Real.exp (-(rho * u))))
            =
          (∫ v in u..gamma,
            (Real.exp (-((1 + a) * v)) - Real.exp (-gamma) * Real.exp (-(a * v))) *
              Real.exp (-(rho * u))) := by
            apply intervalIntegral.integral_congr
            intro v hv
            have hpair : Real.exp (-v) * Real.exp (-(a * v)) =
                Real.exp (-((1 + a) * v)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            calc
              (Real.exp (-v) - Real.exp (-gamma)) *
                  (Real.exp (-(a * v)) * Real.exp (-(rho * u)))
                  = (Real.exp (-v) * Real.exp (-(a * v)) -
                      Real.exp (-gamma) * Real.exp (-(a * v))) *
                      Real.exp (-(rho * u)) := by ring
              _ = (Real.exp (-((1 + a) * v)) -
                      Real.exp (-gamma) * Real.exp (-(a * v))) *
                    Real.exp (-(rho * u)) := by rw [hpair]
        _ =
          (∫ v in u..gamma,
            Real.exp (-((1 + a) * v)) - Real.exp (-gamma) * Real.exp (-(a * v))) *
              Real.exp (-(rho * u)) := by
            rw [intervalIntegral.integral_mul_const]
        _ =
          (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
            - Real.exp (-gamma) *
              ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)) *
            Real.exp (-(rho * u)) := by
            rw [intervalIntegral.integral_sub hcont1 hcont2]
            rw [intervalIntegral.integral_const_mul]
            rw [htail_c (1 + a) u gamma (by linarith)]
            rw [htail_c a u gamma ha]
    have hafter_v :
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            (Real.exp (-v) - Real.exp (-gamma)) *
              (Real.exp (-(a * v)) * Real.exp (-(rho * u))))
        =
        (∫ u in (0 : ℝ)..gamma,
          (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
            - Real.exp (-gamma) *
              ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)) *
            Real.exp (-(rho * u))) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hv_closed u (by simpa [Set.uIcc_of_le hgamma_nonneg] using hu)
    rw [hafter_v]
    have hc1 : 0 < 1 + a := by linarith
    have hc2 : 0 < 1 + a + rho := by linarith
    have houter_mono :
        (∫ u in (0 : ℝ)..gamma,
          (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
            - Real.exp (-gamma) *
              ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)) *
            Real.exp (-(rho * u)))
        ≤
        (∫ u in (0 : ℝ)..gamma,
          Real.exp (-((1 + a + rho) * u)) / (1 + a)) := by
      refine intervalIntegral.integral_mono_on hgamma_nonneg ?_ ?_ ?_
      · exact ((by fun_prop : Continuous fun u : ℝ =>
          (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
            - Real.exp (-gamma) *
              ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)) *
            Real.exp (-(rho * u))).intervalIntegrable 0 gamma)
      · exact ((by fun_prop : Continuous fun u : ℝ =>
          Real.exp (-((1 + a + rho) * u)) / (1 + a)).intervalIntegrable 0 gamma)
      · intro u hu
        have hug : u ≤ gamma := hu.2
        have hsub_nonneg : 0 ≤ (Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a := by
          have hle_exp : Real.exp (-(a * gamma)) ≤ Real.exp (-(a * u)) := by
            rw [Real.exp_le_exp]
            nlinarith [mul_le_mul_of_nonneg_left hug ha.le]
          exact div_nonneg (sub_nonneg.mpr hle_exp) ha.le
        let A : ℝ :=
          ((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
            - Real.exp (-gamma) *
              ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a)
        have hfirst : A ≤ Real.exp (-((1 + a) * u)) / (1 + a) := by
          have hdrop :
              (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
                - Real.exp (-gamma) *
                  ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a))
              ≤ ((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a)) := by
            nlinarith [mul_nonneg (Real.exp_pos (-gamma)).le hsub_nonneg]
          have hend :
              ((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
              ≤ Real.exp (-((1 + a) * u)) / (1 + a) := by
            gcongr
            linarith [(Real.exp_pos (-((1 + a) * gamma))).le]
          exact (show
              (((Real.exp (-((1 + a) * u)) - Real.exp (-((1 + a) * gamma))) / (1 + a))
                - Real.exp (-gamma) *
                  ((Real.exp (-(a * u)) - Real.exp (-(a * gamma))) / a))
              ≤ Real.exp (-((1 + a) * u)) / (1 + a) from hdrop.trans hend)
        have hmul : A * Real.exp (-(rho * u))
            ≤ (Real.exp (-((1 + a) * u)) / (1 + a)) * Real.exp (-(rho * u)) := by
          exact mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
        have heq :
            (Real.exp (-((1 + a) * u)) / (1 + a)) * Real.exp (-(rho * u))
              = Real.exp (-((1 + a + rho) * u)) / (1 + a) := by
          rw [div_mul_eq_mul_div]
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
        change A * Real.exp (-(rho * u)) ≤ Real.exp (-((1 + a + rho) * u)) / (1 + a)
        exact hmul.trans_eq heq
    refine houter_mono.trans ?_
    calc
      (∫ u in (0 : ℝ)..gamma, Real.exp (-((1 + a + rho) * u)) / (1 + a))
          = (1 / (1 + a)) *
              (∫ u in (0 : ℝ)..gamma, Real.exp (-((1 + a + rho) * u))) := by
            have hcongr :
                (∫ u in (0 : ℝ)..gamma, Real.exp (-((1 + a + rho) * u)) / (1 + a))
                  =
                (∫ u in (0 : ℝ)..gamma, (1 / (1 + a)) *
                  Real.exp (-((1 + a + rho) * u))) := by
              apply intervalIntegral.integral_congr
              intro u hu
              field_simp [hc1.ne']
            rw [hcongr, intervalIntegral.integral_const_mul]
      _ = (1 / (1 + a)) *
          ((Real.exp (-((1 + a + rho) * 0)) - Real.exp (-((1 + a + rho) * gamma))) /
            (1 + a + rho)) := by
            rw [htail_c (1 + a + rho) 0 gamma hc2]
      _ ≤ 1 / ((1 + a) * (1 + a + rho)) := by
        have hleftpos : 0 ≤ 1 / (1 + a) := by positivity
        have hfrac :
            (Real.exp (-((1 + a + rho) * 0)) - Real.exp (-((1 + a + rho) * gamma))) /
              (1 + a + rho) ≤ 1 / (1 + a + rho) := by
          rw [mul_zero, neg_zero, Real.exp_zero]
          gcongr
          linarith [(Real.exp_pos (-((1 + a + rho) * gamma))).le]
        calc
          (1 / (1 + a)) *
            ((Real.exp (-((1 + a + rho) * 0)) - Real.exp (-((1 + a + rho) * gamma))) /
              (1 + a + rho))
              ≤ (1 / (1 + a)) * (1 / (1 + a + rho)) :=
            mul_le_mul_of_nonneg_left hfrac hleftpos
          _ = 1 / ((1 + a) * (1 + a + rho)) := by
            field_simp [hc1.ne', hc2.ne']
  calc
    2 *
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N *
                  (1 - u / (Delta : ℝ)) ^ L)
        ≤ 2 *
          (∫ u in (0 : ℝ)..gamma,
            ∫ v in u..gamma,
              ∫ w in v..gamma,
                Real.exp (-w) * Real.exp (-(a * v)) * Real.exp (-(rho * u))) := by
          exact mul_le_mul_of_nonneg_left hfinite_le_exp (by norm_num)
    _ ≤ 2 * (1 / ((1 + a) * (1 + a + rho))) := by
          exact mul_le_mul_of_nonneg_left hexp_bound (by norm_num)
    _ = 2 / ((1 + a) * (1 + a + rho)) := by
          ring
