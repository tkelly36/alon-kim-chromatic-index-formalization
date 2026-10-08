import Tablet.KPartiteTriangleCoefficientIdentity
import Tablet.Preamble

set_option maxHeartbeats 800000

-- [TABLET NODE: KUniformKSimpleBParameterRealEstimate]
theorem KUniformKSimpleBParameterRealEstimate :
    ∀ {k D : ℕ} {y : ℝ}, 2 ≤ k → 0 < D →
      (k : ℝ) ^ 2 / (D : ℝ) ≤ ((k : ℝ) - 1) / 2 →
      0 ≤ y →
      ((k : ℝ) - 1) / 2 - (k : ℝ) ^ 2 / (D : ℝ) ≤ y →
      y ≤ (k : ℝ) ^ 2 / 2 →
      1 - (1 : ℝ) / (D : ℝ) - y / (k : ℝ) ^ 2 +
          ((Nat.choose k 3 : ℝ) /
              ((k : ℝ) ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))) *
            y ^ ((3 : ℝ) / 2)
        ≤ 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
-- BODY
  intro k D y hk hD hthreshold hy_nonneg hy_lower hy_upper
  let kr : ℝ := k
  let a : ℝ := (kr - 1) / 2
  let M : ℝ := kr ^ 2 / 2
  let c : ℝ :=
    (Nat.choose k 3 : ℝ) /
      (kr ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2))
  have hk_pos_nat : 0 < k := by omega
  have hk_real_pos : 0 < kr := by
    dsimp [kr]
    exact_mod_cast hk_pos_nat
  have hk_real_two : (2 : ℝ) ≤ kr := by
    dsimp [kr]
    exact_mod_cast hk
  have hD_real_pos : (0 : ℝ) < D := by exact_mod_cast hD
  have hkr_ne : kr ≠ 0 := ne_of_gt hk_real_pos
  have hkr_sq_pos : 0 < kr ^ 2 := sq_pos_of_pos hk_real_pos
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, kr] at *
    linarith
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have ha_le_M : a ≤ M := by
    dsimp [a, M]
    nlinarith [sq_nonneg (kr - 1)]
  have hchoose_two_pos : (0 : ℝ) < (Nat.choose k 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hrpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
      x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
    by_cases hx0 : x = 0
    · subst x
      norm_num
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      calc
        x ^ ((3 : ℝ) / 2)
            = x ^ (1 + (1 / 2 : ℝ)) := by norm_num
        _ = x * x ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_add hxpos]
              simp
        _ = x * Real.sqrt x := by
              rw [Real.sqrt_eq_rpow]
  have hslope_bound :
      ∀ {x : ℝ}, a ≤ x → x ≤ M →
        x ^ ((3 : ℝ) / 2) - a ^ ((3 : ℝ) / 2) ≤
          (x - a) * ((3 : ℝ) / 2 * Real.sqrt M) := by
    intro x hax hxM
    have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hax
    have hsqrt_a_le_x : Real.sqrt a ≤ Real.sqrt x := Real.sqrt_le_sqrt hax
    have hsqrt_x_le_M : Real.sqrt x ≤ Real.sqrt M := Real.sqrt_le_sqrt hxM
    have hx_sqrt : x = Real.sqrt x ^ 2 := by
      rw [Real.sq_sqrt hx_nonneg]
    have ha_sqrt : a = Real.sqrt a ^ 2 := by
      rw [Real.sq_sqrt ha_nonneg]
    have hsqa_nonneg : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have hsqx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    rw [hrpow_three_halves x hx_nonneg, hrpow_three_halves a ha_nonneg]
    rw [hx_sqrt, ha_sqrt]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsqx_nonneg]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsqa_nonneg]
    ring_nf
    have hdiff_nonneg : 0 ≤ Real.sqrt x - Real.sqrt a := sub_nonneg.mpr hsqrt_a_le_x
    have hmain :
        2 * (Real.sqrt x ^ 2 + Real.sqrt x * Real.sqrt a + Real.sqrt a ^ 2)
          ≤ 3 * Real.sqrt M * (Real.sqrt x + Real.sqrt a) := by
      have h1 : Real.sqrt x ^ 2 ≤ Real.sqrt M * Real.sqrt x := by
        nlinarith [hsqx_nonneg, hsqrt_x_le_M]
      have h2 : Real.sqrt a ^ 2 ≤ Real.sqrt M * Real.sqrt a := by
        nlinarith [hsqa_nonneg, le_trans hsqrt_a_le_x hsqrt_x_le_M]
      have h3 :
          2 * (Real.sqrt x * Real.sqrt a)
            ≤ Real.sqrt M * (Real.sqrt x + Real.sqrt a) := by
        nlinarith [hsqa_nonneg, hsqx_nonneg, hsqrt_x_le_M,
          le_trans hsqrt_a_le_x hsqrt_x_le_M]
      nlinarith
    nlinarith [hdiff_nonneg, hmain]
  have hc_slope :
      c * ((3 : ℝ) / 2 * Real.sqrt M) ≤ 1 / kr ^ 2 := by
    by_cases hk_three : 3 ≤ k
    · have hcoeff :
          (Nat.choose k 3 : ℝ) /
              (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2) =
            ((2 : ℝ) / 3) *
              Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) := by
          dsimp [kr]
          rw [← KPartiteTriangleCoefficientIdentity k hk_three]
      have hM_sqrt :
          Real.sqrt M = kr / Real.sqrt 2 := by
        have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
        have hkr_nonneg : 0 ≤ kr := le_of_lt hk_real_pos
        calc
          Real.sqrt M
              = Real.sqrt (kr ^ 2 / 2) := rfl
          _ = Real.sqrt (kr ^ 2) / Real.sqrt 2 := by
                rw [Real.sqrt_div (sq_nonneg kr)]
          _ = kr / Real.sqrt 2 := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hkr_nonneg]
      have hfrac1_nonneg : 0 ≤ (kr - 2) / (2 * (kr - 1)) := by
        exact div_nonneg (by linarith) (mul_nonneg (by norm_num) (by linarith))
      have hfrac2_nonneg : 0 ≤ (kr - 2) / kr := by
        exact div_nonneg (by linarith) (le_of_lt hk_real_pos)
      have hsqrt_prod_le_two :
          Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) ≤ Real.sqrt 2 := by
        have hfrac1_le_one : (kr - 2) / (2 * (kr - 1)) ≤ 1 := by
          have hden_pos : 0 < 2 * (kr - 1) := by nlinarith
          rw [div_le_iff₀ hden_pos]
          nlinarith
        have hfrac2_le_one : (kr - 2) / kr ≤ 1 := by
          rw [div_le_iff₀ hk_real_pos]
          linarith
        have hs1 : Real.sqrt ((kr - 2) / (2 * (kr - 1))) ≤ 1 := by
          simpa using Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1) |>.2 hfrac1_le_one
        have hs2 : Real.sqrt ((kr - 2) / kr) ≤ 1 := by
          simpa using Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1) |>.2 hfrac2_le_one
        have hprod_le_one :
            Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
                Real.sqrt ((kr - 2) / kr) ≤ 1 := by
          nlinarith [Real.sqrt_nonneg ((kr - 2) / (2 * (kr - 1))),
            Real.sqrt_nonneg ((kr - 2) / kr), hs1, hs2]
        have hone_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
          have hsq : (1 : ℝ) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          nlinarith [Real.sqrt_nonneg (2 : ℝ)]
        exact le_trans hprod_le_one hone_le_sqrt_two
      have hsqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hc_rewrite :
          c * ((3 : ℝ) / 2 * Real.sqrt M) =
            (Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
                Real.sqrt ((kr - 2) / kr)) /
              (Real.sqrt 2 * kr ^ 2) := by
        dsimp [c]
        rw [show (Nat.choose k 3 : ℝ) /
              (kr ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2)) =
            ((Nat.choose k 3 : ℝ) /
              (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2)) / kr ^ 3 by
              field_simp [ne_of_gt hk_real_pos, ne_of_gt hchoose_two_pos,
                ne_of_gt (Real.rpow_pos_of_pos hchoose_two_pos _)]]
        rw [hcoeff, hM_sqrt]
        field_simp [ne_of_gt hk_real_pos, ne_of_gt hsqrt_two_pos]
      rw [hc_rewrite]
      have hden_pos : 0 < Real.sqrt 2 * kr ^ 2 := by positivity
      rw [div_le_iff₀ hden_pos]
      field_simp [ne_of_gt hk_real_pos]
      nlinarith [hsqrt_prod_le_two, hsqrt_two_pos]
    · have hk_eq_two : k = 2 := by omega
      subst k
      norm_num [c, kr]
  have hendpoint :
      c * a ^ ((3 : ℝ) / 2) =
        (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
          (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
    by_cases hk_three : 3 ≤ k
    · have hcoeff :
          (Nat.choose k 3 : ℝ) /
              (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2) =
            ((2 : ℝ) / 3) *
              Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) := by
          dsimp [kr]
          rw [← KPartiteTriangleCoefficientIdentity k hk_three]
      have hkm1_pos : 0 < kr - 1 := by nlinarith
      have hpowA : a ^ ((3 : ℝ) / 2) = a * Real.sqrt a :=
        hrpow_three_halves a ha_nonneg
      have hfrac1_nonneg : 0 ≤ (kr - 2) / (2 * (kr - 1)) := by
        exact div_nonneg (by nlinarith) (le_of_lt (by nlinarith))
      have hfrac2_nonneg : 0 ≤ (kr - 2) / kr := by
        exact div_nonneg (by nlinarith) (le_of_lt hk_real_pos)
      have hsqrts :
          Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) * Real.sqrt a =
            (kr - 2) / (2 * Real.sqrt kr) := by
        have hinside :
            (kr - 2) / (2 * (kr - 1)) * ((kr - 2) / kr) * a =
              (kr - 2) ^ 2 / (4 * kr) := by
          dsimp [a]
          field_simp [ne_of_gt hk_real_pos, ne_of_gt hkm1_pos]
          ring
        have hsqrt_inside :
            Real.sqrt ((kr - 2) ^ 2 / (4 * kr)) =
              (kr - 2) / (2 * Real.sqrt kr) := by
          have hnonneg : 0 ≤ (kr - 2) / (2 * Real.sqrt kr) := by
            exact div_nonneg (by nlinarith) (mul_nonneg (by norm_num)
              (Real.sqrt_nonneg kr))
          calc
            Real.sqrt ((kr - 2) ^ 2 / (4 * kr))
                = Real.sqrt (((kr - 2) / (2 * Real.sqrt kr)) ^ 2) := by
                    congr 1
                    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hk_real_pos)]
                    ring
            _ = |(kr - 2) / (2 * Real.sqrt kr)| := by
                    rw [Real.sqrt_sq_eq_abs]
            _ = (kr - 2) / (2 * Real.sqrt kr) := abs_of_nonneg hnonneg
        calc
          Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) * Real.sqrt a
              = Real.sqrt (((kr - 2) / (2 * (kr - 1))) *
                  ((kr - 2) / kr)) * Real.sqrt a := by
                  rw [Real.sqrt_mul hfrac1_nonneg ((kr - 2) / kr)]
          _ = Real.sqrt (((kr - 2) / (2 * (kr - 1))) *
                  ((kr - 2) / kr) * a) := by
                  rw [← Real.sqrt_mul (mul_nonneg hfrac1_nonneg hfrac2_nonneg) a]
          _ = (kr - 2) / (2 * Real.sqrt kr) := by
                  rw [hinside, hsqrt_inside]
      dsimp [c]
      rw [show (Nat.choose k 3 : ℝ) /
            (kr ^ 3 * (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2)) =
          ((Nat.choose k 3 : ℝ) /
            (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2)) / kr ^ 3 by
            field_simp [ne_of_gt hk_real_pos, ne_of_gt hchoose_two_pos,
              ne_of_gt (Real.rpow_pos_of_pos hchoose_two_pos _)]]
      rw [hcoeff, hpowA]
      calc
        (2 / 3 * Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
              Real.sqrt ((kr - 2) / kr) / kr ^ 3) *
            (a * Real.sqrt a)
            = ((kr - 1) / (3 * kr ^ 3)) *
                (Real.sqrt ((kr - 2) / (2 * (kr - 1))) *
                  Real.sqrt ((kr - 2) / kr) * Real.sqrt a) := by
                dsimp [a]
                ring
        _ = ((kr - 1) / (3 * kr ^ 3)) *
              ((kr - 2) / (2 * Real.sqrt kr)) := by
                rw [hsqrts]
        _ = (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
              (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
                dsimp [kr]
                field_simp [ne_of_gt hk_real_pos, ne_of_gt (Real.sqrt_pos.mpr hk_real_pos)]
                ring
    · have hk_eq_two : k = 2 := by omega
      subst k
      norm_num [c, a, kr]
  by_cases hy_le_a : y ≤ a
  · have hy_rpow_le_a : y ^ ((3 : ℝ) / 2) ≤ a ^ ((3 : ℝ) / 2) := by
      exact Real.rpow_le_rpow hy_nonneg hy_le_a (by norm_num)
    have hcy_le_ca : c * y ^ ((3 : ℝ) / 2) ≤ c * a ^ ((3 : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left hy_rpow_le_a hc_nonneg
    have hbase :
        - (1 : ℝ) / (D : ℝ) - y / kr ^ 2 ≤ -a / kr ^ 2 := by
      have htmp : a - kr ^ 2 / (D : ℝ) ≤ y := by simpa [a, kr] using hy_lower
      have htmp_div : (a - kr ^ 2 / (D : ℝ)) / kr ^ 2 ≤ y / kr ^ 2 := by
        exact div_le_div_of_nonneg_right htmp (le_of_lt hkr_sq_pos)
      have hrewrite : (a - kr ^ 2 / (D : ℝ)) / kr ^ 2 =
          a / kr ^ 2 - 1 / (D : ℝ) := by
        field_simp [ne_of_gt hD_real_pos, ne_of_gt hkr_sq_pos]
      have htmp_div' : a / kr ^ 2 - 1 / (D : ℝ) ≤ y / kr ^ 2 := by
        simpa [hrewrite] using htmp_div
      calc
        - (1 : ℝ) / (D : ℝ) - y / kr ^ 2
            ≤ - (1 : ℝ) / (D : ℝ) - (a / kr ^ 2 - 1 / (D : ℝ)) := by
                linarith
        _ = -a / kr ^ 2 := by ring
    have hca :
        c * a ^ ((3 : ℝ) / 2) =
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
      exact hendpoint
    calc
      1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2 + c * y ^ ((3 : ℝ) / 2)
          ≤ 1 - a / kr ^ 2 + c * a ^ ((3 : ℝ) / 2) := by
            have hbase' : 1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2
                ≤ 1 - a / kr ^ 2 := by
              calc
                1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2
                    = 1 + (-(1 : ℝ) / (D : ℝ) - y / kr ^ 2) := by ring
                _ ≤ 1 + (-a / kr ^ 2) := by
                    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hbase 1
                _ = 1 - a / kr ^ 2 := by ring
            exact add_le_add hbase' hcy_le_ca
      _ = 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
            rw [hca]
            dsimp [a, kr]
            field_simp [ne_of_gt hk_real_pos]
  · have hay : a ≤ y := le_of_not_ge hy_le_a
    have hsec := hslope_bound hay hy_upper
    have hcy_diff :
        c * (y ^ ((3 : ℝ) / 2) - a ^ ((3 : ℝ) / 2)) ≤
          (y - a) / kr ^ 2 := by
      calc
        c * (y ^ ((3 : ℝ) / 2) - a ^ ((3 : ℝ) / 2))
            ≤ c * ((y - a) * ((3 : ℝ) / 2 * Real.sqrt M)) := by
              exact mul_le_mul_of_nonneg_left hsec hc_nonneg
        _ = (y - a) * (c * ((3 : ℝ) / 2 * Real.sqrt M)) := by ring
        _ ≤ (y - a) * (1 / kr ^ 2) := by
              exact mul_le_mul_of_nonneg_left hc_slope (sub_nonneg.mpr hay)
        _ = (y - a) / kr ^ 2 := by ring
    have hca :
        c * a ^ ((3 : ℝ) / 2) =
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
      exact hendpoint
    calc
      1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2 + c * y ^ ((3 : ℝ) / 2)
          = 1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2 +
              c * a ^ ((3 : ℝ) / 2) +
              c * (y ^ ((3 : ℝ) / 2) - a ^ ((3 : ℝ) / 2)) := by
              ring
      _ ≤ 1 - (1 : ℝ) / (D : ℝ) - y / kr ^ 2 +
              c * a ^ ((3 : ℝ) / 2) + (y - a) / kr ^ 2 := by
              linarith
      _ = 1 - (1 : ℝ) / (D : ℝ) - a / kr ^ 2 +
              c * a ^ ((3 : ℝ) / 2) := by ring
      _ ≤ 1 - a / kr ^ 2 + c * a ^ ((3 : ℝ) / 2) := by
              have hinv_pos : 0 < (1 : ℝ) / (D : ℝ) := by positivity
              linarith
      _ = 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
          (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
            (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) := by
            rw [hca]
            dsimp [a, kr]
            field_simp [ne_of_gt hk_real_pos]
