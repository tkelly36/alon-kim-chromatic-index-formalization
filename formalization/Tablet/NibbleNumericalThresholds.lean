import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Tablet.NibbleCeilingPowerEstimate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- [TABLET NODE: NibbleNumericalThresholds]
theorem NibbleNumericalThresholds (A k : ℕ) (hA : 1 ≤ A) (hk : 1 ≤ k)
    (iota : ℝ) (hi : 0 < iota) :
    ∃ gamma0 : ℕ, 1 ≤ gamma0 ∧ ∀ gamma : ℕ, gamma0 ≤ gamma →
      ∃ D0 : ℕ, 1 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
        let ell := Nat.ceil ((k : ℝ) * D / gamma)
        gamma ≤ k * D ∧ 0 < ell ∧
        (1 - (1 - Real.exp (-(gamma : ℝ))) / (k * D : ℕ) +
          2 / ((k * D : ℕ) : ℝ)^2)^ell ≤
            1 - (1 - iota / 2) / gamma ∧
        Real.exp (-(iota^2 / (2 * (gamma : ℝ)^2 * A)) * D) ≤
          Real.exp (-(Real.log D)^2) ∧
        Real.exp (-(iota^2 / (8 + 2 * iota)) * ell) ≤
          Real.exp (-(Real.log D)^2) ∧
        Real.exp 1 * Real.exp (-(Real.log D)^2) *
          ((4 * A * (k + 1) * k^4 * D^6 : ℕ) + 1 : ℝ) ≤ 1 := by
-- BODY
  have hlog : ∀ c : ℝ, 0 < c → ∀ᶠ D : ℕ in Filter.atTop,
      (Real.log D) ^ 2 ≤ c * D := by
    intro c hc
    have h := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 by norm_num)).bound hc
    have h' := (Filter.Tendsto.eventually (tendsto_natCast_atTop_atTop :
      Filter.Tendsto (fun D : ℕ => (D : ℝ)) Filter.atTop Filter.atTop) h)
    filter_upwards [h'] with D hD
    simpa only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (D : ℝ))),
      abs_of_nonneg (show (0 : ℝ) ≤ D from Nat.cast_nonneg D)] using hD
  have hexp : ∀ᶠ gamma : ℕ in Filter.atTop,
      Real.exp (-(gamma : ℝ)) ≤ min (1 / 4) (iota / 8) := by
    have hlim := Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
          Filter.atTop Filter.atTop))
    exact (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < min (1 / 4) (iota / 8)))).mono
      (fun _ h => h.le)
  have hinv : ∀ᶠ gamma : ℕ in Filter.atTop, 1 / (gamma : ℝ) ≤ iota / 4 := by
    have hlim := tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop)
    simpa only [one_div] using
      (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < iota / 4))).mono
        (fun _ h => h.le)
  obtain ⟨gamma0, hgamma0⟩ := Filter.eventually_atTop.1 (hexp.and hinv)
  refine ⟨max 1 gamma0, le_max_left _ _, ?_⟩
  intro gamma hgamma
  have hg : 1 ≤ gamma := (le_max_left _ _).trans hgamma
  have hgR : (1 : ℝ) ≤ gamma := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < gamma := by positivity
  obtain ⟨hge, hgi⟩ := hgamma0 gamma ((le_max_right _ _).trans hgamma)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hA0 : (0 : ℝ) < A := by positivity
  have hk0 : (0 : ℝ) < k := by positivity
  have hc1 : 0 < iota ^ 2 / (2 * (gamma : ℝ) ^ 2 * A) := by positivity
  have hc2 : 0 < (iota ^ 2 / (8 + 2 * iota)) * ((k : ℝ) / gamma) := by positivity
  have hDlarge : ∀ᶠ D : ℕ in Filter.atTop,
      1 ≤ D ∧ gamma ≤ k * D ∧ 4 ≤ ((k * D : ℕ) : ℝ) ∧
        2 / ((k * D : ℕ) : ℝ) ≤ iota / 8 := by
    have hlim : Filter.Tendsto (fun D : ℕ => ((k * D : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      simpa only [Nat.cast_mul] using
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun D : ℕ => (D : ℝ))
          Filter.atTop Filter.atTop).const_mul_atTop hk0
    filter_upwards [Filter.eventually_ge_atTop 1,
      hlim.eventually_ge_atTop (gamma : ℝ), hlim.eventually_ge_atTop 4,
      hlim.eventually_ge_atTop (16 / iota)] with D hD hgd hd4 hdi
    refine ⟨hD, by exact_mod_cast hgd, hd4, ?_⟩
    have hd0 : (0 : ℝ) < (k * D : ℕ) := by linarith
    apply (div_le_iff₀ hd0).2
    have := (div_le_iff₀ hi).1 hdi
    nlinarith
  let C : ℝ := (4 * A * (k + 1) * k ^ 4 : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlocal : ∀ᶠ D : ℕ in Filter.atTop,
      Real.exp 1 * Real.exp (-(Real.log D)^2) * (C * (D : ℝ)^6 + 1) ≤ 1 := by
    have hlim := Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun D : ℕ => (D : ℝ))
        Filter.atTop Filter.atTop)
    filter_upwards [Filter.eventually_ge_atTop 1, hlim.eventually_ge_atTop 7,
      hlim.eventually_ge_atTop (1 + Real.log (C + 1))] with D hD h7 hCbound
    simp only [Function.comp_apply] at h7 hCbound
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hD0 : (0 : ℝ) < D := by linarith
    have hpow : (1 : ℝ) ≤ (D : ℝ)^6 := one_le_pow₀ hD1
    have hpoly : C * (D : ℝ)^6 + 1 ≤ (C + 1) * (D : ℝ)^6 := by nlinarith
    have hexponent : 1 + Real.log (C + 1) + 6 * Real.log D - (Real.log D)^2 ≤ 0 := by
      nlinarith
    calc
      _ ≤ Real.exp 1 * Real.exp (-(Real.log D)^2) * ((C + 1) * (D : ℝ)^6) := by
        gcongr
      _ = Real.exp (1 + Real.log (C + 1) + 6 * Real.log D - (Real.log D)^2) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_add,
          Real.exp_log (by positivity : 0 < C + 1), show (6 : ℝ) = (6 : ℕ) by norm_num,
          Real.exp_nat_mul,
          Real.exp_log hD0, Real.exp_neg]
        ring
      _ ≤ 1 := by simpa using Real.exp_le_exp.mpr hexponent
  obtain ⟨D0, hD0⟩ := Filter.eventually_atTop.1
    (hDlarge.and ((hlog _ hc1).and ((hlog _ hc2).and hlocal)))
  refine ⟨max 1 D0, le_max_left _ _, ?_⟩
  intro D hD
  obtain ⟨⟨hD1, hgd, hd4, hdi⟩, htail1, htail2, hloc⟩ :=
    hD0 D ((le_max_right _ _).trans hD)
  have hDpos : (0 : ℝ) < D := by positivity
  have hell : (k : ℝ) * D / gamma ≤ (Nat.ceil ((k : ℝ) * D / gamma) : ℝ) := Nat.le_ceil _
  refine ⟨hgd, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < (k : ℝ) * D / gamma) hell)
  · simpa only [Nat.cast_mul] using NibbleCeilingPowerEstimate iota gamma (k * D : ℕ)
      hgR hd4 hge hgi hdi
  · exact Real.exp_le_exp.mpr (by nlinarith [htail1])
  · apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hell
      (by positivity : 0 ≤ iota ^ 2 / (8 + 2 * iota))
    have heq : iota ^ 2 / (8 + 2 * iota) * ((k : ℝ) * D / gamma) =
        (iota ^ 2 / (8 + 2 * iota) * ((k : ℝ) / gamma)) * D := by ring
    rw [heq] at hmul
    linarith
  · simpa only [C, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hloc
