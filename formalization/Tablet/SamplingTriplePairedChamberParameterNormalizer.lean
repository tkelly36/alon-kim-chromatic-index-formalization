import Tablet.SamplingTriplePatternCountingBridge

open BigOperators

-- [TABLET NODE: SamplingTriplePairedChamberParameterNormalizer]
theorem SamplingTriplePairedChamberParameterNormalizer
    (Delta : ℕ) (ell_ab ell_ac ell_bc : ℝ)
    (C_ab C_ac C_bc n_abc : ℕ)
    (N_ab_mid N_ab_low N_ac_mid N_ac_low N_bc_mid N_bc_low : ℕ)
    (hDelta_pos : 0 < (Delta : ℝ))
    (hab_pos : 0 < 1 - ell_ab) (hac_pos : 0 < 1 - ell_ac)
    (hbc_pos : 0 < 1 - ell_bc)
    (hell_ab : ell_ab = ((C_ab : ℕ) : ℝ) / (Delta : ℝ))
    (hell_ac : ell_ac = ((C_ac : ℕ) : ℝ) / (Delta : ℝ))
    (hell_bc : ell_bc = ((C_bc : ℕ) : ℝ) / (Delta : ℝ))
    (hmid_ab : N_ab_mid + C_ab = Delta)
    (hmid_ac : N_ac_mid + C_ac = Delta)
    (hmid_bc : N_bc_mid + C_bc = Delta)
    (hlow_ab : N_ab_low + C_ac + C_bc = Delta + n_abc)
    (hlow_ac : N_ac_low + C_ab + C_bc = Delta + n_abc)
    (hlow_bc : N_bc_low + C_ab + C_ac = Delta + n_abc) :
    let x : ℝ := 1 - ell_ab
    let y : ℝ := 1 - ell_ac
    let z : ℝ := 1 - ell_bc
    let tau : ℝ := (n_abc : ℝ) / (Delta : ℝ)
    let rho_x : ℝ := (N_ab_low : ℝ) / (Delta : ℝ)
    let rho_y : ℝ := (N_ac_low : ℝ) / (Delta : ℝ)
    let rho_z : ℝ := (N_bc_low : ℝ) / (Delta : ℝ)
    0 < x ∧ 0 < y ∧ 0 < z ∧
      0 ≤ rho_x ∧ 0 ≤ rho_y ∧ 0 ≤ rho_z ∧ 0 ≤ tau ∧
      ((N_ab_mid : ℝ) / (Delta : ℝ)) = x ∧
      ((N_ab_low : ℝ) / (Delta : ℝ)) = rho_x ∧
      ((N_ac_mid : ℝ) / (Delta : ℝ)) = y ∧
      ((N_ac_low : ℝ) / (Delta : ℝ)) = rho_y ∧
      ((N_bc_mid : ℝ) / (Delta : ℝ)) = z ∧
      ((N_bc_low : ℝ) / (Delta : ℝ)) = rho_z ∧
      1 + x + rho_x = x + y + z + tau ∧
      1 + y + rho_y = x + y + z + tau ∧
      1 + z + rho_z = x + y + z + tau := by
-- BODY
  dsimp only
  have hDne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_pos
  have hmid_ab_real : (N_ab_mid : ℝ) + (C_ab : ℝ) = (Delta : ℝ) := by
    exact_mod_cast hmid_ab
  have hmid_ac_real : (N_ac_mid : ℝ) + (C_ac : ℝ) = (Delta : ℝ) := by
    exact_mod_cast hmid_ac
  have hmid_bc_real : (N_bc_mid : ℝ) + (C_bc : ℝ) = (Delta : ℝ) := by
    exact_mod_cast hmid_bc
  have hlow_ab_real :
      (N_ab_low : ℝ) + (C_ac : ℝ) + (C_bc : ℝ) =
        (Delta : ℝ) + (n_abc : ℝ) := by
    exact_mod_cast hlow_ab
  have hlow_ac_real :
      (N_ac_low : ℝ) + (C_ab : ℝ) + (C_bc : ℝ) =
        (Delta : ℝ) + (n_abc : ℝ) := by
    exact_mod_cast hlow_ac
  have hlow_bc_real :
      (N_bc_low : ℝ) + (C_ab : ℝ) + (C_ac : ℝ) =
        (Delta : ℝ) + (n_abc : ℝ) := by
    exact_mod_cast hlow_bc
  have hN_ab_mid : (N_ab_mid : ℝ) / (Delta : ℝ) = 1 - ell_ab := by
    rw [hell_ab]
    field_simp [hDne]
    linarith
  have hN_ac_mid : (N_ac_mid : ℝ) / (Delta : ℝ) = 1 - ell_ac := by
    rw [hell_ac]
    field_simp [hDne]
    linarith
  have hN_bc_mid : (N_bc_mid : ℝ) / (Delta : ℝ) = 1 - ell_bc := by
    rw [hell_bc]
    field_simp [hDne]
    linarith
  have hMx :
      1 + (1 - ell_ab) + (N_ab_low : ℝ) / (Delta : ℝ) =
        (1 - ell_ab) + (1 - ell_ac) + (1 - ell_bc) +
          (n_abc : ℝ) / (Delta : ℝ) := by
    rw [hell_ab, hell_ac, hell_bc]
    field_simp [hDne]
    linarith
  have hMy :
      1 + (1 - ell_ac) + (N_ac_low : ℝ) / (Delta : ℝ) =
        (1 - ell_ab) + (1 - ell_ac) + (1 - ell_bc) +
          (n_abc : ℝ) / (Delta : ℝ) := by
    rw [hell_ab, hell_ac, hell_bc]
    field_simp [hDne]
    linarith
  have hMz :
      1 + (1 - ell_bc) + (N_bc_low : ℝ) / (Delta : ℝ) =
        (1 - ell_ab) + (1 - ell_ac) + (1 - ell_bc) +
          (n_abc : ℝ) / (Delta : ℝ) := by
    rw [hell_ab, hell_ac, hell_bc]
    field_simp [hDne]
    linarith
  refine
    ⟨hab_pos, hac_pos, hbc_pos, ?_, ?_, ?_, ?_, hN_ab_mid, rfl,
      hN_ac_mid, rfl, hN_bc_mid, rfl, hMx, hMy, hMz⟩
  all_goals positivity
