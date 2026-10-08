import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Tablet.SamplingTripleActivationChamberSum
import Tablet.SamplingTripleRealChamberEstimate
import Tablet.SamplingTripleSingleChamberIntegralEstimate

open BigOperators

-- [TABLET NODE: SamplingTripleFullChamberIntegralEstimate]
theorem SamplingTripleFullChamberIntegralEstimate
    (Delta : ℕ) (gamma : ℝ)
    (x y z tau rho_x rho_y rho_z : ℝ)
    (N_x_mid N_x_low N_y_mid N_y_low N_z_mid N_z_low : ℕ)
    (hDelta_pos : 0 < (Delta : ℝ))
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ (Delta : ℝ))
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hrho_x : 0 ≤ rho_x) (hrho_y : 0 ≤ rho_y) (hrho_z : 0 ≤ rho_z)
    (htau : 0 ≤ tau)
    (hN_x_mid : ((N_x_mid : ℝ) / (Delta : ℝ)) = x)
    (hN_x_low : ((N_x_low : ℝ) / (Delta : ℝ)) = rho_x)
    (hN_y_mid : ((N_y_mid : ℝ) / (Delta : ℝ)) = y)
    (hN_y_low : ((N_y_low : ℝ) / (Delta : ℝ)) = rho_y)
    (hN_z_mid : ((N_z_mid : ℝ) / (Delta : ℝ)) = z)
    (hN_z_low : ((N_z_low : ℝ) / (Delta : ℝ)) = rho_z)
    (hMx : 1 + x + rho_x = x + y + z + tau)
    (hMy : 1 + y + rho_y = x + y + z + tau)
    (hMz : 1 + z + rho_z = x + y + z + tau) :
    2 *
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N_x_mid *
                  (1 - u / (Delta : ℝ)) ^ N_x_low) +
      2 *
        (∫ u in (0 : ℝ)..gamma,
          ∫ v in u..gamma,
            ∫ w in v..gamma,
              (1 - w / (Delta : ℝ)) ^ Delta *
                (1 - v / (Delta : ℝ)) ^ N_y_mid *
                  (1 - u / (Delta : ℝ)) ^ N_y_low) +
        2 *
          (∫ u in (0 : ℝ)..gamma,
            ∫ v in u..gamma,
              ∫ w in v..gamma,
                (1 - w / (Delta : ℝ)) ^ Delta *
                  (1 - v / (Delta : ℝ)) ^ N_z_mid *
                    (1 - u / (Delta : ℝ)) ^ N_z_low) ≤
      2 / ((1 + x) * (x + y + z + tau)) +
        2 / ((1 + y) * (x + y + z + tau)) +
          2 / ((1 + z) * (x + y + z + tau)) := by
-- BODY
  have hsingle
      (a rho : ℝ) (N L : ℕ)
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
    exact SamplingTripleSingleChamberIntegralEstimate Delta gamma a rho N L
      hDelta_pos hgamma_nonneg hgamma_le ha hrho hN hL
  have hx_bound :
      2 *
          (∫ u in (0 : ℝ)..gamma,
            ∫ v in u..gamma,
              ∫ w in v..gamma,
                (1 - w / (Delta : ℝ)) ^ Delta *
                  (1 - v / (Delta : ℝ)) ^ N_x_mid *
                    (1 - u / (Delta : ℝ)) ^ N_x_low) ≤
        2 / ((1 + x) * (x + y + z + tau)) := by
    have h := hsingle x rho_x N_x_mid N_x_low hx hrho_x hN_x_mid hN_x_low
    rwa [hMx] at h
  have hy_bound :
      2 *
          (∫ u in (0 : ℝ)..gamma,
            ∫ v in u..gamma,
              ∫ w in v..gamma,
                (1 - w / (Delta : ℝ)) ^ Delta *
                  (1 - v / (Delta : ℝ)) ^ N_y_mid *
                    (1 - u / (Delta : ℝ)) ^ N_y_low) ≤
        2 / ((1 + y) * (x + y + z + tau)) := by
    have h := hsingle y rho_y N_y_mid N_y_low hy hrho_y hN_y_mid hN_y_low
    rwa [hMy] at h
  have hz_bound :
      2 *
          (∫ u in (0 : ℝ)..gamma,
            ∫ v in u..gamma,
              ∫ w in v..gamma,
                (1 - w / (Delta : ℝ)) ^ Delta *
                  (1 - v / (Delta : ℝ)) ^ N_z_mid *
                    (1 - u / (Delta : ℝ)) ^ N_z_low) ≤
        2 / ((1 + z) * (x + y + z + tau)) := by
    have h := hsingle z rho_z N_z_mid N_z_low hz hrho_z hN_z_mid hN_z_low
    rwa [hMz] at h
  linarith
