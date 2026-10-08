import Tablet.TableColumnPairSquareBound
import Tablet.TableSquareSumFillingBound

set_option linter.unusedVariables false

-- [TABLET NODE: TablePairFillingBound]
theorem TablePairFillingBound :
    ∀ {k n : ℕ} (hk : 2 ≤ k) (C T : ℝ) (q : ℕ) (r : ℝ)
      (A : Fin k → Fin n → ℝ),
      0 < C →
      0 < T →
      q = Nat.floor (T / C) →
      r = T - (q : ℝ) * C →
      (∀ i j, 0 ≤ A i j) →
      (∀ j, (∑ i : Fin k, A i j) ≤ C) →
      (∑ i : Fin k, ∑ j : Fin n, A i j) ≤ T →
      (∑ j : Fin n,
          ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0))
        ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) *
          ((q : ℝ) * C ^ (2 : ℕ) + r ^ (2 : ℕ)) := by
-- BODY
  intro k n hk C T q r A hC hT hq hr hnonneg hcol htot
  let B : Fin n → ℝ := fun j => ∑ i : Fin k, A i j
  let P : Fin n → ℝ := fun j =>
    ∑ i : Fin k, ∑ i' : Fin k, (if i < i' then A i j * A i' j else 0)
  have hkpos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hcoef_nonneg : 0 ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) := by
    have h1k : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hk)
    exact div_nonneg (sub_nonneg.mpr h1k) (mul_nonneg (by norm_num) hkpos.le)
  have hratio_nonneg : 0 ≤ T / C := by positivity
  have hq_le_ratio : (q : ℝ) ≤ T / C := by
    simpa [hq] using (Nat.floor_le hratio_nonneg : ((Nat.floor (T / C) : ℕ) : ℝ) ≤ T / C)
  have hratio_lt_q_add_one : T / C < (q : ℝ) + 1 := by
    simpa [hq] using (Nat.lt_floor_add_one (T / C) :
      T / C < ((Nat.floor (T / C) : ℕ) : ℝ) + 1)
  have hr_nonneg : 0 ≤ r := by
    have hqC_le_T : (q : ℝ) * C ≤ T := by
      rwa [le_div_iff₀ hC] at hq_le_ratio
    nlinarith [hr, hqC_le_T]
  have hr_le_C : r ≤ C := by
    have hT_lt : T < ((q : ℝ) + 1) * C := by
      rwa [div_lt_iff₀ hC] at hratio_lt_q_add_one
    nlinarith [hr, hT_lt]
  have hTsplit : T = (q : ℝ) * C + r := by
    nlinarith [hr]
  have hB_nonneg : ∀ j, 0 ≤ B j := by
    intro j
    dsimp [B]
    exact Finset.sum_nonneg (fun i _ => hnonneg i j)
  have hB_le_C : ∀ j, B j ≤ C := by
    intro j
    dsimp [B]
    exact hcol j
  have hsumB_le : (∑ j : Fin n, B j) ≤ T := by
    dsimp [B]
    rw [Finset.sum_comm]
    exact htot
  have hsq :
      (∑ j : Fin n, (B j) ^ (2 : ℕ)) ≤
        (q : ℝ) * C ^ (2 : ℕ) + r ^ (2 : ℕ) :=
    TableSquareSumFillingBound C T q r B hC hTsplit hr_nonneg hr_le_C
      hB_nonneg hB_le_C hsumB_le
  have hcolpair : ∀ j : Fin n,
      P j ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * (B j) ^ (2 : ℕ) := by
    intro j
    dsimp [P, B]
    exact TableColumnPairSquareBound hk (fun i : Fin k => A i j)
  have hsumP :
      (∑ j : Fin n, P j) ≤
        ∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * (B j) ^ (2 : ℕ) := by
    exact Finset.sum_le_sum (fun j _ => hcolpair j)
  have hmul :
      (∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * (B j) ^ (2 : ℕ))
        ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) *
          ((q : ℝ) * C ^ (2 : ℕ) + r ^ (2 : ℕ)) := by
    calc
      (∑ j : Fin n, (((k : ℝ) - 1) / (2 * (k : ℝ))) * (B j) ^ (2 : ℕ))
          = (((k : ℝ) - 1) / (2 * (k : ℝ))) *
              (∑ j : Fin n, (B j) ^ (2 : ℕ)) := by
            rw [← Finset.mul_sum]
      _ ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) *
              ((q : ℝ) * C ^ (2 : ℕ) + r ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hsq hcoef_nonneg
  exact le_trans hsumP hmul
