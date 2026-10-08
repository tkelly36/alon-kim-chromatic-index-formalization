import Tablet.Preamble
import Tablet.TablePairBound
import Tablet.TableColumnPairSquareBound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped BigOperators

-- [TABLET NODE: TablePairStability]
theorem TablePairStability :
    ∀ {k n : ℕ} (hk : 2 ≤ k) (C delta : ℝ) (A : Fin k → Fin n → ℝ),
      0 < C →
      0 < delta →
      (∀ i j, 0 ≤ A i j) →
      (∀ j, (∑ i : Fin k, A i j) ≤ C) →
      (∃ j1 j2 : Fin n, j1 ≠ j2 ∧
        ∃ i0 : Fin k,
          delta ≤
            |(∑ i : Fin k, if i = i0 then 0 else A i j1 + A i j2) -
              2 * (1 - 1 / (k : ℝ)) * C|) →
      (∑ j : Fin n,
          ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0))
        ≤ (((k : ℝ) - 1) / (2 * (k : ℝ))) * (n : ℝ) * C ^ (2 : ℕ) -
          ((k : ℝ) * delta ^ (2 : ℕ)) / (4 * ((k : ℝ) - 1)) := by
-- BODY
  intro k n hk C delta A hC hdelta hnonneg hcol hex
  let alpha : ℝ := (((k : ℝ) - 1) / (2 * (k : ℝ)))
  let beta : ℝ := ((k : ℝ) / (2 * ((k : ℝ) - 1)))
  let center : ℝ := (1 - 1 / (k : ℝ)) * C
  let B : Fin n → ℝ := fun j => ∑ i : Fin k, A i j
  let P : Fin n → ℝ := fun j =>
    ∑ i : Fin k, ∑ i' : Fin k, (if i < i' then A i j * A i' j else 0)
  obtain ⟨j1, j2, hj12, i0, habs⟩ := hex
  have hkpos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hkminus_pos : 0 < (k : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hcoef_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr (by linarith [hkminus_pos])) (mul_nonneg (by norm_num) hkpos.le)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg hkpos.le (mul_nonneg (by norm_num) hkminus_pos.le)
  have hselected : ∀ j : Fin n,
      P j ≤ alpha * C ^ (2 : ℕ) - beta * ((∑ i ∈ Finset.univ.erase i0, A i j) - center) ^ (2 : ℕ) := by
    intro j
    let t : ℝ := ∑ i ∈ Finset.univ.erase i0, A i j
    let a0 : ℝ := A i0 j
    let Q : ℝ := ∑ i : Fin k, (A i j)^2
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      exact Finset.sum_nonneg (fun i _ => hnonneg i j)
    have ha0_nonneg : 0 ≤ a0 := by
      dsimp [a0]
      exact hnonneg i0 j
    have hB_eq : B j = a0 + t := by
      dsimp [B, a0, t]
      rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
        (fun i : Fin k => A i j) (Finset.mem_univ i0)]
    have ha0_le : a0 ≤ C - t := by
      have hcolj : B j ≤ C := hcol j
      rw [hB_eq] at hcolj
      linarith
    have hoff_cauchy : t ^ (2 : ℕ) ≤ (∑ i ∈ Finset.univ.erase i0, (A i j)^2) * ((k : ℝ) - 1) := by
      dsimp [t]
      have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i0)
        (fun i : Fin k => A i j) (fun _ => (1 : ℝ))
      simpa [Finset.sum_const, Finset.card_erase_of_mem, Fintype.card_fin, nsmul_eq_mul,
        pow_two, Nat.cast_sub (by exact hkpos_nat), mul_comm, mul_left_comm, mul_assoc] using hraw
    have hQ_lower : a0 ^ (2 : ℕ) + t ^ (2 : ℕ) / ((k : ℝ) - 1) ≤ Q := by
      have hdiv : t ^ (2 : ℕ) / ((k : ℝ) - 1) ≤ ∑ i ∈ Finset.univ.erase i0, (A i j)^2 := by
        exact (div_le_iff₀ hkminus_pos).2 (by simpa [mul_comm] using hoff_cauchy)
      have hQsplit : Q = a0 ^ (2 : ℕ) + ∑ i ∈ Finset.univ.erase i0, (A i j)^2 := by
        dsimp [Q, a0]
        rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
          (fun i : Fin k => (A i j)^2) (Finset.mem_univ i0)]
      rw [hQsplit]
      exact add_le_add (le_refl _) hdiv
    have hid : 2 * P j + Q = (B j)^2 := by
      let Q' : ℝ := ∑ i : Fin k, (A i j)^2
      have hdiag :
          (∑ i : Fin k, ∑ i' : Fin k,
              (if i = i' then A i j * A i' j else 0)) = Q' := by
        dsimp [Q']
        simp [pow_two]
      have hdiag' : (∑ i : Fin k, A i j * A i j) = Q' := by
        simpa using hdiag
      have hswap :
          (∑ i : Fin k, ∑ i' : Fin k,
              (if i' < i then A i j * A i' j else 0)) = P j := by
        dsimp [P]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro i' _
        by_cases h : i < i'
        · simp [h, mul_comm]
        · simp [h]
      have hpoint : ∀ i i' : Fin k,
          (if i < i' then A i j * A i' j else 0) +
            (if i' < i then A i j * A i' j else 0) +
            (if i = i' then A i j * A i' j else 0)
            = A i j * A i' j := by
        intro i i'
        rcases lt_trichotomy i i' with hlt | heq | hgt
        · simp [hlt, ne_of_lt hlt, not_lt_of_gt hlt]
        · subst i'
          simp
        · simp [hgt, ne_of_gt hgt, not_lt_of_gt hgt]
      have hsum :
          (∑ i : Fin k, ∑ i' : Fin k,
            ((if i < i' then A i j * A i' j else 0) +
              (if i' < i then A i j * A i' j else 0) +
              (if i = i' then A i j * A i' j else 0)))
            =
          (∑ i : Fin k, ∑ i' : Fin k, A i j * A i' j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro i' _
        exact hpoint i i'
      calc
        2 * P j + Q
            = (∑ i : Fin k, ∑ i' : Fin k,
                ((if i < i' then A i j * A i' j else 0) +
                  (if i' < i then A i j * A i' j else 0) +
                  (if i = i' then A i j * A i' j else 0))) := by
              symm
              have hdiagQ : (∑ i : Fin k, A i j * A i j) = Q := by
                dsimp [Q]
                simp [pow_two]
              simp [P, Finset.sum_add_distrib, hswap, hdiagQ, two_mul, add_assoc]
        _ = (∑ i : Fin k, ∑ i' : Fin k, A i j * A i' j) := hsum
        _ = (B j)^2 := by
              dsimp [B]
              rw [pow_two, Finset.sum_mul]
              simp_rw [Finset.mul_sum]
    have hP_intermediate : P j ≤ a0 * t + (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * t ^ (2 : ℕ) := by
      have hQineq : 2 * P j + (a0 ^ (2 : ℕ) + t ^ (2 : ℕ) / ((k : ℝ) - 1)) ≤ (a0 + t) ^ (2 : ℕ) := by
        rw [← hB_eq, ← hid]
        nlinarith [hQ_lower]
      field_simp [ne_of_gt hkminus_pos] at hQineq ⊢
      nlinarith [hQineq, hkminus_pos]
    have hquad : a0 * t + (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * t ^ (2 : ℕ)
        ≤ alpha * C ^ (2 : ℕ) - beta * (t - center) ^ (2 : ℕ) := by
      have ha0t : a0 * t ≤ (C - t) * t := by
        exact mul_le_mul_of_nonneg_right ha0_le ht_nonneg
      have hidquad :
          (C - t) * t + (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * t ^ (2 : ℕ) =
            alpha * C ^ (2 : ℕ) - beta * (t - center) ^ (2 : ℕ) := by
        dsimp [alpha, beta, center]
        field_simp [ne_of_gt hkpos, ne_of_gt hkminus_pos]
        ring
      calc
        a0 * t + (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * t ^ (2 : ℕ)
            ≤ (C - t) * t + (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * t ^ (2 : ℕ) := by
              nlinarith [ha0t]
        _ = alpha * C ^ (2 : ℕ) - beta * (t - center) ^ (2 : ℕ) := hidquad
    exact le_trans hP_intermediate hquad
  have hcol_bound : ∀ j : Fin n, P j ≤ alpha * C ^ (2 : ℕ) := by
    intro j
    have hB_nonneg : 0 ≤ B j := by
      dsimp [B]
      exact Finset.sum_nonneg (fun i _ => hnonneg i j)
    have hB_le_C : B j ≤ C := hcol j
    have hBsq_le_Csq : (B j) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
      nlinarith [hB_nonneg, hB_le_C, hC]
    have hp := TableColumnPairSquareBound hk (fun i : Fin k => A i j)
    have hmul := mul_le_mul_of_nonneg_left hBsq_le_Csq hcoef_nonneg
    have hp' : P j ≤ alpha * (B j) ^ (2 : ℕ) := by
      simpa [P, B, alpha] using hp
    exact le_trans hp' hmul
  let loss : Fin n → ℝ := fun j =>
    if j = j1 then beta * ((∑ i ∈ Finset.univ.erase i0, A i j1) - center) ^ (2 : ℕ)
    else if j = j2 then beta * ((∑ i ∈ Finset.univ.erase i0, A i j2) - center) ^ (2 : ℕ)
    else 0
  have hper : ∀ j : Fin n, P j ≤ alpha * C ^ (2 : ℕ) - loss j := by
    intro j
    by_cases h1 : j = j1
    · subst j
      rw [show loss j1 = beta * ((∑ i ∈ Finset.univ.erase i0, A i j1) - center) ^ (2 : ℕ) by simp [loss]]
      exact hselected j1
    · by_cases h2 : j = j2
      · subst j
        rw [show loss j2 = beta * ((∑ i ∈ Finset.univ.erase i0, A i j2) - center) ^ (2 : ℕ) by simp [loss, h1]]
        exact hselected j2
      · have hb := hcol_bound j
        simp [loss, h1, h2]
        exact hb
  have hsumper : (∑ j : Fin n, P j) ≤ ∑ j : Fin n, (alpha * C ^ (2 : ℕ) - loss j) := by
    exact Finset.sum_le_sum (fun j _ => hper j)
  have hsumloss : (∑ j : Fin n, loss j) =
      beta * ((∑ i ∈ Finset.univ.erase i0, A i j1) - center) ^ (2 : ℕ) +
      beta * ((∑ i ∈ Finset.univ.erase i0, A i j2) - center) ^ (2 : ℕ) := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) loss (Finset.mem_univ j1)]
    rw [← Finset.add_sum_erase (Finset.univ.erase j1) loss
      (by simp [hj12.symm] : j2 ∈ Finset.univ.erase j1)]
    have hrest : (∑ x ∈ (Finset.univ.erase j1).erase j2, loss x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx' : x ∈ (Finset.univ.erase j1).erase j2 := hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx'
      simp [loss, hx'.1, hx'.2]
    rw [hrest]
    simp [loss, hj12, hj12.symm, add_assoc]
  have hsum_const : (∑ j : Fin n, (alpha * C ^ (2 : ℕ) - loss j)) =
      (n : ℝ) * (alpha * C ^ (2 : ℕ)) - ∑ j : Fin n, loss j := by
    simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdeficit :
      ((k : ℝ) * delta ^ (2 : ℕ)) / (4 * ((k : ℝ) - 1)) ≤ ∑ j : Fin n, loss j := by
    let x : ℝ := (∑ i ∈ Finset.univ.erase i0, A i j1) - center
    let y : ℝ := (∑ i ∈ Finset.univ.erase i0, A i j2) - center
    have hifsum :
        (∑ i : Fin k, if i = i0 then 0 else A i j1 + A i j2) =
          ∑ i ∈ Finset.univ.erase i0, (A i j1 + A i j2) := by
      let f : Fin k → ℝ := fun i => if i = i0 then 0 else A i j1 + A i j2
      have hf0 : f i0 = 0 := by simp [f]
      have hsumf : (∑ i : Fin k, f i) = ∑ i ∈ Finset.univ.erase i0, f i :=
        (Finset.sum_erase (s := (Finset.univ : Finset (Fin k))) (f := f) (a := i0) hf0).symm
      have herase : (∑ i ∈ Finset.univ.erase i0, f i) =
          ∑ i ∈ Finset.univ.erase i0, (A i j1 + A i j2) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
        simp [f, hi]
      calc
        (∑ i : Fin k, if i = i0 then 0 else A i j1 + A i j2) = ∑ i : Fin k, f i := by rfl
        _ = ∑ i ∈ Finset.univ.erase i0, f i := hsumf
        _ = ∑ i ∈ Finset.univ.erase i0, (A i j1 + A i j2) := herase
    have habsxy : delta ≤ |x + y| := by
      rw [hifsum] at habs
      dsimp [x, y, center] at habs ⊢
      rw [Finset.sum_add_distrib] at habs
      convert habs using 2
      ring
    have hsq_abs : delta ^ (2 : ℕ) ≤ (x + y) ^ (2 : ℕ) := by
      have hdelta_nonneg : 0 ≤ delta := hdelta.le
      have h := sq_le_sq.mpr (abs_le.mpr ⟨?_, habsxy⟩)
      · simpa [sq_abs] using h
      · nlinarith [hdelta_nonneg, abs_nonneg (x + y)]
    have hxy : (x + y) ^ (2 : ℕ) ≤ 2 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg (x - y)]
    have hxy2 : delta ^ (2 : ℕ) / 2 ≤ x ^ (2 : ℕ) + y ^ (2 : ℕ) := by
      nlinarith
    rw [hsumloss]
    dsimp [loss, beta, x, y]
    field_simp [ne_of_gt hkminus_pos] at hxy2 ⊢
    nlinarith [hxy2, hkpos, hkminus_pos]
  calc
    (∑ j : Fin n, ∑ i : Fin k, ∑ i' : Fin k, (if i < i' then A i j * A i' j else 0))
        = ∑ j : Fin n, P j := by rfl
    _ ≤ ∑ j : Fin n, (alpha * C ^ (2 : ℕ) - loss j) := hsumper
    _ = (n : ℝ) * (alpha * C ^ (2 : ℕ)) - ∑ j : Fin n, loss j := hsum_const
    _ ≤ (n : ℝ) * (alpha * C ^ (2 : ℕ)) - ((k : ℝ) * delta ^ (2 : ℕ)) / (4 * ((k : ℝ) - 1)) := by
          linarith
    _ = (((k : ℝ) - 1) / (2 * (k : ℝ))) * (n : ℝ) * C ^ (2 : ℕ) -
          ((k : ℝ) * delta ^ (2 : ℕ)) / (4 * ((k : ℝ) - 1)) := by
          dsimp [alpha]
          ring
