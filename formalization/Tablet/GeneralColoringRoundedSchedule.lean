import Tablet.Preamble

-- [TABLET NODE: GeneralColoringRoundedSchedule]
theorem GeneralColoringRoundedSchedule (eps : ℝ) (k : ℕ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hk : 0 < k) :
    ∃ A : ℕ, ∀ gamma0 : ℕ, ∃ gamma : ℕ, gamma0 ≤ gamma ∧ 0 < gamma ∧
      ∀ Dn : ℕ, ∃ D0 : ℕ, ∀ D : ℝ, (D0 : ℝ) ≤ D →
        ∀ theta : ℝ, 0 < theta → theta < 1 →
          ∃ (s : ℕ) (N K : ℕ → ℕ),
            D ≤ (N 0 : ℝ) ∧
            Nat.ceil ((k : ℝ) * N 0 / gamma) ≤ K 0 ∧
            (∀ i, i < s →
              Dn ≤ N i ∧ eps * D / 3 ≤ (N i : ℝ) ∧
              K i ≤ A * N i ∧ K i ≤ K (i + 1) ∧
              (1 - (1 - eps / 6) / gamma) * N i ≤ (N (i + 1) : ℝ) ∧
              (1 - theta - eps / 6) * (Nat.ceil ((k : ℝ) * N i / gamma) : ℝ) +
                ((K (i + 1) : ℝ) - K i) ≥
                  (Nat.ceil ((k : ℝ) * N (i + 1) / gamma) : ℝ)) ∧
            ((K s + (k * N s + 1) : ℕ) : ℝ) ≤ (theta + eps) * k * D := by
-- BODY
  classical
  let A := Nat.ceil (6 * (1 + eps) * k / eps)
  refine ⟨A, ?_⟩
  intro gamma0
  let gamma := gamma0 + Nat.ceil (12 / eps) + 1
  have hgNat : 0 < gamma := by dsimp [gamma]; omega
  have hg : (0 : ℝ) < gamma := by exact_mod_cast hgNat
  have hglarge : 12 / eps ≤ (gamma : ℝ) := by
    have := Nat.le_ceil (12 / eps)
    dsimp [gamma]
    push_cast
    linarith only [this, (Nat.cast_nonneg gamma0 : (0 : ℝ) ≤ gamma0)]
  have hginv : 1 / (gamma : ℝ) ≤ eps / 12 := by
    have := (div_le_iff₀ heps).mp hglarge
    apply (div_le_iff₀ hg).mpr
    nlinarith only [this]
  let rho : ℝ := 1 - (1 - eps / 6) / gamma
  have hrho0 : 0 < rho := by
    have hg1 : (1 : ℝ) ≤ gamma := by exact_mod_cast hgNat
    dsimp [rho]
    have : (1 - eps / 6) / (gamma : ℝ) < 1 :=
      (div_lt_iff₀ hg).mpr (by linarith only [hg1, heps])
    linarith only [this]
  have hrho1 : rho < 1 := by
    have : 0 < (1 - eps / 6) / (gamma : ℝ) :=
      div_pos (by linarith only [heps1]) hg
    dsimp [rho]
    linarith only [this]
  refine ⟨gamma, by dsimp [gamma]; omega, hgNat, ?_⟩
  intro Dn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let C : ℝ := 3 * k / 2 + 3 + k / gamma
  obtain ⟨D0, hD0⟩ := exists_nat_gt
    (max 1 (max (60 / eps) (max (3 * Dn / eps)
      (max (6 / (eps * (1 - rho))) (36 * gamma * C / (k * eps ^ 2))))))
  refine ⟨D0, ?_⟩
  intro D hD theta htheta htheta1
  have hlarge := le_trans (le_of_lt hD0) hD
  simp only [max_le_iff] at hlarge
  rcases hlarge with ⟨hD1, hD60, hDn, hstop, hlist⟩
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have heD : 60 ≤ eps * D := by
    have := (div_le_iff₀ heps).mp hD60
    nlinarith only [this]
  let T : ℝ := eps * D / 3
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hDnT : (Dn : ℝ) ≤ T := by
    have := (div_le_iff₀ heps).mp hDn
    dsimp [T]
    nlinarith only [this]
  have hstopT : 2 ≤ (1 - rho) * T := by
    have := (div_le_iff₀ (mul_pos heps (sub_pos.mpr hrho1))).mp hstop
    dsimp [T]
    nlinarith only [this]
  have hlistD : C ≤ k * eps ^ 2 * D / (36 * gamma) := by
    have := (div_le_iff₀ (mul_pos hkR (sq_pos_of_pos heps))).mp hlist
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 36 * gamma)).mpr
    nlinarith only [this]
  let B := Nat.ceil D
  have hDB : D ≤ (B : ℝ) := Nat.le_ceil D
  have hBD : (B : ℝ) < D + 1 := Nat.ceil_lt_add_one hDpos.le
  let N : ℕ → ℕ := fun i =>
    Nat.rec (motive := fun _ => ℕ) B (fun _ n => Nat.ceil (rho * (n : ℝ))) i
  have hN0 : N 0 = B := rfl
  have hNsucc (i : ℕ) : N (i + 1) = Nat.ceil (rho * N i) := rfl
  have hNlower (i : ℕ) : rho * N i ≤ (N (i + 1) : ℝ) := by
    rw [hNsucc]
    exact Nat.le_ceil _
  have hNupper (i : ℕ) : (N (i + 1) : ℝ) < rho * N i + 1 := by
    rw [hNsucc]
    exact Nat.ceil_lt_add_one (by positivity)
  have hdescent (i : ℕ) (hi : T ≤ (N i : ℝ)) : N (i + 1) < N i := by
    have hm := mul_le_mul_of_nonneg_left hi (sub_pos.mpr hrho1).le
    have hu := hNupper i
    have : (N (i + 1) : ℝ) < N i := by nlinarith only [hm, hu, hstopT]
    exact_mod_cast this
  have hexit : ∃ s, (N s : ℝ) < T := by
    by_contra! hnever
    have hbound : ∀ i, N i + i ≤ B := by
      intro i
      induction i with
      | zero => simp [hN0]
      | succ i ih =>
        have := hdescent i (hnever i)
        omega
    have := hbound (B + 1)
    omega
  let s := Nat.find hexit
  have hs : (N s : ℝ) < T := Nat.find_spec hexit
  have hbefore (i : ℕ) (hi : i < s) : T ≤ (N i : ℝ) :=
    le_of_not_gt (Nat.find_min hexit hi)
  have hNB (i : ℕ) (hi : i ≤ s) : N i ≤ B := by
    induction i with
    | zero => simp [hN0]
    | succ i ih =>
      have hlt : i < s := by omega
      exact le_trans (hdescent i (hbefore i hlt)).le (ih (by omega))
  let K : ℕ → ℕ := fun i =>
    Nat.ceil ((theta + eps / 2) * k * ((B : ℝ) - N i) + k * B / gamma)
  have hKarg (i : ℕ) (hi : i ≤ s) :
      0 ≤ (theta + eps / 2) * k * ((B : ℝ) - N i) + k * B / gamma := by
    have : (N i : ℝ) ≤ B := by exact_mod_cast hNB i hi
    have : 0 ≤ (B : ℝ) - N i := sub_nonneg.mpr this
    positivity
  have hKlower (i : ℕ) :
      (theta + eps / 2) * k * ((B : ℝ) - N i) + k * B / gamma ≤ (K i : ℝ) :=
    Nat.le_ceil _
  have hKupper (i : ℕ) (hi : i ≤ s) :
      (K i : ℝ) < (theta + eps / 2) * k * ((B : ℝ) - N i) + k * B / gamma + 1 :=
    Nat.ceil_lt_add_one (hKarg i hi)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : (k : ℝ) * B / gamma ≤ eps / 12 * k * B := by
    have := mul_le_mul_of_nonneg_left hginv
      (by positivity : (0 : ℝ) ≤ (k : ℝ) * B)
    convert this using 1 <;> ring
  have hKbudget (i : ℕ) (hi : i ≤ s) :
      (K i : ℝ) ≤ (theta + 7 * eps / 12) * k * B + 1 := by
    have hn : 0 ≤ (theta + eps / 2) * k * (N i : ℝ) := by positivity
    nlinarith only [hKupper i hi, hfrac, hn]
  have hkeD : 60 * (k : ℝ) ≤ eps * k * D := by
    nlinarith only [mul_le_mul_of_nonneg_left heD hkR.le]
  have heDB : eps * k * D ≤ eps * k * B :=
    mul_le_mul_of_nonneg_left hDB (by positivity)
  have hA : 6 * (1 + eps) * k ≤ eps * (A : ℝ) := by
    have := (div_le_iff₀ heps).mp (Nat.le_ceil (6 * (1 + eps) * k / eps))
    nlinarith only [this]
  refine ⟨s, N, K, hDB, ?_, ?_, ?_⟩
  · simp [K, hN0]
  · intro i hi
    have hTi := hbefore i hi
    have hnext := hdescent i hTi
    have hnextR : (N (i + 1) : ℝ) ≤ N i := by exact_mod_cast hnext.le
    refine ⟨?_, hTi, ?_, ?_, hNlower i, ?_⟩
    · exact_mod_cast le_trans hDnT hTi
    · have hKB : (K i : ℝ) ≤ (1 + eps) * k * B := by
        have ht := mul_le_mul_of_nonneg_right htheta1.le
          (by positivity : (0 : ℝ) ≤ (k : ℝ) * B)
        nlinarith only [hKbudget i (by omega), ht, hkeD, heDB, hk1]
      have hB2 : (B : ℝ) ≤ 2 * D := by linarith only [hBD, hD1]
      have hBbound := mul_le_mul_of_nonneg_left hB2
        (by positivity : 0 ≤ (1 + eps) * (k : ℝ))
      have hAbound := mul_le_mul_of_nonneg_right hA hDpos.le
      have hNbound := mul_le_mul_of_nonneg_left hTi
        (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
      have : (K i : ℝ) ≤ (A : ℝ) * N i := by
        dsimp [T] at hNbound
        nlinarith only [hKB, hBbound, hAbound, hNbound]
      exact_mod_cast this
    · apply Nat.ceil_mono
      have hc : 0 ≤ (theta + eps / 2) * (k : ℝ) := by positivity
      nlinarith only [hc, hnextR]
    · let q : ℝ := k * N i / gamma
      let c : ℝ := 1 - theta - eps / 6
      let a : ℝ := theta + eps / 2
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have ha : 0 ≤ a * (k : ℝ) := by dsimp [a]; positivity
      have hc : -eps / 6 ≤ c := by dsimp [c]; linarith only [htheta1]
      have hceil : c * (Nat.ceil q : ℝ) ≥ c * q - eps / 6 := by
        by_cases hc0 : 0 ≤ c
        · have := mul_le_mul_of_nonneg_left (Nat.le_ceil q) hc0
          linarith only [this, heps]
        · have := mul_le_mul_of_nonpos_left
            (Nat.ceil_lt_add_one hq).le (le_of_not_ge hc0)
          nlinarith only [this, hc]
      have hdiff : a * k * ((N i : ℝ) - N (i + 1)) - 1 ≤
          (K (i + 1) : ℝ) - K i := by
        have hu := hKupper i (by omega)
        have hl := hKlower (i + 1)
        dsimp [a]
        nlinarith only [hu, hl]
      have hdrop := mul_le_mul_of_nonneg_left (hNupper i).le ha
      have hstep : a * k * ((1 - rho) * N i - 1) - 1 ≤
          (K (i + 1) : ℝ) - K i := by
        nlinarith only [hdiff, hdrop]
      have hpoly : 1 + eps / 12 ≤ c + a * (1 - eps / 6) := by
        have hsmall : 1 + theta + eps / 2 ≤ 5 / 2 := by
          linarith only [htheta1, heps1]
        have := mul_le_mul_of_nonneg_left hsmall heps.le
        dsimp [c, a]
        nlinarith only [this]
      have hid : c * q + a * k * (1 - rho) * N i =
          (c + a * (1 - eps / 6)) * q := by
        dsimp [q, rho]
        ring
      have hmain : (1 + eps / 12) * q - a * k - 1 - eps / 6 ≤
          c * (Nat.ceil q : ℝ) + ((K (i + 1) : ℝ) - K i) := by
        have hm := mul_le_mul_of_nonneg_right hpoly hq
        nlinarith only [hceil, hstep, hid, hm]
      have hqnext : (k : ℝ) * N (i + 1) / gamma ≤ q := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnextR hkR.le) hg.le
      have hlnext : (Nat.ceil ((k : ℝ) * N (i + 1) / gamma) : ℝ) ≤ q + 1 := by
        have := Nat.ceil_lt_add_one
          (by positivity : (0 : ℝ) ≤ (k : ℝ) * N (i + 1) / gamma)
        linarith only [this, hqnext]
      have herror : C ≤ eps / 12 * q := by
        have ht := mul_le_mul_of_nonneg_left hTi
          (by positivity : 0 ≤ (k : ℝ) * eps / (12 * gamma))
        have heq : (k : ℝ) * eps / (12 * gamma) * T =
            k * eps ^ 2 * D / (36 * gamma) := by dsimp [T]; ring
        have heq' : (k : ℝ) * eps / (12 * gamma) * N i = eps / 12 * q := by
          dsimp [q]; ring
        rw [heq, heq'] at ht
        exact le_trans hlistD ht
      have hak : a * (k : ℝ) ≤ 3 * k / 2 := by
        have := mul_le_mul_of_nonneg_right
          (show a ≤ 3 / 2 by dsimp [a]; linarith only [htheta1, heps1]) hkR.le
        nlinarith only [this]
      change c * (Nat.ceil q : ℝ) + ((K (i + 1) : ℝ) - K i) ≥ _
      have hkg : (0 : ℝ) ≤ (k : ℝ) / gamma := by positivity
      dsimp [C] at herror
      nlinarith only [hmain, hlnext, herror, hak, heps1, hkg]
  · have hcoeff : (theta + 7 * eps / 12) * (k : ℝ) ≤ 19 * k / 12 := by
      nlinarith only [mul_le_mul_of_nonneg_right htheta1.le hkR.le,
        mul_le_mul_of_nonneg_right heps1 hkR.le]
    have hround := mul_le_mul_of_nonneg_left (le_of_lt hBD)
      (by positivity : 0 ≤ (theta + 7 * eps / 12) * (k : ℝ))
    have hterminal := mul_le_mul_of_nonneg_left hs.le hkR.le
    have hbound := hKbudget s le_rfl
    dsimp [T] at hterminal
    push_cast
    nlinarith only [hbound, hround, hterminal, hcoeff, hkeD, hk1]
