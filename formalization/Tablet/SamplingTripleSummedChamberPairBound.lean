import Tablet.SamplingTripleFullChamberIntegralEstimate
import Tablet.SamplingTripleFullWeightPairingNormalizer
import Tablet.SamplingTriplePairedChamberParameterNormalizer
import Tablet.SamplingTriplePatternCountingBridge
import Tablet.SamplingTripleRealChamberEstimate

open BigOperators

-- [TABLET NODE: SamplingTripleSummedChamberPairBound]
theorem SamplingTripleSummedChamberPairBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (a b c : V)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c)
    (hab_nonadj : ¬ G.Adj a b) (hac_nonadj : ¬ G.Adj a c)
    (hbc_nonadj : ¬ G.Adj b c)
    (ell_ab ell_ac ell_bc : ℝ)
    (n_a n_b n_c n_ab n_ac n_bc n_abc : ℕ)
    (hDelta_pos : 0 < (Delta : ℝ))
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le : gamma ≤ (Delta : ℝ))
    (hell_ab_pos : 0 < 1 - ell_ab)
    (hell_ac_pos : 0 < 1 - ell_ac)
    (hell_bc_pos : 0 < 1 - ell_bc)
    (hcount_a :
      n_a =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card)
    (hcount_b :
      n_b =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card)
    (hcount_c :
      n_c =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card)
    (hcount_ab :
      n_ab =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card)
    (hcount_ac :
      n_ac =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card)
    (hcount_bc :
      n_bc =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card)
    (hcount_abc :
      n_abc =
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, b, c} : Finset V) ∧
            G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card)
    (hell_ab : ell_ab = ((n_ab + n_abc : ℕ) : ℝ) / (Delta : ℝ))
    (hell_ac : ell_ac = ((n_ac + n_abc : ℕ) : ℝ) / (Delta : ℝ))
    (hell_bc : ell_bc = ((n_bc + n_abc : ℕ) : ℝ) / (Delta : ℝ))
    (hdeg_a : n_a + n_ab + n_ac + n_abc = Delta)
    (hdeg_b : n_b + n_ab + n_bc + n_abc = Delta)
    (hdeg_c : n_c + n_ac + n_bc + n_abc = Delta) :
    let Q : Finset V := {a, b, c}
    let orders : Finset (V × V × V) :=
      {((a, b, c) : V × V × V), (a, c, b), (b, a, c),
        (b, c, a), (c, a, b), (c, b, a)}
    let fullWeight : V × V × V → ℝ := fun t =>
      (1 / (Delta : ℝ) ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / (Delta : ℝ)) ^
                  (((Finset.univ : Finset V).filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ G.Adj t.1 w).card) *
                (1 - y / (Delta : ℝ)) ^
                  (((Finset.univ : Finset V).filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                      ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                  (1 - z / (Delta : ℝ)) ^
                    (((Finset.univ : Finset V).filter fun w : V =>
                      w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                        ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧
                          G.Adj t.2.2 w).card)
    (∑ t ∈ orders, fullWeight t) ≤
      (1 / (Delta : ℝ) ^ 3) *
        (1 + (1 / 3) *
          ((2 / ((2 - ell_ab) * (1 - ell_ab)) - 1) +
            (2 / ((2 - ell_ac) * (1 - ell_ac)) - 1) +
              (2 / ((2 - ell_bc) * (1 - ell_bc)) - 1))) := by
-- BODY
  classical
  intro Q orders fullWeight
  let C_ab : ℕ := n_ab + n_abc
  let C_ac : ℕ := n_ac + n_abc
  let C_bc : ℕ := n_bc + n_abc
  let N_ab : ℕ := Delta - C_ab
  let N_ac : ℕ := Delta - C_ac
  let N_bc : ℕ := Delta - C_bc
  let x : ℝ := 1 - ell_ab
  let y : ℝ := 1 - ell_ac
  let z : ℝ := 1 - ell_bc
  let tau : ℝ := (n_abc : ℝ) / (Delta : ℝ)
  let rho_x : ℝ := (n_c : ℝ) / (Delta : ℝ)
  let rho_y : ℝ := (n_b : ℝ) / (Delta : ℝ)
  let rho_z : ℝ := (n_a : ℝ) / (Delta : ℝ)
  let Iab : ℝ :=
    ∫ u in (0 : ℝ)..gamma,
      ∫ v in u..gamma,
        ∫ w in v..gamma,
          (1 - w / (Delta : ℝ)) ^ Delta *
            (1 - v / (Delta : ℝ)) ^ N_ab *
              (1 - u / (Delta : ℝ)) ^ n_c
  let Iac : ℝ :=
    ∫ u in (0 : ℝ)..gamma,
      ∫ v in u..gamma,
        ∫ w in v..gamma,
          (1 - w / (Delta : ℝ)) ^ Delta *
            (1 - v / (Delta : ℝ)) ^ N_ac *
              (1 - u / (Delta : ℝ)) ^ n_b
  let Ibc : ℝ :=
    ∫ u in (0 : ℝ)..gamma,
      ∫ v in u..gamma,
        ∫ w in v..gamma,
          (1 - w / (Delta : ℝ)) ^ Delta *
            (1 - v / (Delta : ℝ)) ^ N_bc *
              (1 - u / (Delta : ℝ)) ^ n_a
  have hmid_ab_nat : N_ab + C_ab = Delta := by
    dsimp [N_ab, C_ab]
    omega
  have hmid_ac_nat : N_ac + C_ac = Delta := by
    dsimp [N_ac, C_ac]
    omega
  have hmid_bc_nat : N_bc + C_bc = Delta := by
    dsimp [N_bc, C_bc]
    omega
  have hlow_ab_nat : n_c + C_ac + C_bc = Delta + n_abc := by
    dsimp [C_ac, C_bc]
    omega
  have hlow_ac_nat : n_b + C_ab + C_bc = Delta + n_abc := by
    dsimp [C_ab, C_bc]
    omega
  have hlow_bc_nat : n_a + C_ab + C_ac = Delta + n_abc := by
    dsimp [C_ab, C_ac]
    omega
  have hnorm :=
    SamplingTriplePairedChamberParameterNormalizer Delta ell_ab ell_ac ell_bc
      C_ab C_ac C_bc n_abc N_ab n_c N_ac n_b N_bc n_a
      hDelta_pos hell_ab_pos hell_ac_pos hell_bc_pos
      (by simpa [C_ab] using hell_ab)
      (by simpa [C_ac] using hell_ac)
      (by simpa [C_bc] using hell_bc)
      hmid_ab_nat hmid_ac_nat hmid_bc_nat
      hlow_ab_nat hlow_ac_nat hlow_bc_nat
  dsimp only at hnorm
  rcases hnorm with
    ⟨hx, hy, hz, hrx, hry, hrz, htau, hNab, hncr, hNac, hnbr, hNbc, hnar,
      hMx, hMy, hMz⟩
  have hfull :=
    SamplingTripleFullChamberIntegralEstimate Delta gamma x y z tau rho_x rho_y rho_z
      N_ab n_c N_ac n_b N_bc n_a
      hDelta_pos hgamma_nonneg hgamma_le hx hy hz hrx hry hrz htau
      (by simpa [x] using hNab) (by simpa [rho_x] using hncr)
      (by simpa [y] using hNac) (by simpa [rho_y] using hnbr)
      (by simpa [z] using hNbc) (by simpa [rho_z] using hnar)
      (by simpa [x, y, z, tau, rho_x] using hMx)
      (by simpa [x, y, z, tau, rho_y] using hMy)
      (by simpa [x, y, z, tau, rho_z] using hMz)
  have hreal :=
    SamplingTripleRealChamberEstimate x y z tau hx hy hz htau
  have hanalytic :
      2 * Iab + 2 * Iac + 2 * Ibc ≤
        1 + (1 / 3) *
          ((2 / ((1 + x) * x) - 1) +
            (2 / ((1 + y) * y) - 1) +
              (2 / ((1 + z) * z) - 1)) := by
    have h := hfull.trans hreal
    simpa [Iab, Iac, Ibc] using h
  have hsum_orders :
      (∑ t ∈ orders, fullWeight t) =
        fullWeight (a, b, c) + fullWeight (b, a, c) +
            fullWeight (a, c, b) + fullWeight (c, a, b) +
          fullWeight (b, c, a) + fullWeight (c, b, a) := by
    have hsum_any (f : V × V × V → ℝ) :
        (∑ t ∈ orders, f t) =
          f (a, b, c) + f (b, a, c) + f (a, c, b) + f (c, a, b) +
            f (b, c, a) + f (c, b, a) := by
      simp [orders, hab_ne, hac_ne, hbc_ne, hab_ne.symm, hac_ne.symm, hbc_ne.symm,
        add_assoc, add_left_comm, add_comm]
    exact hsum_any fullWeight
  have hpair_raw :=
      SamplingTripleFullWeightPairingNormalizer G Delta gamma a b c
        hab_ne hac_ne hbc_ne hab_nonadj hac_nonadj hbc_nonadj
        n_a n_b n_c n_ab n_ac n_bc n_abc
        hcount_a hcount_b hcount_c hcount_ab hcount_ac hcount_bc hcount_abc
        hdeg_a hdeg_b hdeg_c
  dsimp only at hpair_raw
  have hscaled :
      (1 / (Delta : ℝ) ^ 3) * (2 * Iab + 2 * Iac + 2 * Ibc) ≤
        (1 / (Delta : ℝ) ^ 3) *
          (1 + (1 / 3) *
            ((2 / ((1 + x) * x) - 1) +
              (2 / ((1 + y) * y) - 1) +
                (2 / ((1 + z) * z) - 1))) := by
    exact mul_le_mul_of_nonneg_left hanalytic (by positivity)
  have hmain :
      (∑ t ∈ orders, fullWeight t) ≤
        (1 / (Delta : ℝ) ^ 3) *
          (1 + (1 / 3) *
            ((2 / ((1 + x) * x) - 1) +
              (2 / ((1 + y) * y) - 1) +
                (2 / ((1 + z) * z) - 1))) := by
    rw [hsum_orders]
    rw [hpair_raw]
    change (1 / (Delta : ℝ) ^ 3) * (2 * Iab + 2 * Iac + 2 * Ibc) ≤
      (1 / (Delta : ℝ) ^ 3) *
        (1 + (1 / 3) *
          ((2 / ((1 + x) * x) - 1) +
            (2 / ((1 + y) * y) - 1) +
              (2 / ((1 + z) * z) - 1)))
    exact hscaled
  have hxden : (1 + x) * x = (2 - ell_ab) * (1 - ell_ab) := by
    dsimp [x]
    ring
  have hyden : (1 + y) * y = (2 - ell_ac) * (1 - ell_ac) := by
    dsimp [y]
    ring
  have hzden : (1 + z) * z = (2 - ell_bc) * (1 - ell_bc) := by
    dsimp [z]
    ring
  simpa [hxden, hyden, hzden] using hmain
