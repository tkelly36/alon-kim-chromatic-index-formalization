import Tablet.SamplingTripleOrderedExponentNormalizer

open BigOperators

-- [TABLET NODE: SamplingTripleFullWeightPairingNormalizer]
theorem SamplingTripleFullWeightPairingNormalizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (a b c : V)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c)
    (hab_nonadj : ¬ G.Adj a b) (hac_nonadj : ¬ G.Adj a c)
    (hbc_nonadj : ¬ G.Adj b c)
    (n_a n_b n_c n_ab n_ac n_bc n_abc : ℕ)
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
    (hdeg_a : n_a + n_ab + n_ac + n_abc = Delta)
    (hdeg_b : n_b + n_ab + n_bc + n_abc = Delta)
    (hdeg_c : n_c + n_ac + n_bc + n_abc = Delta) :
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
    let N_ab : ℕ := Delta - (n_ab + n_abc)
    let N_ac : ℕ := Delta - (n_ac + n_abc)
    let N_bc : ℕ := Delta - (n_bc + n_abc)
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
    fullWeight (a, b, c) + fullWeight (b, a, c) +
        fullWeight (a, c, b) + fullWeight (c, a, b) +
      fullWeight (b, c, a) + fullWeight (c, b, a) =
      (1 / (Delta : ℝ) ^ 3) * (2 * Iab + 2 * Iac + 2 * Ibc) := by
-- BODY
  classical
  intro fullWeight N_ab N_ac N_bc Iab Iac Ibc
  let K : ℝ := 1 / (Delta : ℝ) ^ 3
  change
    fullWeight (a, b, c) + fullWeight (b, a, c) +
        fullWeight (a, c, b) + fullWeight (c, a, b) +
      fullWeight (b, c, a) + fullWeight (c, b, a) =
      K * (2 * Iab + 2 * Iac + 2 * Ibc)
  have htop_abc :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧ G.Adj a w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) a b c
    dsimp only at h
    have h1 := h.1
    rw [← h1]
    rw [← hcount_a, ← hcount_ab, ← hcount_ac, ← hcount_abc]
    exact hdeg_a
  have hmid_abc :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧ ¬ G.Adj a w ∧ G.Adj b w).card = N_ab := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) a b c
    dsimp only at h
    have h1 := h.2.1
    rw [← h1]
    rw [← hcount_b, ← hcount_bc]
    dsimp [N_ab]
    omega
  have hlow_abc :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card =
        n_c := by
    exact hcount_c.symm
  have htop_bac :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, a, c} : Finset V) ∧ G.Adj b w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) b a c
    dsimp only at h
    have hb_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            G.Adj b w ∧ ¬ G.Adj a w ∧ ¬ G.Adj c w).card = n_b := by
      rw [hcount_b]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hba :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            G.Adj b w ∧ G.Adj a w ∧ ¬ G.Adj c w).card = n_ab := by
      rw [hcount_ab]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            G.Adj b w ∧ ¬ G.Adj a w ∧ G.Adj c w).card = n_bc := by
      rw [hcount_bc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbabc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            G.Adj b w ∧ G.Adj a w ∧ G.Adj c w).card = n_abc := by
      rw [hcount_abc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.1
    rw [← h1]
    rw [hb_only, hba, hbc, hbabc]
    exact hdeg_b
  have hmid_bac :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, a, c} : Finset V) ∧ ¬ G.Adj b w ∧ G.Adj a w).card = N_ab := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) b a c
    dsimp only at h
    have ha_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            ¬ G.Adj b w ∧ G.Adj a w ∧ ¬ G.Adj c w).card = n_a := by
      rw [hcount_a]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hac :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, a, c} : Finset V) ∧
            ¬ G.Adj b w ∧ G.Adj a w ∧ G.Adj c w).card = n_ac := by
      rw [hcount_ac]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.2.1
    rw [← h1]
    rw [ha_only, hac]
    dsimp [N_ab]
    omega
  have hlow_bac :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, a, c} : Finset V) ∧ ¬ G.Adj b w ∧ ¬ G.Adj a w ∧ G.Adj c w).card =
        n_c := by
    rw [hcount_c]
    congr 1
    ext w
    simp [and_assoc, and_left_comm, and_comm]
  have htop_acb :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, c, b} : Finset V) ∧ G.Adj a w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) a c b
    dsimp only at h
    have ha_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            G.Adj a w ∧ ¬ G.Adj c w ∧ ¬ G.Adj b w).card = n_a := by
      rw [hcount_a]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hac :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            G.Adj a w ∧ G.Adj c w ∧ ¬ G.Adj b w).card = n_ac := by
      rw [hcount_ac]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hab :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            G.Adj a w ∧ ¬ G.Adj c w ∧ G.Adj b w).card = n_ab := by
      rw [hcount_ab]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have habc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            G.Adj a w ∧ G.Adj c w ∧ G.Adj b w).card = n_abc := by
      rw [hcount_abc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.1
    rw [← h1]
    rw [ha_only, hac, hab, habc]
    omega
  have hmid_acb :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, c, b} : Finset V) ∧ ¬ G.Adj a w ∧ G.Adj c w).card = N_ac := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) a c b
    dsimp only at h
    have hc_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            ¬ G.Adj a w ∧ G.Adj c w ∧ ¬ G.Adj b w).card = n_c := by
      rw [hcount_c]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbc' :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({a, c, b} : Finset V) ∧
            ¬ G.Adj a w ∧ G.Adj c w ∧ G.Adj b w).card = n_bc := by
      rw [hcount_bc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.2.1
    rw [← h1]
    rw [hc_only, hbc']
    dsimp [N_ac]
    omega
  have hlow_acb :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, c, b} : Finset V) ∧ ¬ G.Adj a w ∧ ¬ G.Adj c w ∧ G.Adj b w).card =
        n_b := by
    rw [hcount_b]
    congr 1
    ext w
    simp [and_assoc, and_left_comm, and_comm]
  have htop_cab :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, a, b} : Finset V) ∧ G.Adj c w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) c a b
    dsimp only at h
    have hc_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            G.Adj c w ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w).card = n_c := by
      rw [hcount_c]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hac :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            G.Adj c w ∧ G.Adj a w ∧ ¬ G.Adj b w).card = n_ac := by
      rw [hcount_ac]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbc' :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            G.Adj c w ∧ ¬ G.Adj a w ∧ G.Adj b w).card = n_bc := by
      rw [hcount_bc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have habc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            G.Adj c w ∧ G.Adj a w ∧ G.Adj b w).card = n_abc := by
      rw [hcount_abc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.1
    rw [← h1]
    rw [hc_only, hac, hbc', habc]
    exact hdeg_c
  have hmid_cab :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, a, b} : Finset V) ∧ ¬ G.Adj c w ∧ G.Adj a w).card = N_ac := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) c a b
    dsimp only at h
    have ha_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            ¬ G.Adj c w ∧ G.Adj a w ∧ ¬ G.Adj b w).card = n_a := by
      rw [hcount_a]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hab' :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, a, b} : Finset V) ∧
            ¬ G.Adj c w ∧ G.Adj a w ∧ G.Adj b w).card = n_ab := by
      rw [hcount_ab]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.2.1
    rw [← h1]
    rw [ha_only, hab']
    dsimp [N_ac]
    omega
  have hlow_cab :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, a, b} : Finset V) ∧ ¬ G.Adj c w ∧ ¬ G.Adj a w ∧ G.Adj b w).card =
        n_b := by
    rw [hcount_b]
    congr 1
    ext w
    simp [and_assoc, and_left_comm, and_comm]
  have htop_bca :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, c, a} : Finset V) ∧ G.Adj b w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) b c a
    dsimp only at h
    have hb_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj a w).card = n_b := by
      rw [hcount_b]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbc' :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            G.Adj b w ∧ G.Adj c w ∧ ¬ G.Adj a w).card = n_bc := by
      rw [hcount_bc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hab :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            G.Adj b w ∧ ¬ G.Adj c w ∧ G.Adj a w).card = n_ab := by
      rw [hcount_ab]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have habc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            G.Adj b w ∧ G.Adj c w ∧ G.Adj a w).card = n_abc := by
      rw [hcount_abc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.1
    rw [← h1]
    rw [hb_only, hbc', hab, habc]
    omega
  have hmid_bca :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, c, a} : Finset V) ∧ ¬ G.Adj b w ∧ G.Adj c w).card = N_bc := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) b c a
    dsimp only at h
    have hc_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            ¬ G.Adj b w ∧ G.Adj c w ∧ ¬ G.Adj a w).card = n_c := by
      rw [hcount_c]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hac :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({b, c, a} : Finset V) ∧
            ¬ G.Adj b w ∧ G.Adj c w ∧ G.Adj a w).card = n_ac := by
      rw [hcount_ac]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.2.1
    rw [← h1]
    rw [hc_only, hac]
    dsimp [N_bc]
    omega
  have hlow_bca :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({b, c, a} : Finset V) ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ G.Adj a w).card =
        n_a := by
    rw [hcount_a]
    congr 1
    ext w
    simp [and_assoc, and_left_comm, and_comm]
  have htop_cba :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, b, a} : Finset V) ∧ G.Adj c w).card = Delta := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) c b a
    dsimp only at h
    have hc_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            G.Adj c w ∧ ¬ G.Adj b w ∧ ¬ G.Adj a w).card = n_c := by
      rw [hcount_c]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hbc' :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            G.Adj c w ∧ G.Adj b w ∧ ¬ G.Adj a w).card = n_bc := by
      rw [hcount_bc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hac :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            G.Adj c w ∧ ¬ G.Adj b w ∧ G.Adj a w).card = n_ac := by
      rw [hcount_ac]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have habc :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            G.Adj c w ∧ G.Adj b w ∧ G.Adj a w).card = n_abc := by
      rw [hcount_abc]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.1
    rw [← h1]
    rw [hc_only, hbc', hac, habc]
    omega
  have hmid_cba :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, b, a} : Finset V) ∧ ¬ G.Adj c w ∧ G.Adj b w).card = N_bc := by
    have h := SamplingTripleOrderedExponentNormalizer G (Finset.univ : Finset V) c b a
    dsimp only at h
    have hb_only :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            ¬ G.Adj c w ∧ G.Adj b w ∧ ¬ G.Adj a w).card = n_b := by
      rw [hcount_b]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have hab :
        ((Finset.univ : Finset V).filter fun w : V =>
          w ∉ ({c, b, a} : Finset V) ∧
            ¬ G.Adj c w ∧ G.Adj b w ∧ G.Adj a w).card = n_ab := by
      rw [hcount_ab]
      congr 1
      ext w
      simp [and_assoc, and_left_comm, and_comm]
    have h1 := h.2.1
    rw [← h1]
    rw [hb_only, hab]
    dsimp [N_bc]
    omega
  have hlow_cba :
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({c, b, a} : Finset V) ∧ ¬ G.Adj c w ∧ ¬ G.Adj b w ∧ G.Adj a w).card =
        n_a := by
    rw [hcount_a]
    congr 1
    ext w
    simp [and_assoc, and_left_comm, and_comm]
  have hweight_abc :
      fullWeight (a, b, c) = K * Iab := by
    dsimp [fullWeight, Iab, K]
    rw [htop_abc, hmid_abc, hlow_abc]
  have hweight_bac :
      fullWeight (b, a, c) = K * Iab := by
    dsimp [fullWeight, Iab, K]
    rw [htop_bac, hmid_bac, hlow_bac]
  have hweight_acb :
      fullWeight (a, c, b) = K * Iac := by
    dsimp [fullWeight, Iac, K]
    rw [htop_acb, hmid_acb, hlow_acb]
  have hweight_cab :
      fullWeight (c, a, b) = K * Iac := by
    dsimp [fullWeight, Iac, K]
    rw [htop_cab, hmid_cab, hlow_cab]
  have hweight_bca :
      fullWeight (b, c, a) = K * Ibc := by
    dsimp [fullWeight, Ibc, K]
    rw [htop_bca, hmid_bca, hlow_bca]
  have hweight_cba :
      fullWeight (c, b, a) = K * Ibc := by
    dsimp [fullWeight, Ibc, K]
    rw [htop_cba, hmid_cba, hlow_cba]
  rw [hweight_abc, hweight_bac, hweight_acb, hweight_cab, hweight_bca,
    hweight_cba]
  ring
