import Tablet.Preamble
import Tablet.KPartiteFixedVertexReducedEstimate

set_option maxHeartbeats 1200000

-- [TABLET NODE: KPartiteFixedVertexTotalEstimate]
theorem KPartiteFixedVertexTotalEstimate :
    ∀ k : ℕ, 3 ≤ k → ∀ i : Fin k, ∀ w : Fin k → Fin k → ℝ,
      (∀ a b, 0 ≤ w a b) →
      let edge : Fin k → Fin k → ℝ :=
        fun a b => if a < b then w a b else if b < a then w b a else 0
      let pairs : Finset (Fin k × Fin k) :=
        (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
      let M : ℝ := pairs.sum (fun p => edge p.1 p.2)
      let Mi : ℝ := ∑ j : Fin k, edge i j
      let others := {j : Fin k // j ≠ i}
      let pairsOther : Finset (others × others) :=
        (Finset.univ.filter (fun p : others × others => p.1 < p.2))
      pairsOther.sum
          (fun p =>
            Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1)) ≤
        Mi * Real.sqrt
          ((((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * (M - Mi)) := by
-- BODY
  intro k hk i w hw edge pairs M Mi others pairsOther
  classical
  have hedge_nonneg : ∀ a b : Fin k, 0 ≤ edge a b := by
    intro a b
    dsimp [edge]
    by_cases hab : a < b
    · simp [hab, hw a b]
    · by_cases hba : b < a
      · simp [hab, hba, hw b a]
      · simp [hab, hba]
  have hedge_diag : edge i i = 0 := by
    simp [edge]
  have hedge_symm : ∀ a b : Fin k, edge a b = edge b a := by
    intro a b
    dsimp [edge]
    by_cases hab : a < b
    · have hnot_ba : ¬ b < a := not_lt.mpr (le_of_lt hab)
      simp [hab, hnot_ba]
    · by_cases hba : b < a
      · have hnot_ab : ¬ a < b := not_lt.mpr (le_of_lt hba)
        simp [hba, hnot_ab]
      · simp [hab, hba]
  have hothers_nonempty : Nonempty others := by
    have hfin_card : 1 < Fintype.card (Fin k) := by
      simpa [Fintype.card_fin] using (by omega : 1 < k)
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hfin_card i
    exact ⟨⟨j, hji⟩⟩
  have hothers_card_pos : 0 < Fintype.card others :=
    Fintype.card_pos_iff.mpr hothers_nonempty
  have hcard_others : Fintype.card others = k - 1 := by
    rw [Fintype.card_subtype]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k))) (p := fun j => j = i)
    have hsingleton :
        ((Finset.univ : Finset (Fin k)).filter (fun j => j = i)).card = 1 := by
      exact Finset.card_eq_one.mpr ⟨i, by ext j; simp⟩
    have hnot :
        ((Finset.univ : Finset (Fin k)).filter (fun j => ¬ j = i)).card = k - 1 := by
      have :
          ((Finset.univ : Finset (Fin k)).filter (fun j => ¬ j = i)).card + 1 = k := by
        rw [← hsingleton, add_comm]
        simpa [Fintype.card_fin] using hsplit
      omega
    simp [hnot]
  let nonincident : Finset (Fin k × Fin k) :=
    pairs.filter (fun p => p.1 ≠ i ∧ p.2 ≠ i)
  let incident : Finset (Fin k × Fin k) :=
    pairs.filter (fun p => p.1 = i ∨ p.2 = i)
  have hB_sub :
      pairsOther.sum (fun p => edge p.1.1 p.2.1) =
        nonincident.sum (fun p => edge p.1 p.2) := by
    refine Finset.sum_bij' (fun p _hp => (p.1.1, p.2.1))
      (fun p hp => (⟨p.1, by
        simp [nonincident, pairs] at hp
        exact hp.2.1⟩, ⟨p.2, by
        simp [nonincident, pairs] at hp
        exact hp.2.2⟩)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp [pairsOther, nonincident, pairs] at hp ⊢
      exact ⟨hp, p.1.2, p.2.2⟩
    · intro p hp
      simp [pairsOther, nonincident, pairs] at hp ⊢
      exact hp.1
    · intro p hp
      ext <;> rfl
    · intro p hp
      rfl
    · intro p hp
      rfl
  have hI_sub :
      (∑ j : Fin k, edge i j) = incident.sum (fun p => edge p.1 p.2) := by
    have hsum_ne :
        (∑ j : Fin k, edge i j) =
          ∑ j : {j : Fin k // j ≠ i}, edge i j.1 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => edge i j) i]
      rw [hedge_diag]
      ring
    rw [hsum_ne]
    refine Finset.sum_bij'
      (fun j _hj => if hij : i < j.1 then (i, j.1) else (j.1, i))
      (fun p hp =>
        if hp1 : p.1 = i then
          ⟨p.2, by
            simp [incident, pairs] at hp
            intro hp2
            exact (ne_of_lt hp.1) (by rw [hp1, hp2])
          ⟩
        else
          ⟨p.1, by
            simp [incident, pairs] at hp
            intro hp1i
            exact hp1 hp1i
          ⟩) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      by_cases hij : i < j.1
      · simp [incident, pairs, hij]
      · have hji : j.1 < i := lt_of_le_of_ne (le_of_not_gt hij) j.2
        simp [incident, pairs, hij, hji]
    · intro p hp
      simp [incident, pairs] at hp ⊢
    · intro j hj
      by_cases hij : i < j.1
      · simp [hij]
      · have _hji : j.1 < i := lt_of_le_of_ne (le_of_not_gt hij) j.2
        simp [hij]
        intro h
        exact False.elim (j.2 h)
    · intro p hp
      simp [incident, pairs] at hp ⊢
      rcases hp.2 with hp1 | hp2
      · subst hp1
        simp [hp.1]
      · subst hp2
        have hp1ne : ¬ p.1 = p.2 := ne_of_lt hp.1
        have hnlt : ¬ p.2 < p.1 := not_lt.mpr (le_of_lt hp.1)
        simp [hp1ne, hnlt]
    · intro j hj
      by_cases hij : i < j.1
      · simp [hij]
      · have _hji : j.1 < i := lt_of_le_of_ne (le_of_not_gt hij) j.2
        simp [hij]
        exact hedge_symm i j.1
  have htotal_split :
      nonincident.sum (fun p => edge p.1 p.2) +
          incident.sum (fun p => edge p.1 p.2) =
        pairs.sum (fun p => edge p.1 p.2) := by
    have hsplit0 := Finset.sum_filter_add_sum_filter_not
      (s := pairs) (p := fun p : Fin k × Fin k => p.1 ≠ i ∧ p.2 ≠ i)
      (f := fun p => edge p.1 p.2)
    have hcomp_eq :
        (∑ x ∈ pairs.filter
              (fun p : Fin k × Fin k => ¬ (p.1 ≠ i ∧ p.2 ≠ i)),
            edge x.1 x.2) =
          incident.sum (fun p => edge p.1 p.2) := by
      apply Finset.sum_congr
      · apply Finset.ext
        intro p
        simp [incident]
        intro _hp_mem
        constructor
        · intro hnot
          by_cases hp1 : p.1 = i
          · exact Or.inl hp1
          · exact Or.inr (hnot hp1)
        · intro h hp1ne
          rcases h with hp1 | hp2
          · exact False.elim (hp1ne hp1)
          · exact hp2
      · intro p hp
        rfl
    rw [hcomp_eq] at hsplit0
    simpa [nonincident] using hsplit0
  have hB_eq : pairsOther.sum (fun p => edge p.1.1 p.2.1) = M - Mi := by
    have hadd : pairsOther.sum (fun p => edge p.1.1 p.2.1) + Mi = M := by
      dsimp [M, Mi]
      rw [hB_sub, hI_sub]
      exact htotal_split
    linarith
  have hred :=
    (KPartiteFixedVertexReducedEstimate
      (u := fun j : others => edge i j.1)
      (v := fun a b : others => edge a.1 b.1)
      (by intro j; exact hedge_nonneg i j.1)
      (by intro a b; exact hedge_nonneg a.1 b.1)
      hothers_card_pos)
  have hMi_sub : (∑ a : others, edge i a.1) = Mi := by
    dsimp [Mi]
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => edge i j) i]
    rw [hedge_diag]
    ring
  have hcoef :
      (((Fintype.card others : ℝ) - 1) / (2 * (Fintype.card others : ℝ))) =
      (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) := by
    rw [hcard_others]
    norm_num [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
    ring
  calc
    pairsOther.sum
          (fun p => Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))
        ≤ Mi * Real.sqrt
          (((((Fintype.card others : ℝ) - 1) / (2 * (Fintype.card others : ℝ))) *
              pairsOther.sum (fun p => edge p.1.1 p.2.1))) := by
            simpa [pairsOther, hMi_sub] using hred
    _ = Mi * Real.sqrt
          ((((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * (M - Mi)) := by
          rw [hcoef, hB_eq]
