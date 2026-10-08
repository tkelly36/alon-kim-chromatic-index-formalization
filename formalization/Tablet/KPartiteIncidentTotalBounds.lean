import Tablet.Preamble
import Tablet.KPartiteIncidentWeightDoubleCount

-- [TABLET NODE: KPartiteIncidentTotalBounds]
theorem KPartiteIncidentTotalBounds :
    ∀ k : ℕ, ∀ w : Fin k → Fin k → ℝ,
      (∀ a b, 0 ≤ w a b) →
      let edge : Fin k → Fin k → ℝ :=
        fun a b => if a < b then w a b else if b < a then w b a else 0
      let pairs : Finset (Fin k × Fin k) :=
        (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
      let M : ℝ := pairs.sum (fun p => edge p.1 p.2)
      (∀ i : Fin k, 0 ≤ ∑ j : Fin k, edge i j) ∧
        (∀ i : Fin k, (∑ j : Fin k, edge i j) ≤ M) ∧
          (∑ i : Fin k, ∑ j : Fin k, edge i j) = 2 * M := by
-- BODY
  intro k w hw edge pairs M
  classical
  have hedge_nonneg : ∀ a b : Fin k, 0 ≤ edge a b := by
    intro a b
    dsimp [edge]
    by_cases hab : a < b
    · simp [hab, hw a b]
    · by_cases hba : b < a
      · simp [hab, hba, hw b a]
      · simp [hab, hba]
  have hedge_diag : ∀ i : Fin k, edge i i = 0 := by
    intro i
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
  have hnonneg : ∀ i : Fin k, 0 ≤ ∑ j : Fin k, edge i j := by
    intro i
    exact Finset.sum_nonneg (by
      intro j hj
      exact hedge_nonneg i j)
  have hsum :
      (∑ i : Fin k, ∑ j : Fin k, edge i j) = 2 * M := by
    have hdc := KPartiteIncidentWeightDoubleCount k w
    have hpairs_edge :
        pairs.sum (fun p : Fin k × Fin k => edge p.1 p.2) =
          pairs.sum (fun p : Fin k × Fin k => w p.1 p.2) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      simp [pairs] at hp
      simp [edge, hp]
    dsimp [edge, M]
    rw [hpairs_edge]
    simpa [pairs] using hdc
  have hle : ∀ i : Fin k, (∑ j : Fin k, edge i j) ≤ M := by
    intro i
    let incident : Finset (Fin k × Fin k) :=
      pairs.filter (fun p : Fin k × Fin k => p.1 = i ∨ p.2 = i)
    have hI_sub :
        (∑ j : Fin k, edge i j) = incident.sum (fun p => edge p.1 p.2) := by
      have hsum_ne :
          (∑ j : Fin k, edge i j) =
            ∑ j : {j : Fin k // j ≠ i}, edge i j.1 := by
        rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => edge i j) i]
        rw [hedge_diag i]
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
    rw [hI_sub]
    dsimp [M]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro p hp
        simp [incident] at hp
        exact hp.1)
      (by
        intro p hp_pairs hp_not_incident
        exact hedge_nonneg p.1 p.2)
  exact ⟨hnonneg, hle, hsum⟩
