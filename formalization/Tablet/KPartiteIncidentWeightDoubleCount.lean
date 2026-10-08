import Tablet.Preamble

-- [TABLET NODE: KPartiteIncidentWeightDoubleCount]
theorem KPartiteIncidentWeightDoubleCount :
    ∀ k : ℕ, ∀ w : Fin k → Fin k → ℝ,
      (∑ i : Fin k, ∑ j : Fin k,
          if i < j then w i j else if j < i then w j i else 0) =
        2 * (((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun p => p.1 < p.2)).sum (fun p => w p.1 p.2)) := by
-- BODY
  intro k w
  classical
  let pairs : Finset (Fin k × Fin k) :=
    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
  have hsplit :
      (∑ i : Fin k, ∑ j : Fin k,
          if i < j then w i j else if j < i then w j i else 0) =
        (∑ i : Fin k, ∑ j : Fin k, if i < j then w i j else 0) +
        (∑ i : Fin k, ∑ j : Fin k, if j < i then w j i else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hij : i < j
    · have hnji : ¬ j < i := not_lt.mpr (le_of_lt hij)
      simp [hij, hnji]
    · by_cases hji : j < i
      · simp [hij, hji]
      · simp [hij, hji]
  have hfirst :
      (∑ i : Fin k, ∑ j : Fin k, if i < j then w i j else 0) =
        pairs.sum (fun p => w p.1 p.2) := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, if i < j then w i j else 0)
          = ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
              if p.1 < p.2 then w p.1 p.2 else 0 := by
              simpa using
                (Finset.sum_product' (Finset.univ : Finset (Fin k))
                  (Finset.univ : Finset (Fin k))
                  (fun i j : Fin k => if i < j then w i j else 0)).symm
      _ = pairs.sum (fun p => w p.1 p.2) := by
              simpa [pairs] using
                (Finset.sum_filter (s := (Finset.univ : Finset (Fin k × Fin k)))
                  (p := fun p : Fin k × Fin k => p.1 < p.2)
                  (f := fun p : Fin k × Fin k => w p.1 p.2)).symm
  have hsecond :
      (∑ i : Fin k, ∑ j : Fin k, if j < i then w j i else 0) =
        pairs.sum (fun p => w p.1 p.2) := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, if j < i then w j i else 0)
          = ∑ j : Fin k, ∑ i : Fin k, if j < i then w j i else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ p ∈ (Finset.univ : Finset (Fin k × Fin k)),
              if p.1 < p.2 then w p.1 p.2 else 0 := by
              simpa using
                (Finset.sum_product' (Finset.univ : Finset (Fin k))
                  (Finset.univ : Finset (Fin k))
                  (fun j i : Fin k => if j < i then w j i else 0)).symm
      _ = pairs.sum (fun p => w p.1 p.2) := by
              simpa [pairs] using
                (Finset.sum_filter (s := (Finset.univ : Finset (Fin k × Fin k)))
                  (p := fun p : Fin k × Fin k => p.1 < p.2)
                  (f := fun p : Fin k × Fin k => w p.1 p.2)).symm
  rw [hsplit, hfirst, hsecond]
  ring
