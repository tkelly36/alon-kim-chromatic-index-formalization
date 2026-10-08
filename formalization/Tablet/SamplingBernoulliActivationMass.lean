import Tablet.RandomIndependentSetSampling

open BigOperators

universe u

-- [TABLET NODE: SamplingBernoulliActivationMass]
theorem SamplingBernoulliActivationMass :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ Delta : ℕ, ∀ gamma : ℝ,
        0 < gamma → gamma ≤ (Delta : ℝ) →
          (∀ A : Finset V,
            0 ≤
              (gamma / (Delta : ℝ)) ^ A.card *
                (1 - gamma / (Delta : ℝ)) ^
                  ((Finset.univ : Finset V).card - A.card)) ∧
          (∑ A : Finset V,
            (gamma / (Delta : ℝ)) ^ A.card *
              (1 - gamma / (Delta : ℝ)) ^
                ((Finset.univ : Finset V).card - A.card)) = 1 := by
-- BODY
  intro V _ _ Delta gamma hgamma hle
  let q : ℝ := gamma / (Delta : ℝ)
  have hDelta_pos : 0 < (Delta : ℝ) := lt_of_lt_of_le hgamma hle
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg (le_of_lt hgamma) (le_of_lt hDelta_pos)
  have hq_le_one : q ≤ 1 := by
    exact (div_le_one hDelta_pos).mpr hle
  have hone_minus_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq_le_one
  constructor
  · intro A
    exact mul_nonneg (pow_nonneg hq_nonneg A.card)
      (pow_nonneg hone_minus_nonneg ((Finset.univ : Finset V).card - A.card))
  · let s : Finset V := Finset.univ
    have huniv_powerset : (Finset.univ : Finset (Finset V)) = s.powerset := by
      ext A
      simp [s]
    have hsum_powerset :
        (∑ A ∈ s.powerset, q ^ A.card * (1 - q) ^ (s.card - A.card)) =
          (q + (1 - q)) ^ s.card := by
      simpa using
        (Finset.sum_pow_mul_eq_add_pow (s := s) (a := q) (b := 1 - q))
    calc
      (∑ A : Finset V,
          (gamma / (Delta : ℝ)) ^ A.card *
            (1 - gamma / (Delta : ℝ)) ^
              ((Finset.univ : Finset V).card - A.card))
          = ∑ A ∈ s.powerset, q ^ A.card * (1 - q) ^ (s.card - A.card) := by
            rw [← huniv_powerset]
      _ = (q + (1 - q)) ^ s.card := hsum_powerset
      _ = 1 := by
            ring_nf
