import Tablet.Preamble
import Mathlib.Algebra.Order.Chebyshev

-- [TABLET NODE: KPartitePairProductCauchyBound]
theorem KPartitePairProductCauchyBound :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι],
      ∀ u : ι → ℝ,
        0 < Fintype.card ι →
        (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
            u p.1 * u p.2) ≤
          (((Fintype.card ι : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) *
            (∑ a : ι, u a) ^ 2 := by
-- BODY
  intro ι _ _ _ u hcard
  classical
  let pairSum : ℝ :=
    (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        u p.1 * u p.2)
  let sumsq : ℝ := ∑ a : ι, u a ^ 2
  let S : ℝ := ∑ a : ι, u a
  have hprod :
      S ^ 2 = ∑ p : ι × ι, u p.1 * u p.2 := by
    dsimp [S]
    rw [sq]
    rw [Finset.sum_mul_sum]
    exact (Finset.sum_product' (Finset.univ : Finset ι) (Finset.univ : Finset ι)
      (fun a b => u a * u b)).symm
  have hdiag :
      (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 = p.2),
          u p.1 * u p.2) = sumsq := by
    dsimp [sumsq]
    calc
      (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 = p.2),
          u p.1 * u p.2)
          = ∑ a : ι, u a * u a := by
              refine Finset.sum_bij' (fun p _hp => p.1) (fun a _ha => (a, a)) ?_ ?_ ?_ ?_ ?_
              · intro p hp
                simp at hp ⊢
              · intro a ha
                simp
              · intro p hp
                simp at hp
                rcases p with ⟨a, b⟩
                simp at hp ⊢
                exact hp
              · intro p hp
                rfl
              · intro a ha
                rcases a with ⟨a, b⟩
                simp at ha ⊢
                subst b
                simp
      _ = ∑ a : ι, u a ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
  have hoff :
      (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2),
          u p.1 * u p.2) = 2 * pairSum := by
    dsimp [pairSum]
    let ltPairs : Finset (ι × ι) :=
      (Finset.univ.filter (fun p : ι × ι => p.1 < p.2))
    let gtPairs : Finset (ι × ι) :=
      (Finset.univ.filter (fun p : ι × ι => p.2 < p.1))
    have hsplit :
        (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2),
            u p.1 * u p.2) =
          (∑ p ∈ ltPairs, u p.1 * u p.2) +
            (∑ p ∈ gtPairs, u p.1 * u p.2) := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2))
        (p := fun p => p.1 < p.2)
        (f := fun p => u p.1 * u p.2)]
      congr 1
      · refine Finset.sum_congr ?_ ?_
        · apply Finset.ext
          intro p
          simp [ltPairs]
          exact fun h => ne_of_lt h
        · intro p hp
          rfl
      · refine Finset.sum_congr ?_ ?_
        · apply Finset.ext
          intro p
          simp [gtPairs]
          constructor
          · intro h
            exact lt_of_le_of_ne h.2 (Ne.symm h.1)
          · intro h
            exact ⟨ne_of_gt h, le_of_lt h⟩
        · intro p hp
          rfl
    have hgt :
        (∑ p ∈ gtPairs, u p.1 * u p.2) =
          (∑ p ∈ ltPairs, u p.1 * u p.2) := by
      refine Finset.sum_bij' (fun p _hp => (p.2, p.1)) (fun p _hp => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp [gtPairs, ltPairs] at hp ⊢
        exact hp
      · intro p hp
        simp [gtPairs, ltPairs] at hp ⊢
        exact hp
      · intro p hp
        rfl
      · intro p hp
        rfl
      · intro p hp
        rw [mul_comm]
    rw [hsplit, hgt]
    ring
  have hsplit_total :
      (∑ p : ι × ι, u p.1 * u p.2) = sumsq + 2 * pairSum := by
    calc
      (∑ p : ι × ι, u p.1 * u p.2)
          =
        (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 = p.2),
          u p.1 * u p.2) +
        (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter (fun p => p.1 ≠ p.2),
          u p.1 * u p.2) := by
            rw [← Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset (ι × ι)))
              (p := fun p => p.1 = p.2)
              (f := fun p => u p.1 * u p.2)]
      _ = sumsq + 2 * pairSum := by
            rw [hdiag, hoff]
  have hS_expand : S ^ 2 = sumsq + 2 * pairSum := by
    rw [hprod, hsplit_total]
  have hcs :
      S ^ 2 ≤ (Fintype.card ι : ℝ) * sumsq := by
    dsimp [S, sumsq]
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := u))
  have hcard_real_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast hcard
  have hsumsq_ge : S ^ 2 / (Fintype.card ι : ℝ) ≤ sumsq := by
    exact (div_le_iff₀ hcard_real_pos).mpr (by simpa [mul_comm] using hcs)
  have htwo_pair_le :
      2 * pairSum ≤ S ^ 2 - S ^ 2 / (Fintype.card ι : ℝ) := by
    nlinarith [hS_expand, hsumsq_ge]
  have hcoef :
      S ^ 2 - S ^ 2 / (Fintype.card ι : ℝ) =
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) * S ^ 2 := by
    field_simp [ne_of_gt hcard_real_pos]
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hpair_le :
      pairSum ≤
        ((((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) * S ^ 2) / 2 := by
    rw [← hcoef]
    exact (le_div_iff₀ htwo_pos).mpr (by simpa [mul_comm] using htwo_pair_le)
  dsimp [pairSum, S] at hpair_le ⊢
  convert hpair_le using 1
  ring
