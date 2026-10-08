import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingNonadjacentPairOrderedPriorityAffineIntegral]
theorem SamplingNonadjacentPairOrderedPriorityAffineIntegral
    {V : Type*} [Fintype V]
    (Delta : ℕ) (gamma : ℝ) (S T : Finset V)
    (hgamma_pos : 0 < gamma) :
    (∫ a in (0 : ℝ)..1,
      ∫ b in (0 : ℝ)..a,
        (gamma / (Delta : ℝ)) ^ 2 * (a ^ S.card * b ^ T.card)) =
      ∫ x in (0 : ℝ)..gamma,
        ∫ y in x..gamma,
          (1 / gamma ^ 2) *
            ((gamma / (Delta : ℝ)) ^ 2 *
              ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)) := by
-- BODY
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  let c : ℝ := (gamma / (Delta : ℝ)) ^ 2
  have h_subst (F : ℝ → ℝ) (a : ℝ) :
      ∫ t in a..gamma, F (1 - t / gamma) =
        gamma * ∫ u in (0 : ℝ)..(1 - a / gamma), F u := by
    have h := intervalIntegral.integral_comp_sub_div
      (f := F) (a := a) (b := gamma) (c := gamma) hgamma_ne (d := (1 : ℝ))
    simpa [sub_self, div_self hgamma_ne, mul_comm, mul_left_comm, mul_assoc] using h
  have h_rhs :
      (∫ x in (0 : ℝ)..gamma,
        ∫ y in x..gamma,
          c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)) =
        gamma ^ 2 *
          (∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              c * (a ^ S.card * b ^ T.card)) := by
    calc
      (∫ x in (0 : ℝ)..gamma,
        ∫ y in x..gamma,
          c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card))
          =
          ∫ x in (0 : ℝ)..gamma,
            gamma *
              (c * ((1 - x / gamma) ^ S.card *
                ∫ b in (0 : ℝ)..(1 - x / gamma), b ^ T.card)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hy_subst := h_subst (F := fun b : ℝ =>
          c * ((1 - x / gamma) ^ S.card * b ^ T.card)) x
        simpa [mul_assoc, mul_left_comm, mul_comm] using hy_subst
      _ =
          gamma *
            (∫ x in (0 : ℝ)..gamma,
              c * ((1 - x / gamma) ^ S.card *
                ∫ b in (0 : ℝ)..(1 - x / gamma), b ^ T.card)) := by
        rw [intervalIntegral.integral_const_mul]
      _ =
          gamma *
            (gamma *
              (∫ a in (0 : ℝ)..1,
                ∫ b in (0 : ℝ)..a,
                  c * (a ^ S.card * b ^ T.card))) := by
        congr 1
        have hx_subst := h_subst (F := fun a : ℝ =>
          ∫ b in (0 : ℝ)..a, c * (a ^ S.card * b ^ T.card)) (0 : ℝ)
        simpa [zero_div, sub_zero, mul_assoc, mul_left_comm, mul_comm] using hx_subst
      _ =
          gamma ^ 2 *
            (∫ a in (0 : ℝ)..1,
              ∫ b in (0 : ℝ)..a,
                c * (a ^ S.card * b ^ T.card)) := by
        ring
  have hscaled :
      (1 / gamma ^ 2) *
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)) =
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            c * (a ^ S.card * b ^ T.card)) := by
    rw [h_rhs]
    field_simp [hgamma_ne]
  calc
    (∫ a in (0 : ℝ)..1,
      ∫ b in (0 : ℝ)..a,
        (gamma / (Delta : ℝ)) ^ 2 * (a ^ S.card * b ^ T.card))
        =
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            c * (a ^ S.card * b ^ T.card)) := by
      rfl
    _ =
        (1 / gamma ^ 2) *
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)) := by
      rw [hscaled]
    _ =
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / gamma ^ 2) *
              ((gamma / (Delta : ℝ)) ^ 2 *
                ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)) := by
      symm
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      change
        (∫ y in x..gamma,
          (1 / gamma ^ 2) *
            (c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card))) =
          (1 / gamma ^ 2) *
            ∫ y in x..gamma,
              c * ((1 - x / gamma) ^ S.card * (1 - y / gamma) ^ T.card)
      rw [intervalIntegral.integral_const_mul]
