import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingTripleChamberAffineIntegralIdentity]
theorem SamplingTripleChamberAffineIntegralIdentity
    {V : Type*} [Fintype V]
    (gamma : ℝ) (Sx Sy Sz : Finset V)
    (hgamma_pos : 0 < gamma) :
    (∫ z in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..z,
        ∫ x in (0 : ℝ)..y,
          x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) =
      (1 / gamma ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card := by
-- BODY
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have h_inner (y : ℝ) :
      ∫ x in y..gamma, (1 - x / gamma) ^ Sx.card =
        gamma * ∫ x in (0 : ℝ)..(1 - y / gamma), x ^ Sx.card := by
    have h := intervalIntegral.integral_comp_sub_div
      (f := fun x : ℝ => x ^ Sx.card) (a := y) (b := gamma)
      (c := gamma) hgamma_ne (d := (1 : ℝ))
    simpa [one_sub_div, sub_self, div_self hgamma_ne, sub_eq_add_neg, mul_comm, mul_left_comm,
      mul_assoc] using h
  have h_subst (F : ℝ → ℝ) (a : ℝ) :
      ∫ t in a..gamma, F (1 - t / gamma) =
        gamma * ∫ u in (0 : ℝ)..(1 - a / gamma), F u := by
    have h := intervalIntegral.integral_comp_sub_div
      (f := F) (a := a) (b := gamma) (c := gamma) hgamma_ne (d := (1 : ℝ))
    simpa [sub_self, div_self hgamma_ne, mul_comm, mul_left_comm, mul_assoc] using h
  have h_rhs :
      (∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card)
        =
        gamma ^ 3 *
          (∫ z in (0 : ℝ)..1,
            ∫ y in (0 : ℝ)..z,
              ∫ x in (0 : ℝ)..y,
                x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
    calc
      (∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card)
          =
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              gamma *
                ((1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card *
                    ∫ x in (0 : ℝ)..(1 - y / gamma), x ^ Sx.card) := by
        apply intervalIntegral.integral_congr
        intro z hz
        apply intervalIntegral.integral_congr
        intro y hy
        calc
          (∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card)
              =
              ∫ x in y..gamma,
                (1 - x / gamma) ^ Sx.card *
                  ((1 - y / gamma) ^ Sy.card *
                    (1 - z / gamma) ^ Sz.card) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
          _ =
              (∫ x in y..gamma, (1 - x / gamma) ^ Sx.card) *
                ((1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card) := by
            rw [intervalIntegral.integral_mul_const]
          _ =
              gamma *
                ((1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card *
                    ∫ x in (0 : ℝ)..(1 - y / gamma), x ^ Sx.card) := by
            rw [h_inner y]
            ring
      _ =
          ∫ z in (0 : ℝ)..gamma,
            gamma *
              (∫ y in (0 : ℝ)..(1 - z / gamma),
                gamma *
                  (y ^ Sy.card *
                    (1 - z / gamma) ^ Sz.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card)) := by
        apply intervalIntegral.integral_congr
        intro z hz
        have hy_subst := h_subst
          (F := fun y : ℝ =>
            gamma *
              (y ^ Sy.card *
                (1 - z / gamma) ^ Sz.card *
                  ∫ x in (0 : ℝ)..y, x ^ Sx.card)) z
        simpa [mul_assoc, mul_left_comm, mul_comm] using hy_subst
      _ =
          gamma *
            (∫ z in (0 : ℝ)..gamma,
              ∫ y in (0 : ℝ)..(1 - z / gamma),
                gamma *
                  (y ^ Sy.card *
                    (1 - z / gamma) ^ Sz.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card)) := by
        rw [intervalIntegral.integral_const_mul]
      _ =
          gamma *
            (gamma *
              (∫ z in (0 : ℝ)..1,
                z ^ Sz.card *
                  ∫ y in (0 : ℝ)..z,
                    gamma *
                      (y ^ Sy.card *
                        ∫ x in (0 : ℝ)..y, x ^ Sx.card))) := by
        congr 1
        have hz_subst := h_subst
          (F := fun z : ℝ =>
            ∫ y in (0 : ℝ)..z,
              gamma *
                (y ^ Sy.card *
                  z ^ Sz.card *
                    ∫ x in (0 : ℝ)..y, x ^ Sx.card)) (0 : ℝ)
        simpa [zero_div, sub_zero, mul_assoc, mul_left_comm, mul_comm] using hz_subst
      _ =
          gamma ^ 3 *
            (∫ z in (0 : ℝ)..1,
              ∫ y in (0 : ℝ)..z,
                ∫ x in (0 : ℝ)..y,
                  x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
        rw [show gamma * (gamma *
            (∫ z in (0 : ℝ)..1,
              z ^ Sz.card *
                ∫ y in (0 : ℝ)..z,
                  gamma *
                    (y ^ Sy.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card))) =
            gamma ^ 2 *
              (∫ z in (0 : ℝ)..1,
                z ^ Sz.card *
                  ∫ y in (0 : ℝ)..z,
                    gamma *
                      (y ^ Sy.card *
                        ∫ x in (0 : ℝ)..y, x ^ Sx.card)) by ring]
        rw [show gamma ^ 3 *
            (∫ z in (0 : ℝ)..1,
              ∫ y in (0 : ℝ)..z,
                ∫ x in (0 : ℝ)..y,
                  x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) =
            gamma ^ 2 *
              (gamma *
                (∫ z in (0 : ℝ)..1,
                  ∫ y in (0 : ℝ)..z,
                    ∫ x in (0 : ℝ)..y,
                      x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)) by ring]
        congr 1
        calc
          (∫ z in (0 : ℝ)..1,
            z ^ Sz.card *
              ∫ y in (0 : ℝ)..z,
                gamma *
                  (y ^ Sy.card *
                    ∫ x in (0 : ℝ)..y, x ^ Sx.card))
              =
              ∫ z in (0 : ℝ)..1,
                gamma *
                  (z ^ Sz.card *
                    ∫ y in (0 : ℝ)..z,
                      y ^ Sy.card *
                        ∫ x in (0 : ℝ)..y, x ^ Sx.card) := by
            apply intervalIntegral.integral_congr
            intro z hz
            calc
              z ^ Sz.card *
                  ∫ y in (0 : ℝ)..z,
                    gamma *
                      (y ^ Sy.card *
                        ∫ x in (0 : ℝ)..y, x ^ Sx.card)
                  =
                  z ^ Sz.card *
                    (gamma *
                      ∫ y in (0 : ℝ)..z,
                        y ^ Sy.card *
                          ∫ x in (0 : ℝ)..y, x ^ Sx.card) := by
                rw [intervalIntegral.integral_const_mul]
              _ =
                  gamma *
                    (z ^ Sz.card *
                      ∫ y in (0 : ℝ)..z,
                        y ^ Sy.card *
                          ∫ x in (0 : ℝ)..y, x ^ Sx.card) := by
                ring
          _ =
              gamma *
                (∫ z in (0 : ℝ)..1,
                  z ^ Sz.card *
                    ∫ y in (0 : ℝ)..z,
                      y ^ Sy.card *
                        ∫ x in (0 : ℝ)..y, x ^ Sx.card) := by
            rw [intervalIntegral.integral_const_mul]
          _ =
              gamma *
                (∫ z in (0 : ℝ)..1,
                  ∫ y in (0 : ℝ)..z,
                    ∫ x in (0 : ℝ)..y,
                      x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro z hz
            calc
              z ^ Sz.card *
                  ∫ y in (0 : ℝ)..z,
                    y ^ Sy.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card
                  =
                  ∫ y in (0 : ℝ)..z,
                    (y ^ Sy.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card) *
                      z ^ Sz.card := by
                rw [intervalIntegral.integral_mul_const]
                ring
              _ =
                  ∫ y in (0 : ℝ)..z,
                    ∫ x in (0 : ℝ)..y,
                      x ^ Sx.card * y ^ Sy.card * z ^ Sz.card := by
                apply intervalIntegral.integral_congr
                intro y hy
                calc
                  (y ^ Sy.card *
                      ∫ x in (0 : ℝ)..y, x ^ Sx.card) *
                      z ^ Sz.card
                      =
                      (∫ x in (0 : ℝ)..y, x ^ Sx.card) *
                        (y ^ Sy.card * z ^ Sz.card) := by
                    ring
                  _ =
                      ∫ x in (0 : ℝ)..y,
                        x ^ Sx.card * (y ^ Sy.card * z ^ Sz.card) := by
                    rw [intervalIntegral.integral_mul_const]
                  _ =
                      ∫ x in (0 : ℝ)..y,
                        x ^ Sx.card * y ^ Sy.card * z ^ Sz.card := by
                    apply intervalIntegral.integral_congr
                    intro x hx
                    ring
  calc
    (∫ z in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..z,
        ∫ x in (0 : ℝ)..y,
          x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)
        = (1 / gamma ^ 3) *
          (gamma ^ 3 *
            (∫ z in (0 : ℝ)..1,
              ∫ y in (0 : ℝ)..z,
                ∫ x in (0 : ℝ)..y,
                  x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)) := by
      field_simp [hgamma_ne]
    _ = (1 / gamma ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^ Sx.card *
                (1 - y / gamma) ^ Sy.card *
                  (1 - z / gamma) ^ Sz.card := by
      rw [h_rhs]
