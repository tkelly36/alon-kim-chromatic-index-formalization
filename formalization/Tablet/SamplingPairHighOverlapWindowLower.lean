import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingPairHighOverlapWindowLower]
theorem SamplingPairHighOverlapWindowLower
    (Delta : ℕ) (L alpha : ℝ) (N : ℕ)
    (hD : 0 < (Delta : ℝ))
    (hL : 0 ≤ L)
    (hfirst :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) L →
        (1 - x / (Delta : ℝ)) ^ N ≥
          (1 - alpha) * Real.exp (-(alpha * L)))
    (hsecond :
      ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) L →
        (1 - y / (Delta : ℝ)) ^ Delta ≥
          (1 - alpha) * Real.exp (-y))
    (halpha_nonneg : 0 ≤ 1 - alpha)
    (hmargin :
      (5 / 3 + 2 * alpha) ≤
        2 *
          (∫ x in (0 : ℝ)..L,
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y)))) :
    (2 / (Delta : ℝ)^2) *
        (∫ x in (0 : ℝ)..L,
          ∫ y in x..L,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta) ≥
      (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 := by
-- BODY
  have hDsq_pos : 0 < (Delta : ℝ)^2 := sq_pos_of_pos hD
  have hfinite_int :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in x..L,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta)
        MeasureTheory.volume 0 L := by
    have hcont :
        Continuous
          (fun x : ℝ =>
            ∫ y in x..L,
              (1 - x / (Delta : ℝ)) ^ N *
                (1 - y / (Delta : ℝ)) ^ Delta) := by
      let F : ℝ → ℝ → ℝ := fun x y =>
        (1 - x / (Delta : ℝ)) ^ N *
          (1 - y / (Delta : ℝ)) ^ Delta
      have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
        dsimp [F]
        fun_prop
      have htop : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..L, F x y :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
          (s := fun _x : ℝ => L) hF (by fun_prop)
      have hbot : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..x, F x y :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
          (s := fun x : ℝ => x) hF (by fun_prop)
      have heq :
          (fun x : ℝ => ∫ y in x..L, F x y) =
            fun x : ℝ => (∫ y in (0 : ℝ)..L, F x y) -
              ∫ y in (0 : ℝ)..x, F x y := by
        ext x
        exact (intervalIntegral.integral_interval_sub_left
          ((by fun_prop : Continuous fun y : ℝ => F x y).intervalIntegrable 0 L)
          ((by fun_prop : Continuous fun y : ℝ => F x y).intervalIntegrable 0 x)).symm
      rw [show (fun x : ℝ =>
            ∫ y in x..L,
              (1 - x / (Delta : ℝ)) ^ N *
                (1 - y / (Delta : ℝ)) ^ Delta) =
          (fun x : ℝ => ∫ y in x..L, F x y) by rfl, heq]
      exact htop.sub hbot
    exact hcont.intervalIntegrable 0 L
  have hlower_int :
      IntervalIntegrable
        (fun x : ℝ =>
          ∫ y in x..L,
            ((1 - alpha) * Real.exp (-(alpha * L))) *
              ((1 - alpha) * Real.exp (-y)))
        MeasureTheory.volume 0 L := by
    have hcont :
        Continuous
          (fun x : ℝ =>
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y))) := by
      let F : ℝ → ℝ → ℝ := fun _x y =>
        ((1 - alpha) * Real.exp (-(alpha * L))) *
          ((1 - alpha) * Real.exp (-y))
      have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
        dsimp [F]
        fun_prop
      have htop : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..L, F x y :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
          (s := fun _x : ℝ => L) hF (by fun_prop)
      have hbot : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..x, F x y :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
          (s := fun x : ℝ => x) hF (by fun_prop)
      have heq :
          (fun x : ℝ => ∫ y in x..L, F x y) =
            fun x : ℝ => (∫ y in (0 : ℝ)..L, F x y) -
              ∫ y in (0 : ℝ)..x, F x y := by
        ext x
        exact (intervalIntegral.integral_interval_sub_left
          ((by fun_prop : Continuous fun y : ℝ => F x y).intervalIntegrable 0 L)
          ((by fun_prop : Continuous fun y : ℝ => F x y).intervalIntegrable 0 x)).symm
      rw [show (fun x : ℝ =>
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y))) =
          (fun x : ℝ => ∫ y in x..L, F x y) by rfl, heq]
      exact htop.sub hbot
    exact hcont.intervalIntegrable 0 L
  have hwindow :
      (∫ x in (0 : ℝ)..L,
          ∫ y in x..L,
            ((1 - alpha) * Real.exp (-(alpha * L))) *
              ((1 - alpha) * Real.exp (-y))) ≤
        (∫ x in (0 : ℝ)..L,
          ∫ y in x..L,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta) := by
    refine intervalIntegral.integral_mono_on hL hlower_int hfinite_int ?_
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) L := by simpa using hx
    have hinner_lower_int :
        IntervalIntegrable
          (fun y : ℝ =>
            ((1 - alpha) * Real.exp (-(alpha * L))) *
              ((1 - alpha) * Real.exp (-y)))
          MeasureTheory.volume x L := by
      exact ((by fun_prop : Continuous fun y : ℝ =>
        ((1 - alpha) * Real.exp (-(alpha * L))) *
          ((1 - alpha) * Real.exp (-y))).intervalIntegrable x L)
    have hinner_finite_int :
        IntervalIntegrable
          (fun y : ℝ =>
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta)
          MeasureTheory.volume x L := by
      exact ((by fun_prop : Continuous fun y : ℝ =>
        (1 - x / (Delta : ℝ)) ^ N *
          (1 - y / (Delta : ℝ)) ^ Delta).intervalIntegrable x L)
    refine intervalIntegral.integral_mono_on hx.2 hinner_lower_int hinner_finite_int ?_
    intro y hy
    have hyI : y ∈ Set.Icc (0 : ℝ) L := ⟨le_trans hx.1 hy.1, hy.2⟩
    have hA := hfirst x hxI
    have hB := hsecond y hyI
    have hC_nonneg : 0 ≤ (1 - alpha) * Real.exp (-(alpha * L)) := by
      exact mul_nonneg halpha_nonneg (Real.exp_pos _).le
    have hB_nonneg : 0 ≤ (1 - alpha) * Real.exp (-y) := by
      exact mul_nonneg halpha_nonneg (Real.exp_pos _).le
    exact mul_le_mul hA hB hB_nonneg (le_trans hC_nonneg hA)
  have hscaled :
      (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 ≤
        (2 / (Delta : ℝ)^2) *
          (∫ x in (0 : ℝ)..L,
            ∫ y in x..L,
              (1 - x / (Delta : ℝ)) ^ N *
                (1 - y / (Delta : ℝ)) ^ Delta) := by
    calc
      (5 / 3 + 2 * alpha) / (Delta : ℝ)^2
          ≤ (2 *
              (∫ x in (0 : ℝ)..L,
                ∫ y in x..L,
                  ((1 - alpha) * Real.exp (-(alpha * L))) *
                    ((1 - alpha) * Real.exp (-y)))) / (Delta : ℝ)^2 := by
            exact div_le_div_of_nonneg_right hmargin hDsq_pos.le
      _ ≤ (2 *
              (∫ x in (0 : ℝ)..L,
                ∫ y in x..L,
                  (1 - x / (Delta : ℝ)) ^ N *
                    (1 - y / (Delta : ℝ)) ^ Delta)) / (Delta : ℝ)^2 := by
            gcongr
      _ = (2 / (Delta : ℝ)^2) *
              (∫ x in (0 : ℝ)..L,
                ∫ y in x..L,
                  (1 - x / (Delta : ℝ)) ^ N *
                    (1 - y / (Delta : ℝ)) ^ Delta) := by
            ring
  exact hscaled
