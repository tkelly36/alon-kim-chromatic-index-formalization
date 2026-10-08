import Tablet.RandomIndependentSetSampling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingSimplexPartialIntegralRegularity]
theorem SamplingSimplexPartialIntegralRegularity
    (g : ℝ → ℝ → ℝ → ℝ)
    (hg_cont : Continuous fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (hg_nonneg :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 → 0 ≤ g x y z) :
    (∀ y z : ℝ,
        0 ≤ y → y ≤ z → z ≤ 1 →
          IntervalIntegrable (fun x : ℝ => g x y z) MeasureTheory.volume 0 y ∧
            ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) y → 0 ≤ g x y z) ∧
      (∀ z : ℝ,
        0 ≤ z → z ≤ 1 →
          ContinuousOn
              (fun y : ℝ => ∫ x in (0 : ℝ)..y, g x y z)
              (Set.Icc (0 : ℝ) z) ∧
            IntervalIntegrable
              (fun y : ℝ => ∫ x in (0 : ℝ)..y, g x y z)
              MeasureTheory.volume 0 z ∧
            ∀ y : ℝ, y ∈ Set.Ioc (0 : ℝ) z →
              0 ≤ ∫ x in (0 : ℝ)..y, g x y z) ∧
      (ContinuousOn
          (fun z : ℝ =>
            ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z)
          (Set.Icc (0 : ℝ) 1) ∧
        IntervalIntegrable
          (fun z : ℝ =>
            ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z)
          MeasureTheory.volume 0 1 ∧
        ∀ z : ℝ, z ∈ Set.Ioc (0 : ℝ) 1 →
          0 ≤ ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
-- BODY
  constructor
  · intro y z hy0 hyz hz1
    constructor
    · have hcontx : Continuous fun x : ℝ => g x y z := by
        fun_prop
      exact hcontx.intervalIntegrable (μ := MeasureTheory.volume) 0 y
    · intro x hx
      exact hg_nonneg x y z (le_of_lt hx.1) hx.2 hyz hz1
  constructor
  · intro z hz0 hz1
    have hFcont : Continuous fun y : ℝ => ∫ x in (0 : ℝ)..y, g x y z := by
      let f : ℝ → ℝ → ℝ := fun y x => g x y z
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := f) (a₀ := (0 : ℝ)) (s := fun y : ℝ => y)
        (by
          dsimp [f, Function.uncurry]
          fun_prop)
        (by fun_prop)
    constructor
    · exact hFcont.continuousOn
    constructor
    · exact hFcont.intervalIntegrable (μ := MeasureTheory.volume) 0 z
    · intro y hy
      refine intervalIntegral.integral_nonneg (le_of_lt hy.1) ?_
      intro x hx
      exact hg_nonneg x y z hx.1 hx.2 hy.2 hz1
  · have hFcont : Continuous fun yz : ℝ × ℝ => ∫ x in (0 : ℝ)..yz.1, g x yz.1 yz.2 := by
      let f : (ℝ × ℝ) → ℝ → ℝ := fun yz x => g x yz.1 yz.2
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := f) (a₀ := (0 : ℝ))
        (s := fun yz : ℝ × ℝ => yz.1)
        (by
          dsimp [f, Function.uncurry]
          fun_prop)
        (by fun_prop)
    have hGcont : Continuous fun z : ℝ =>
        ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z := by
      let f : ℝ → ℝ → ℝ := fun z y => ∫ x in (0 : ℝ)..y, g x y z
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (f := f) (a₀ := (0 : ℝ)) (s := fun z : ℝ => z)
        (by
          dsimp [f, Function.uncurry]
          fun_prop)
        (by fun_prop)
    constructor
    · exact hGcont.continuousOn
    constructor
    · exact hGcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
    · intro z hz
      refine intervalIntegral.integral_nonneg (le_of_lt hz.1) ?_
      intro y hy
      refine intervalIntegral.integral_nonneg hy.1 ?_
      intro x hx
      exact hg_nonneg x y z hx.1 hx.2 hy.2 hz.2
