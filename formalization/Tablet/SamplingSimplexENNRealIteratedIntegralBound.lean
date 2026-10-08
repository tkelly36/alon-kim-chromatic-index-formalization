import Tablet.RandomIndependentSetSampling
import Tablet.SamplingIntervalLIntegralOfRealConversion
import Tablet.SamplingSimplexIndicatorLIntegralRestriction
import Tablet.SamplingSimplexPartialIntegralRegularity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingSimplexENNRealIteratedIntegralBound]
theorem SamplingSimplexENNRealIteratedIntegralBound
    (g : ℝ → ℝ → ℝ → ℝ)
    (hg_cont : Continuous fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (hg_nonneg :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 → 0 ≤ g x y z) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
      {p : ℝ × ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
            p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
        (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z)) ≤
      ENNReal.ofReal
        (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
-- BODY
  have hreg := SamplingSimplexPartialIntegralRegularity g hg_cont hg_nonneg
  have hx_reg := hreg.1
  have hy_reg := hreg.2.1
  have hz_reg := hreg.2.2
  have h_eq :
      (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
        {p : ℝ × ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
              p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
          (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z)) =
        ENNReal.ofReal
          (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
    calc
      (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
        {p : ℝ × ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
              p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
          (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z))
          = ∫⁻ z in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Set.Ioc (0 : ℝ) z,
              ∫⁻ x in Set.Ioc (0 : ℝ) y, ENNReal.ofReal (g x y z) := by
            exact SamplingSimplexIndicatorLIntegralRestriction g hg_cont
      _ = ∫⁻ z in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Set.Ioc (0 : ℝ) z,
              ENNReal.ofReal (∫ x in (0 : ℝ)..y, g x y z) := by
            apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
            intro z hz
            apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
            intro y hy
            exact SamplingIntervalLIntegralOfRealConversion
              (fun x : ℝ => g x y z) (0 : ℝ) y (le_of_lt hy.1)
              (hx_reg y z (le_of_lt hy.1) hy.2 hz.2).1
              (hx_reg y z (le_of_lt hy.1) hy.2 hz.2).2
      _ = ∫⁻ z in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
            apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
            intro z hz
            exact SamplingIntervalLIntegralOfRealConversion
              (fun y : ℝ => ∫ x in (0 : ℝ)..y, g x y z) (0 : ℝ) z (le_of_lt hz.1)
              (hy_reg z (le_of_lt hz.1) hz.2).2.1
              (hy_reg z (le_of_lt hz.1) hz.2).2.2
      _ = ENNReal.ofReal
              (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z,
                ∫ x in (0 : ℝ)..y, g x y z) := by
            exact SamplingIntervalLIntegralOfRealConversion
              (fun z : ℝ => ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z)
              (0 : ℝ) 1 (by norm_num)
              hz_reg.2.1 hz_reg.2.2
  exact le_of_eq h_eq
