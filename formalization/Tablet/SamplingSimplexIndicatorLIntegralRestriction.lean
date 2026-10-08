import Tablet.RandomIndependentSetSampling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option maxHeartbeats 800000

open BigOperators

-- [TABLET NODE: SamplingSimplexIndicatorLIntegralRestriction]
theorem SamplingSimplexIndicatorLIntegralRestriction
    (g : ℝ → ℝ → ℝ → ℝ)
    (hg_cont : Continuous fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
      {p : ℝ × ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
            p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
        (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z)) =
      ∫⁻ z in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Set.Ioc (0 : ℝ) z,
        ∫⁻ x in Set.Ioc (0 : ℝ) y, ENNReal.ofReal (g x y z) := by
-- BODY
  let S : Set (ℝ × ℝ × ℝ) :=
    {p : ℝ × ℝ × ℝ |
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
        p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}
  let F : ℝ × ℝ × ℝ → ENNReal :=
    fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)
  have hmeasF : Measurable F := by
    dsimp [F]
    exact ENNReal.measurable_ofReal.comp hg_cont.measurable
  have hmeasS : MeasurableSet S := by
    dsimp [S]
    measurability
  rw [show {p : ℝ × ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
            p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1} = S from rfl]
  rw [show (fun p : ℝ × ℝ × ℝ => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) = F from rfl]
  have hswap_all :
      (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, S.indicator F (x, y, z)) =
        ∫⁻ z : ℝ, ∫⁻ y : ℝ, ∫⁻ x : ℝ, S.indicator F (x, y, z) := by
    have hswap_yz :
        ∀ x : ℝ,
          (∫⁻ y : ℝ, ∫⁻ z : ℝ, S.indicator F (x, y, z)) =
            ∫⁻ z : ℝ, ∫⁻ y : ℝ, S.indicator F (x, y, z) := by
      intro x
      exact MeasureTheory.lintegral_lintegral_swap (by measurability)
    simp_rw [hswap_yz]
    rw [MeasureTheory.lintegral_lintegral_swap]
    · have hswap_xy :
          ∀ z : ℝ,
            (∫⁻ x : ℝ, ∫⁻ y : ℝ, S.indicator F (x, y, z)) =
              ∫⁻ y : ℝ, ∫⁻ x : ℝ, S.indicator F (x, y, z) := by
        intro z
        exact MeasureTheory.lintegral_lintegral_swap (by measurability)
      simp_rw [hswap_xy]
    · measurability
  rw [hswap_all]
  have hinner :
      ∀ z y : ℝ,
        (∫⁻ x : ℝ, S.indicator F (x, y, z)) =
          (Set.Icc (0 : ℝ) 1).indicator
            (fun z : ℝ =>
              (Set.Icc (0 : ℝ) z).indicator
                (fun y : ℝ => ∫⁻ x in Set.Icc (0 : ℝ) y, ENNReal.ofReal (g x y z)) y) z := by
    intro z y
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · by_cases hy : y ∈ Set.Icc (0 : ℝ) z
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hy]
        rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
        apply MeasureTheory.lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          by_cases hx : x ∈ Set.Icc (0 : ℝ) y
          · rw [Set.indicator_of_mem hx]
            have hsx : (x, y, z) ∈ S := by
              rcases hx with ⟨hx0, hxy⟩
              rcases hy with ⟨_hy0, hyz⟩
              exact ⟨⟨hx0, le_trans hxy (le_trans hyz hz.2)⟩, hxy, hyz, hz⟩
            change S.indicator F (x, y, z) = ENNReal.ofReal (g x y z)
            rw [Set.indicator_of_mem hsx]
          · rw [Set.indicator_of_notMem hx]
            have hsx : (x, y, z) ∉ S := by
              intro hs
              exact hx ⟨hs.1.1, hs.2.1⟩
            change S.indicator F (x, y, z) = 0
            rw [Set.indicator_of_notMem hsx])
      · rw [Set.indicator_of_mem hz, Set.indicator_of_notMem hy]
        simpa using (MeasureTheory.lintegral_congr_ae
          (Filter.Eventually.of_forall (fun x => by
            have hsx : (x, y, z) ∉ S := by
              intro hs
              exact hy ⟨le_trans hs.1.1 hs.2.1, hs.2.2.1⟩
            change S.indicator F (x, y, z) = 0
            rw [Set.indicator_of_notMem hsx]) :
              (fun x : ℝ => S.indicator F (x, y, z)) =ᵐ[MeasureTheory.volume]
                fun _ : ℝ => (0 : ENNReal)))
    · rw [Set.indicator_of_notMem hz]
      simpa using (MeasureTheory.lintegral_congr_ae
        (Filter.Eventually.of_forall (fun x => by
          have hsx : (x, y, z) ∉ S := by
            intro hs
            exact hz hs.2.2.2
          change S.indicator F (x, y, z) = 0
          rw [Set.indicator_of_notMem hsx]) :
            (fun x : ℝ => S.indicator F (x, y, z)) =ᵐ[MeasureTheory.volume]
              fun _ : ℝ => (0 : ENNReal)))
  have houter :
      ∀ z : ℝ,
        (∫⁻ y : ℝ, ∫⁻ x : ℝ, S.indicator F (x, y, z)) =
          (Set.Icc (0 : ℝ) 1).indicator
            (fun z : ℝ =>
              ∫⁻ y in Set.Icc (0 : ℝ) z,
                ∫⁻ x in Set.Icc (0 : ℝ) y, ENNReal.ofReal (g x y z)) z := by
    intro z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hz]
      simp_rw [hinner z, Set.indicator_of_mem hz]
      rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
    · rw [Set.indicator_of_notMem hz]
      simp_rw [hinner z, Set.indicator_of_notMem hz]
      simp
  simp_rw [houter]
  rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
  intro z _hz
  change (∫⁻ y in Set.Icc (0 : ℝ) z,
      ∫⁻ x in Set.Icc (0 : ℝ) y, ENNReal.ofReal (g x y z)) =
    ∫⁻ y in Set.Ioc (0 : ℝ) z,
      ∫⁻ x in Set.Ioc (0 : ℝ) y, ENNReal.ofReal (g x y z)
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
  intro y _hy
  change (∫⁻ x in Set.Icc (0 : ℝ) y, ENNReal.ofReal (g x y z)) =
    ∫⁻ x in Set.Ioc (0 : ℝ) y, ENNReal.ofReal (g x y z)
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
