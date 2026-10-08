import Tablet.RandomIndependentSetSampling
import Tablet.SamplingSimplexENNRealIteratedIntegralBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingMeasurePreservingTripleSliceIntegralBound]
theorem SamplingMeasurePreservingTripleSliceIntegralBound
    {X W : Type*} [MeasureTheory.MeasureSpace X] [MeasureTheory.MeasureSpace W]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure W)]
    (Φ : X → ℝ × ℝ × ℝ × W)
    (E : Set X)
    (A : Set (ℝ × ℝ × ℝ × W))
    (g : ℝ → ℝ → ℝ → ℝ)
    (hΦ : MeasureTheory.MeasurePreserving Φ MeasureTheory.volume MeasureTheory.volume)
    (hA_meas : MeasurableSet A)
    (hg_cont : Continuous fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (hg_nonneg :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 → 0 ≤ g x y z)
    (hE :
      E ⊆ Φ ⁻¹' A)
    (hA_simplex :
      A ⊆
        {p : ℝ × ℝ × ℝ × W |
          p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
            p.2.1 ≤ p.2.2.1 ∧ p.2.2.1 ∈ Set.Icc (0 : ℝ) 1})
    (hslice :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 →
          MeasureTheory.volume
              {w : W | (x, y, z, w) ∈ A} ≤
            ENNReal.ofReal (g x y z)) :
    MeasureTheory.volume E ≤
      ENNReal.ofReal
        (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
-- BODY
  have hEA : MeasureTheory.volume E ≤ MeasureTheory.volume A := by
    calc
      MeasureTheory.volume E ≤ MeasureTheory.volume (Φ ⁻¹' A) := MeasureTheory.measure_mono hE
      _ = MeasureTheory.volume A := hΦ.measure_preimage hA_meas.nullMeasurableSet
  have hsections :
      MeasureTheory.volume A =
        ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
          MeasureTheory.volume {w : W | (x, y, z, w) ∈ A} := by
    have h1 :
        MeasureTheory.volume A =
          ∫⁻ x : ℝ, MeasureTheory.volume {r : ℝ × ℝ × W | (x, r) ∈ A} := by
      exact MeasureTheory.Measure.prod_apply hA_meas
    rw [h1]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with x
    let B : Set (ℝ × ℝ × W) := {r | (x, r) ∈ A}
    have hB : MeasurableSet B := measurable_prodMk_left hA_meas
    rw [show MeasureTheory.volume {r : ℝ × ℝ × W | (x, r) ∈ A} =
        MeasureTheory.volume B by rfl]
    have h2 :
        MeasureTheory.volume B =
          ∫⁻ y : ℝ, MeasureTheory.volume {r : ℝ × W | (y, r) ∈ B} := by
      exact MeasureTheory.Measure.prod_apply hB
    rw [h2]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with y
    let C : Set (ℝ × W) := {r | (y, r) ∈ B}
    have hC : MeasurableSet C := measurable_prodMk_left hB
    rw [show MeasureTheory.volume {r : ℝ × W | (y, r) ∈ B} =
        MeasureTheory.volume C by rfl]
    have h3 :
        MeasureTheory.volume C =
          ∫⁻ z : ℝ, MeasureTheory.volume {w : W | (z, w) ∈ C} := by
      exact MeasureTheory.Measure.prod_apply hC
    rw [h3]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with z
    rfl
  have hA_bound :
      MeasureTheory.volume A ≤
        ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
          {p : ℝ × ℝ × ℝ |
              p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
                p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
            (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z) := by
    rw [hsections]
    apply MeasureTheory.lintegral_mono
    intro x
    apply MeasureTheory.lintegral_mono
    intro y
    apply MeasureTheory.lintegral_mono
    intro z
    by_cases hs : 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ 1
    · have hx01 : x ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨hs.1, le_trans hs.2.1 (le_trans hs.2.2.1 hs.2.2.2)⟩
      have hz01 : z ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans hs.1 (le_trans hs.2.1 hs.2.2.1), hs.2.2.2⟩
      have hmem :
          (x, y, z) ∈
            {p : ℝ × ℝ × ℝ |
              p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
                p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1} := by
        exact ⟨hx01, hs.2.1, hs.2.2.1, hz01⟩
      change
        MeasureTheory.volume {w : W | (x, y, z, w) ∈ A} ≤
          {p : ℝ × ℝ × ℝ |
              p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
                p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
            (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z)
      simpa [Set.indicator, hmem,
        show ((0 ≤ x ∧ x ≤ 1) ∧ x ≤ y ∧ y ≤ z ∧ 0 ≤ z ∧ z ≤ 1) from
          ⟨⟨hx01.1, hx01.2⟩, hs.2.1, hs.2.2.1, hz01.1, hz01.2⟩] using
        hslice x y z hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    · have hzero : {w : W | (x, y, z, w) ∈ A} = ∅ := by
        ext w
        constructor
        · intro hw
          have hp := hA_simplex hw
          simp only [Set.mem_setOf_eq, Set.mem_Icc] at hp
          exact False.elim (hs ⟨hp.1.1, hp.2.1, hp.2.2.1, hp.2.2.2.2⟩)
        · intro hw
          cases hw
      have hifnot : ¬ ((0 ≤ x ∧ x ≤ 1) ∧ x ≤ y ∧ y ≤ z ∧ 0 ≤ z ∧ z ≤ 1) := by
        intro hif
        exact hs ⟨hif.1.1, hif.2.1, hif.2.2.1, hif.2.2.2.2⟩
      change
        MeasureTheory.volume {w : W | (x, y, z, w) ∈ A} ≤
          {p : ℝ × ℝ × ℝ |
              p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2.1 ∧
                p.2.1 ≤ p.2.2 ∧ p.2.2 ∈ Set.Icc (0 : ℝ) 1}.indicator
            (fun p => ENNReal.ofReal (g p.1 p.2.1 p.2.2)) (x, y, z)
      rw [hzero, MeasureTheory.measure_empty]
      simp [Set.indicator, hifnot]
  exact hEA.trans (hA_bound.trans
    (SamplingSimplexENNRealIteratedIntegralBound g hg_cont hg_nonneg))
