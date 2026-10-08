import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingFiniteMassSubcellNormalization]
theorem SamplingFiniteMassSubcellNormalization
    {σ : Type u}
    [MeasurableSpace σ] (ν : MeasureTheory.Measure σ) (w : ℝ) (cell E : Set σ)
    (hw_nonneg : 0 ≤ w)
    (hcell : ENNReal.ofReal w = ν cell)
    (hsubset : E ⊆ cell) :
    ∃ p : ℝ, 0 ≤ p ∧ (w = 0 → p = 0) ∧ ENNReal.ofReal (w * p) = ν E := by
-- BODY
  by_cases hwz : w = 0
  · refine ⟨0, le_refl 0, (fun _ => rfl), ?_⟩
    have hcell_zero : ν cell = 0 := by
      simpa [hwz] using hcell.symm
    have hE_zero : ν E = 0 := by
      have hle : ν E ≤ ν cell := measure_mono hsubset
      rw [hcell_zero] at hle
      exact le_antisymm hle (zero_le _)
    simp [hE_zero]
  · have hwpos : 0 < w := lt_of_le_of_ne hw_nonneg (Ne.symm hwz)
    have hfinite_E : ν E ≠ ⊤ := by
      have hle : ν E ≤ ν cell := measure_mono hsubset
      rw [← hcell] at hle
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    let p : ℝ := (ν E).toReal / w
    refine ⟨p, ?_, ?_, ?_⟩
    · dsimp [p]
      exact div_nonneg ENNReal.toReal_nonneg hw_nonneg
    · intro h
      exact (hwz h).elim
    · have hmul : w * p = (ν E).toReal := by
        dsimp [p]
        field_simp [ne_of_gt hwpos]
      rw [hmul]
      exact ENNReal.ofReal_toReal hfinite_E
