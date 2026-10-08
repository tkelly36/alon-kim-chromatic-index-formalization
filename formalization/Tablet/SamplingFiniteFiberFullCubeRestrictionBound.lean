import Tablet.RandomIndependentSetSampling

-- [TABLET NODE: SamplingFiniteFiberFullCubeRestrictionBound]
theorem SamplingFiniteFiberFullCubeRestrictionBound
    {Ω : Type*}
    (ν : @MeasureTheory.Measure Ω ⊤)
    (F C E : Set Ω) (B : ENNReal)
    (hE_sub_F : E ⊆ F)
    (hfinite_F : ν F ≠ ⊤)
    (hfull : ν (F ∩ C) = ν F)
    (hcube_bound : ν (E ∩ C) ≤ B) :
    ν E ≤ B := by
-- BODY
  have hFC_sub_F : F ∩ C ⊆ F := by
    intro x hx
    exact hx.1
  have hFC_finite : ν (F ∩ C) ≠ ⊤ := by
    rw [hfull]
    exact hfinite_F
  have hdiff_eq : F \ (F ∩ C) = F \ C := by
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hFdiff_zero : ν (F \ C) = 0 := by
    have hdecomp := MeasureTheory.measure_diff hFC_sub_F (by measurability) hFC_finite
    rw [hfull] at hdecomp
    simpa [hdiff_eq] using hdecomp
  have hEdiff_zero : ν (E \ C) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hFdiff_zero
    intro x hx
    exact ⟨hE_sub_F hx.1, hx.2⟩
  have hE_le : ν E ≤ ν (E ∩ C) + ν (E \ C) := by
    calc
      ν E = ν ((E ∩ C) ∪ (E \ C)) := by
        congr 1
        ext x
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
        tauto
      _ ≤ ν (E ∩ C) + ν (E \ C) := MeasureTheory.measure_union_le _ _
  calc
    ν E ≤ ν (E ∩ C) + ν (E \ C) := hE_le
    _ = ν (E ∩ C) := by simp [hEdiff_zero]
    _ ≤ B := hcube_bound
