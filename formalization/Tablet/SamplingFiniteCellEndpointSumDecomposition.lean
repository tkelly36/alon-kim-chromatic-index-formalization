import Tablet.Preamble

open BigOperators

universe u

-- [TABLET NODE: SamplingFiniteCellEndpointSumDecomposition]
theorem SamplingFiniteCellEndpointSumDecomposition :
    ∀ {α Ω : Type u} [MeasurableSpace α] [Fintype Ω],
      ∀ (ν : MeasureTheory.Measure α) (E support : Set α)
        (cell : Ω → Set α) (w P : Ω → ℝ),
        MeasurableSet E →
        (∀ ω : Ω, MeasurableSet (cell ω)) →
        (∀ ω : Ω, 0 ≤ w ω) →
        (∀ ω : Ω, 0 ≤ P ω) →
        (∀ ω : Ω, w ω = 0 → P ω = 0) →
        (∀ ω : Ω, ENNReal.ofReal (w ω * P ω) = ν (E ∩ cell ω)) →
        (∀ ω : Ω, cell ω ⊆ support) →
        (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) →
        E ∩ support = ⋃ ω : Ω, E ∩ cell ω →
        ν (E \ support) = 0 →
        ENNReal.ofReal (∑ ω : Ω, w ω * P ω) = ν E := by
-- BODY
  intro α Ω _ _ ν E support cell w P hE hcell hw hP _hzero hcell_mass
    hcell_subset hdisj hcover hnull
  have hpiece_meas : ∀ ω : Ω, MeasurableSet (E ∩ cell ω) := fun ω =>
    hE.inter (hcell ω)
  have hpiece_disj : Pairwise (fun ω₁ ω₂ : Ω => Disjoint (E ∩ cell ω₁) (E ∩ cell ω₂)) := by
    intro ω₁ ω₂ hne
    exact (hdisj ω₁ ω₂ hne).mono Set.inter_subset_right Set.inter_subset_right
  have hsum_nonneg : ∀ ω : Ω, 0 ≤ w ω * P ω := fun ω =>
    mul_nonneg (hw ω) (hP ω)
  have hUnion :
      ν (⋃ ω : Ω, E ∩ cell ω) = ∑' ω : Ω, ν (E ∩ cell ω) := by
    exact MeasureTheory.measure_iUnion hpiece_disj hpiece_meas
  have hfinite_sum :
      ν (E ∩ support) = ∑ ω : Ω, ν (E ∩ cell ω) := by
    rw [hcover, hUnion, tsum_fintype]
  have hreal_sum :
      ENNReal.ofReal (∑ ω : Ω, w ω * P ω) =
        ∑ ω : Ω, ENNReal.ofReal (w ω * P ω) := by
    simpa using
      (ENNReal.ofReal_sum_of_nonneg
        (s := (Finset.univ : Finset Ω)) (f := fun ω => w ω * P ω)
        (by simpa using fun ω (_hω : ω ∈ (Finset.univ : Finset Ω)) => hsum_nonneg ω))
  have hsum_cells :
      ENNReal.ofReal (∑ ω : Ω, w ω * P ω) =
        ν (E ∩ support) := by
    rw [hreal_sum, hfinite_sum]
    exact Finset.sum_congr rfl (fun ω _ => hcell_mass ω)
  have hsupport_mass : ν (E ∩ support) = ν E := by
    exact MeasureTheory.measure_inter_conull' (μ := ν) (s := E) (t := support) hnull
  exact hsum_cells.trans hsupport_mass
