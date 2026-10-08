import Tablet.Preamble
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory BigOperators

-- [TABLET NODE: FiniteIndicatorCountExpectation]
theorem FiniteIndicatorCountExpectation {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (s : Finset ι) (P : ι → Ω → Prop)
    [∀ ω, DecidablePred fun i => P i ω]
    (hm : ∀ i ∈ s, MeasurableSet {ω | P i ω}) :
    Integrable (fun ω => ((s.filter fun i => P i ω).card : ℝ)) ν ∧
    (∫ ω, ((s.filter fun i => P i ω).card : ℝ) ∂ν) =
      ∑ i ∈ s, ν.real {ω | P i ω} := by
-- BODY
  classical
  have he : (fun ω => ((s.filter fun i => P i ω).card : ℝ)) =
      fun ω => ∑ i ∈ s, ({ω | P i ω} : Set Ω).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp [Set.indicator, Finset.sum_boole]
  have hi (i : ι) (hi : i ∈ s) :
      Integrable (({ω | P i ω} : Set Ω).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator (hm i hi)
  rw [he]
  refine ⟨integrable_finset_sum s hi, ?_⟩
  rw [integral_finset_sum s hi]
  exact Finset.sum_congr rfl (fun i hi => integral_indicator_one (hm i hi))
