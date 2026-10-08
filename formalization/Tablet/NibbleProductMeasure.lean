import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

-- [TABLET NODE: NibbleProductMeasure]
noncomputable def NibbleProductMeasure {T : Type*} [Fintype T] (p : ℝ) :
    Measure (T → ℝ × ℝ) :=
-- BODY
  Measure.pi fun _ : T =>
    (ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))
