import Tablet.SamplingSplitOutsideBlockerProductDecode
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerProductRealization]
structure SamplingSplitOutsideBlockerProductRealization
    {V V' : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] (p : ℝ) (φ : V → V') (S : Finset V)
    (μ : @Measure ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      (MeasurableSpace.prod (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))) where
-- BODY
  Tag : Type u
  finiteTag : Fintype Tag
  sourceTag : V → Tag
  targetTag : V' → Tag
  source_injective : Function.Injective sourceTag
  target_injective : Function.Injective targetTag
  overlap : ∀ v v', sourceTag v = targetTag v' ↔ v ∈ S ∧ φ v = v'
  covers : ∀ a : Tag, (∃ v, sourceTag v = a) ∨ (∃ v', targetTag v' = a)
  decode_measurable :
    @Measurable (Tag → ℝ × ℝ)
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      inferInstance (MeasurableSpace.prod (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))
      (SamplingSplitOutsideBlockerProductDecode sourceTag targetTag)
  measure_eq : μ = @Measure.map (Tag → ℝ × ℝ)
      ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      inferInstance (MeasurableSpace.prod (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))
      (SamplingSplitOutsideBlockerProductDecode sourceTag targetTag)
      (by
        letI := finiteTag
        exact Measure.pi fun _ : Tag =>
          ((ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
            ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
              (volume.restrict (Set.Icc (0 : ℝ) 1))))
