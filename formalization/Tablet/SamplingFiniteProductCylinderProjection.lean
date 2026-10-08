import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingFiniteProductCylinderProjection]
theorem SamplingFiniteProductCylinderProjection :
    ∀ {Source Target : Type u} [MeasurableSpace Source] [MeasurableSpace Target],
      ∀ (ν : MeasureTheory.Measure Source) (ν' : MeasureTheory.Measure Target)
        [SFinite ν] [SFinite ν'] (E : Set Source) (F : Set Target),
        ν Set.univ = 1 →
        ν' Set.univ = 1 →
        MeasureTheory.Measure.prod ν ν' (E ×ˢ (Set.univ : Set Target)) = ν E ∧
          MeasureTheory.Measure.prod ν ν' ((Set.univ : Set Source) ×ˢ F) = ν' F := by
-- BODY
  intro Source Target _ _ ν ν' _ _ E F hν hν'
  constructor
  · rw [MeasureTheory.Measure.prod_prod, hν']
    simp
  · rw [MeasureTheory.Measure.prod_prod, hν]
    simp
