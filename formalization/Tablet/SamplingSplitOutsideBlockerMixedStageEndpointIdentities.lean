import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMixedStageEndpointIdentities]
theorem SamplingSplitOutsideBlockerMixedStageEndpointIdentities :
    ∀ {Ω Source Target : Type u} [Fintype Ω] [MeasurableSpace Source]
      [MeasurableSpace Target],
      ∀ (n : ℕ) (w : Ω → ℝ)
        (ν : MeasureTheory.Measure Source) (ν' : MeasureTheory.Measure Target)
        (cell : Ω → Set Source) (targetCell : Ω → Set Target)
        (sourceStage : ℕ → Ω → Set Source)
        (targetStage : ℕ → Ω → Set Target)
        (sourceEndpoint : Ω → Set Source)
        (targetEndpoint : Ω → Set Target)
        (stageMass : ℕ → Ω → ℝ),
        (∀ ω : Ω,
          ENNReal.ofReal (w ω * stageMass 0 ω) =
            ν (sourceStage 0 ω ∩ cell ω)) →
        (∀ ω : Ω,
          ENNReal.ofReal (w ω * stageMass n ω) =
            ν' (targetStage n ω ∩ targetCell ω)) →
        (∀ ω : Ω, sourceStage 0 ω ∩ cell ω = sourceEndpoint ω ∩ cell ω) →
        (∀ ω : Ω, targetStage n ω ∩ targetCell ω = targetEndpoint ω ∩ targetCell ω) →
        (∀ ω : Ω,
          ENNReal.ofReal (w ω * stageMass 0 ω) =
            ν (sourceEndpoint ω ∩ cell ω)) ∧
          (∀ ω : Ω,
            ENNReal.ofReal (w ω * stageMass n ω) =
              ν' (targetEndpoint ω ∩ targetCell ω)) := by
-- BODY
  intro Ω Source Target _ _ _ n w ν ν' cell targetCell sourceStage
    targetStage sourceEndpoint targetEndpoint stageMass hsource htarget
    hsource_id htarget_id
  constructor
  · intro ω
    rw [← hsource_id ω]
    exact hsource ω
  · intro ω
    rw [← htarget_id ω]
    exact htarget ω
