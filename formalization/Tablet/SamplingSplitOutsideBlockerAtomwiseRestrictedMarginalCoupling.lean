import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingData

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerAtomwiseRestrictedMarginalCoupling]
theorem SamplingSplitOutsideBlockerAtomwiseRestrictedMarginalCoupling :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
        ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
          ∀ (φ : V → V') (sourceCoord : Finset V)
            (targetCommonCoord : Finset V')
            (cell : Ω → Set (Finset V × (V → ℝ)))
            (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
            (w : Ω → ℝ),
            ∀ pairedMeasure :
              @MeasureTheory.Measure
                ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
                (MeasurableSpace.prod
                  (MeasurableSpace.prod ⊤ inferInstance)
                  (MeasurableSpace.prod ⊤ inferInstance)),
            pairedMeasure {ζ |
              ¬ (ζ.2.1 ∩ targetCommonCoord =
                  (ζ.1.1 ∩ sourceCoord).image φ ∧
                ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v)} = 0 →
            (∀ E : Set (Finset V × (V → ℝ)),
              @MeasurableSet (Finset V × (V → ℝ))
                (MeasurableSpace.prod ⊤ inferInstance) E →
                pairedMeasure {ζ | ζ.1 ∈ E} = ν E) →
            (∀ E' : Set (Finset V' × (V' → ℝ)),
              @MeasurableSet (Finset V' × (V' → ℝ))
                (MeasurableSpace.prod ⊤ inferInstance) E' →
                pairedMeasure {ζ | ζ.2 ∈ E'} = ν' E') →
            (∀ ω : Ω, 0 ≤ w ω) →
            (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) →
            (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) →
            (∀ ω : Ω, ∀ η η',
              η'.1 ∩ targetCommonCoord =
                (η.1 ∩ sourceCoord).image φ →
              (∀ v : V, v ∈ sourceCoord →
                η'.2 (φ v) = η.2 v) →
                (η ∈ cell ω ↔ η' ∈ targetCell ω)) →
            (∀ ω : Ω,
              @MeasurableSet (Finset V × (V → ℝ))
                (MeasurableSpace.prod ⊤ inferInstance) (cell ω)) →
            (∀ ω : Ω,
              @MeasurableSet (Finset V' × (V' → ℝ))
                (MeasurableSpace.prod ⊤ inferInstance) (targetCell ω)) →
            ∃ coupling : SamplingSplitOutsideBlockerMarginalPreservingCouplingData
                ν ν' φ sourceCoord targetCommonCoord cell targetCell w,
              coupling.pairedMeasure = pairedMeasure ∧
              ∀ ω, coupling.pairedCell ω = {ζ |
                ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧
                ζ.2.1 ∩ targetCommonCoord = (ζ.1.1 ∩ sourceCoord).image φ ∧
                ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v} := by
-- BODY
  intro V V' Ω _ _ _ _ _ ν ν' φ S S' cell targetCell w μ
  intro hnull hs ht _hw hmass _htmass htransport hcell htcell
  let sync := {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
    ζ.2.1 ∩ S' = (ζ.1.1 ∩ S).image φ ∧
    ∀ v : V, v ∈ S → ζ.2.2 (φ v) = ζ.1.2 v}
  have hae : ∀ᵐ ζ ∂μ, ζ ∈ sync := by
    exact (ae_iff).2 hnull
  let C : Ω → Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))) :=
    fun ω => {ζ |
    ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧ ζ ∈ sync}
  have heqS (ω : Ω) : C ω =ᵐ[μ] {ζ | ζ.1 ∈ cell ω} := by
    filter_upwards [hae] with ζ hζ
    apply propext
    change (ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧ ζ ∈ sync) ↔ _
    exact ⟨fun h => h.1, fun h =>
      ⟨h, (htransport ω ζ.1 ζ.2 hζ.1 hζ.2).mp h, hζ⟩⟩
  have heqT (ω : Ω) : C ω =ᵐ[μ] {ζ | ζ.2 ∈ targetCell ω} := by
    filter_upwards [hae] with ζ hζ
    apply propext
    change (ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧ ζ ∈ sync) ↔ _
    exact ⟨fun h => h.2.1, fun h =>
      ⟨(htransport ω ζ.1 ζ.2 hζ.1 hζ.2).mpr h, h, hζ⟩⟩
  refine ⟨{
    pairedMeasure := μ
    pairedCell := C
    pairedCell_projects := fun _ _ h => ⟨h.1, h.2.1⟩
    pairedCell_mass := ?_
    pairedCell_common_trace := fun _ _ h => h.2.2.1
    pairedCell_common_priorities := fun _ _ h => h.2.2.2
    source_restricted_marginal := ?_
    target_restricted_marginal := ?_ }, rfl, fun _ => rfl⟩
  · intro ω
    exact (measure_congr (heqS ω)).trans ((hs _ (hcell ω)).trans (hmass ω).symm)
  · intro ω E hE
    have h : Set.inter {ζ | ζ.1 ∈ E} (C ω) =ᵐ[μ] {ζ | ζ.1 ∈ E ∩ cell ω} := by
      filter_upwards [heqS ω] with ζ hζ
      exact propext (and_congr_right fun _ => iff_of_eq hζ)
    exact (measure_congr h).trans (hs _ (hE.inter (hcell ω)))
  · intro ω E hE
    have h : Set.inter {ζ | ζ.2 ∈ E} (C ω) =ᵐ[μ] {ζ | ζ.2 ∈ E ∩ targetCell ω} := by
      filter_upwards [heqT ω] with ζ hζ
      exact propext (and_congr_right fun _ => iff_of_eq hζ)
    exact (measure_congr h).trans (ht _ (hE.inter (htcell ω)))
