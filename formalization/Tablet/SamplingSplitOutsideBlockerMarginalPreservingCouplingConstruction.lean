import Tablet.SamplingSplitOutsideBlockerPrescribedCommonRefinedCellPackage
import Tablet.SamplingSplitOutsideBlockerMarginalPreservingCouplingData
import Tablet.SamplingSplitOutsideBlockerCopiedCommonProductCouplingMarginals
import Tablet.SamplingSplitOutsideBlockerAtomwiseRestrictedMarginalCoupling

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMarginalPreservingCouplingConstruction]
theorem SamplingSplitOutsideBlockerMarginalPreservingCouplingConstruction :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ Delta : ℕ, ∀ gamma : ℝ,
        ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
        ∀ (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance)),
          0 ≤ gamma / (Delta : ℝ) →
          gamma / (Delta : ℝ) ≤ 1 →
          (∀ A : Finset V,
            ν {ω | ω.1 = A} =
              ENNReal.ofReal
                ((gamma / (Delta : ℝ)) ^ A.card *
                  (1 - gamma / (Delta : ℝ)) ^
                    ((Finset.univ : Finset V).card - A.card))) →
          (∀ A : Finset V, ∀ t : V → ℝ,
            (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
              ν {ω |
                ω.1 = A ∧
                  ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                ν {ω | ω.1 = A} *
                  ENNReal.ofReal (∏ v : V, t v)) →
          (∀ A : Finset V',
            ν' {ω | ω.1 = A} =
              ENNReal.ofReal
                ((gamma / (Delta : ℝ)) ^ A.card *
                  (1 - gamma / (Delta : ℝ)) ^
                    ((Finset.univ : Finset V').card - A.card))) →
          (∀ A : Finset V', ∀ t : V' → ℝ,
            (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
              ν' {ω |
                ω.1 = A ∧
                  ∀ v' : V', 0 ≤ ω.2 v' ∧ ω.2 v' ≤ t v'} =
                ν' {ω | ω.1 = A} *
                  ENNReal.ofReal (∏ v' : V', t v')) →
          ∀ (φ : V → V') (sourceCoord : Finset V)
            (targetCommonCoord : Finset V')
            (cell : Ω → Set (Finset V × (V → ℝ)))
            (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
            (w : Ω → ℝ),
            Function.Injective φ →
            targetCommonCoord = sourceCoord.image φ →
            (∀ ω : Ω, 0 ≤ w ω) →
            (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) →
            (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) →
            (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) →
            (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
              Disjoint (targetCell ω₁) (targetCell ω₂)) →
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
              Nonempty (SamplingSplitOutsideBlockerProductRealization
                (gamma / (Delta : ℝ)) φ sourceCoord coupling.pairedMeasure) ∧
              ∀ ω, coupling.pairedCell ω = {ζ |
                ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧
                ζ.2.1 ∩ targetCommonCoord = (ζ.1.1 ∩ sourceCoord).image φ ∧
                ∀ v : V, v ∈ sourceCoord → ζ.2.2 (φ v) = ζ.1.2 v} := by
-- BODY
  intro V V' Ω hV hDecV hV' hDecV' hΩ Delta gamma ν ν'
  intro hgamma_nonneg hgamma_le hsource_act hsource_rect
  intro htarget_act htarget_rect φ sourceCoord targetCommonCoord
  intro cell targetCell w hφ htargetCommon hnonneg hsource_mass
  intro htarget_mass _hsource_disjoint _htarget_disjoint htransport
  intro hcell_meas htargetCell_meas
  rcases
    SamplingSplitOutsideBlockerCopiedCommonProductCouplingMarginals
      (V := V) (V' := V') Delta gamma ν ν'
      hgamma_nonneg hgamma_le hsource_act hsource_rect
      htarget_act htarget_rect φ sourceCoord targetCommonCoord
      hφ htargetCommon with
  ⟨pairedMeasure, hsync_null, hsource_marginal, htarget_marginal, hproduct⟩
  obtain ⟨coupling, hmeasure, hcells⟩ :=
    SamplingSplitOutsideBlockerAtomwiseRestrictedMarginalCoupling
      (V := V) (V' := V') (Ω := Ω) ν ν' φ sourceCoord targetCommonCoord
      cell targetCell w pairedMeasure hsync_null hsource_marginal htarget_marginal
      hnonneg hsource_mass htarget_mass htransport hcell_meas htargetCell_meas
  refine ⟨coupling, ?_, hcells⟩
  simpa only [hmeasure] using hproduct
