import Tablet.RandomIndependentSetSampling
import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Tablet.SamplingNonemptyPushForwardEvent
import Tablet.SamplingFiniteConditionalReplacementIteration
import Tablet.SamplingFiniteCellEndpointSumDecomposition
import Tablet.SamplingOneBlockerProductInequality
import Tablet.SamplingCandidateSetReplacementSurvivalComparison
import Tablet.SamplingFiniteProductCandidateReplacementStep
import Tablet.SamplingFinitePriorityCutProductFormula
import Tablet.SamplingIntegratedCandidatePriorityReplacementStep
import Tablet.SamplingSplitOutsideBlockerHybridRepresentation

open BigOperators

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerEventMonotonicity]
theorem SamplingSplitOutsideBlockerEventMonotonicity :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ Delta : ℕ, ∀ gamma : ℝ,
            (∀ v : V, G.degree v = Delta) →
            (∀ v' : V', G'.degree v' = Delta) →
            ∀ μ : Finset V → ℝ, ∀ μ' : Finset V' → ℝ,
              RandomIndependentSetSampling G Delta gamma μ →
              RandomIndependentSetSampling G' Delta gamma μ' →
              ∀ (φ : V → V') (r : V) (X : Finset V),
                Function.Injective φ →
                (∀ x : V, x ∈ X → G.Adj r x) →
                (∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
                  (G.Adj a b ↔ G'.Adj (φ a) (φ b))) →
                  ∀ (β :
                    (Σ x : {x : V // x ∈ X},
                      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
                    Function.Injective β →
                    (∀ x : V, ∀ hx : x ∈ X,
                      ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      ∀ y : V, y ∈ insert r X →
                        β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ≠ φ y) →
                    (∀ x : V, ∀ hx : x ∈ X,
                      ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                        G'.Adj (φ x)
                        (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                    ∀ y : V, y ∈ X →
                      G'.Adj (φ y) (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) → y = x) →
                  (∀ x : V, ∀ hx : x ∈ X,
                    ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                      ¬ G'.Adj (φ r)
                        (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
                  (∀ x : V, ∀ hx : x ∈ X, ∀ w' : V',
                    G'.Adj (φ x) w' →
                      (∃ y : V, y ∈ insert r X ∧ w' = φ y ∧ G.Adj x y) ∨
                        ∃ z : V, ∃ hz : z ∉ insert r X ∧ G.Adj x z,
                          w' = β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩) →
                (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
                  (∑ S' : Finset V',
                    if (S' ∩ X.image φ).Nonempty then μ' S' else 0) := by
-- BODY
  classical
  intro V V' _instV _instDecV _instV' _instDecV' G _instAdjG G' _instAdjG'
    Delta gamma hG_regular hG'_regular μ μ' hsamp hsamp' φ r X hφ_inj hX_neigh
    hlocal_adj β hβ_inj hβ_fresh hβ_adj hβ_private hβ_not_r hclassify
  have hsamp_src : RandomIndependentSetSampling G Delta gamma μ := hsamp
  have hsamp_tgt : RandomIndependentSetSampling G' Delta gamma μ' := hsamp'
  rcases hsamp with
    ⟨hgamma_pos, hμ_data, ν, hν_univ, hν_A, hν_prio_mem, hν_prio_rect,
      hν_compare, hpush, hind⟩
  rcases hsamp' with
    ⟨hgamma_pos', hμ'_data, ν', hν'_univ, hν'_A, hν'_prio_mem, hν'_prio_rect,
      hν'_compare, hpush', hind'⟩
  have hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S := hμ_data.1
  have hμ'_nonneg : ∀ S' : Finset V', 0 ≤ μ' S' := hμ'_data.1
  have hleft_event :
      ENNReal.ofReal (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) =
        ν {ω |
          ((Finset.univ.filter fun z : V =>
            z ∈ ω.1 ∧
              ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∩ X).Nonempty} := by
    exact SamplingNonemptyPushForwardEvent G μ ν hμ_nonneg hpush X
  have hright_event :
      ENNReal.ofReal
          (∑ S' : Finset V', if (S' ∩ X.image φ).Nonempty then μ' S' else 0) =
        ν' {ω |
          ((Finset.univ.filter fun z : V' =>
            z ∈ ω.1 ∧
              ∀ w : V', w ∈ ω.1 → G'.Adj z w → ω.2 w < ω.2 z) ∩
              X.image φ).Nonempty} := by
    exact SamplingNonemptyPushForwardEvent G' μ' ν' hμ'_nonneg hpush' (X.image φ)
  have hleft_nonneg :
      0 ≤ (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) := by
    exact Finset.sum_nonneg fun S _hS => by
      by_cases hSX : (S ∩ X).Nonempty
      · simp [hSX, hμ_nonneg S]
      · simp [hSX]
  have hright_nonneg :
      0 ≤ (∑ S' : Finset V', if (S' ∩ X.image φ).Nonempty then μ' S' else 0) := by
    exact Finset.sum_nonneg fun S' _hS' => by
      by_cases hSX : (S' ∩ X.image φ).Nonempty
      · simp [hSX, hμ'_nonneg S']
      · simp [hSX]
  have hevent_le :
      ν {ω |
        ((Finset.univ.filter fun z : V =>
          z ∈ ω.1 ∧
            ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∩ X).Nonempty} ≤
        ν' {ω |
          ((Finset.univ.filter fun z : V' =>
            z ∈ ω.1 ∧
              ∀ w : V', w ∈ ω.1 → G'.Adj z w → ω.2 w < ω.2 z) ∩
              X.image φ).Nonempty} := by
    rcases
        SamplingSplitOutsideBlockerHybridRepresentation G G' Delta gamma
          hG_regular hG'_regular μ μ' hsamp_src hsamp_tgt ν ν'
          hν_A hν_prio_rect hν'_A hν'_prio_rect φ r X hφ_inj hX_neigh
          hlocal_adj β hβ_inj hβ_fresh hβ_adj hβ_private hβ_not_r
          hclassify with
      ⟨n, zAt, B, sourceCoord, sourceExtensionCoord, targetCommonCoord,
        targetExtensionCoord, targetCoord, Ω, hΩ, cell, targetCell, w,
        sourceStage, targetStage, P, hzinj, hActualOutside, hzAt_cover, hB,
        hsourceExt, hsourceDisj, hsourceCoord, htargetCommon, htargetDisj,
        htargetCoord, htargetContains, htargetExt, hw_nonneg, hcell_mass,
        htargetcell_mass, hcell_disj, htargetcell_disj, hcell_cover,
        htargetcell_cover, hcell_unit_zero, htargetcell_unit_zero,
        hsourceStage, htargetStage, hP_nonneg, hP_zero, hP_source,
        hP_target, haggregate_source, haggregate_target, hP_mono⟩
    have hsum_le :
        (∑ ω : Ω, w ω * P 0 ω) ≤ (∑ ω : Ω, w ω * P n ω) :=
      SamplingFiniteConditionalReplacementIteration n w P hw_nonneg hP_mono
    rw [← haggregate_source, ← haggregate_target]
    exact ENNReal.ofReal_le_ofReal hsum_le
  have hofreal_le :
      ENNReal.ofReal (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
        ENNReal.ofReal
          (∑ S' : Finset V', if (S' ∩ X.image φ).Nonempty then μ' S' else 0) := by
    rw [hleft_event, hright_event]
    exact hevent_le
  exact (ENNReal.ofReal_le_ofReal_iff hright_nonneg).mp hofreal_le
