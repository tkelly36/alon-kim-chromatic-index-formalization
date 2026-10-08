import Tablet.SamplingBernoulliUniformSurvivorFiberLaw
import Tablet.SamplingFiniteProductContextSlicing
import Tablet.SamplingSplitOutsideBlockerProductRealization
import Tablet.SamplingSplitOutsideBlockerProductAtomContextInvariant
import Tablet.SamplingSplitOutsideBlockerPairedContextCurrentInvariant
import Tablet.SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer
import Tablet.SamplingSplitOutsideBlockerActualCurrentFiberIntegrals
import Tablet.SamplingFiniteMassSubcellNormalization

open MeasureTheory
universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualProductAdjacentIntegral]
theorem SamplingSplitOutsideBlockerActualProductAdjacentIntegral
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ))) (w : Ω → ℝ)
    (surface : SamplingSplitOutsideBlockerPairedMixedMeasureSurface
      G G' φ r X n zAt B hOutside β cell targetCell w)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (product : SamplingSplitOutsideBlockerProductRealization
      p φ surface.sourceCoord surface.pairedMeasure)
    (hβ : Function.Injective β)
    (hFresh : ∀ a, ∀ y ∈ insert r X, β a ≠ φ y)
    (hcurrent : ∀ i, zAt i ∉ surface.sourceCoord)
    (hprivate : ∀ i (x : {x : V // x ∈ X})
      (hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i)),
      β ⟨x, ⟨zAt i, hz⟩⟩ ∉ surface.targetCommonCoord)
    (hw : ∀ ω, 0 ≤ w ω)
    (hcell : ∀ ω, @MeasurableSet (Finset V × (V → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance) (cell ω))
    (hcell' : ∀ ω, @MeasurableSet (Finset V' × (V' → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance) (targetCell ω))
    (htransport : ∀ ω η η',
      η'.1 ∩ surface.targetCommonCoord = (η.1 ∩ surface.sourceCoord).image φ →
      (∀ v ∈ surface.sourceCoord, η'.2 (φ v) = η.2 v) →
        (η ∈ cell ω ↔ η' ∈ targetCell ω))
    (hpaired : ∀ ω, surface.pairedCell ω =
      {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
        ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧
        ζ.2.1 ∩ surface.targetCommonCoord =
          (ζ.1.1 ∩ surface.sourceCoord).image φ ∧
        ∀ v ∈ surface.sourceCoord, ζ.2.2 (φ v) = ζ.1.2 v})
    (k : Fin n) (ω : Ω) :
    let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
      (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
    let U := {ζ | ∃ x : {x : V // x ∈ X}, x.1 ∉ B k ∧ ζ ∈ C x}
    let L := surface.mixedStage k ω \ U
    let R := surface.mixedStage (k.val + 1) ω \ U
    ∃ unchanged leftBoundary rightBoundary : ℝ,
      0 ≤ unchanged ∧ 0 ≤ leftBoundary ∧ 0 ≤ rightBoundary ∧
      ENNReal.ofReal (w ω * unchanged) =
        surface.pairedMeasure (U ∩ surface.pairedCell ω) ∧
      ENNReal.ofReal (w ω * leftBoundary) =
        surface.pairedMeasure (L ∩ surface.pairedCell ω) ∧
      ENNReal.ofReal (w ω * rightBoundary) =
        surface.pairedMeasure (R ∩ surface.pairedCell ω) ∧
      surface.mixedMass k ω = unchanged + leftBoundary ∧
      surface.mixedMass (k.val + 1) ω = unchanged + rightBoundary ∧
      leftBoundary ≤ rightBoundary := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  dsimp only
  let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
    (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
  let U := {ζ | ∃ x : {x : V // x ∈ X}, x.1 ∉ B k ∧ ζ ∈ C x}
  let L := surface.mixedStage k ω \ U
  let R := surface.mixedStage (k.val + 1) ω \ U
  let μ := surface.pairedMeasure
  let Q := surface.pairedCell ω
  change ∃ u l r' : ℝ, 0 ≤ u ∧ 0 ≤ l ∧ 0 ≤ r' ∧
    ENNReal.ofReal (w ω * u) = μ (U ∩ Q) ∧
    ENNReal.ofReal (w ω * l) = μ (L ∩ Q) ∧
    ENNReal.ofReal (w ω * r') = μ (R ∩ Q) ∧
    surface.mixedMass k ω = u + l ∧
    surface.mixedMass (k.val + 1) ω = u + r' ∧ l ≤ r'
  obtain ⟨hQ, hq, hleft, hright⟩ :=
    SamplingSplitOutsideBlockerActualCurrentFiberIntegrals G G' φ r X n zAt B
      hOutside β cell targetCell w surface p hp hp' product hβ hFresh hcurrent
      hprivate hcell hcell' htransport hpaired k ω
  have hcompare : μ (L ∩ Q) ≤ μ (R ∩ Q) := by
    rw [hleft, hright]
    apply lintegral_mono_ae
    filter_upwards [hq] with t ht
    apply Set.indicator_le_indicator
    exact (SamplingBernoulliUniformSurvivorFiberLaw p hp hp' _ _
      (fun a _ => ht a)).2.2.2.2.2.2
  obtain ⟨hS, hT, _, _, _, hU, hL, hR⟩ :=
    SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer G G' φ r X n
      zAt B hOutside β cell targetCell w surface k ω
  have hUS : U ⊆ surface.mixedStage k ω := by
    rw [hS]
    exact Set.subset_union_left
  have hUT : U ⊆ surface.mixedStage (k.val + 1) ω := by
    rw [hT]
    exact Set.subset_union_left
  have hmL : MeasurableSet L := by
    apply MeasurableSet.diff _ hU
    rw [hS]
    exact hU.union hL
  have hmR : MeasurableSet R := by
    apply MeasurableSet.diff _ hU
    rw [hT]
    exact hU.union hR
  have hsplit (H : Set ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))))
      (hUH : U ⊆ H) (hm : MeasurableSet (H \ U)) :
      μ (H ∩ Q) = μ (U ∩ Q) + μ ((H \ U) ∩ Q) := by
    have heq : H = U ∪ (H \ U) := by
      ext ζ
      constructor
      · intro h
        by_cases hu : ζ ∈ U
        · exact Or.inl hu
        · exact Or.inr ⟨h, hu⟩
      · rintro (h | h)
        · exact hUH h
        · exact h.1
    conv_lhs => rw [heq, Set.union_inter_distrib_right]
    apply measure_union _ (hm.inter hQ)
    exact Set.disjoint_left.mpr (fun ζ hu hl => hl.1.2 hu.1)
  obtain ⟨u, hu, huz, hue⟩ := SamplingFiniteMassSubcellNormalization μ (w ω) Q
    (U ∩ Q) (hw ω) (surface.pairedCell_mass ω).symm Set.inter_subset_right
  obtain ⟨l, hl, hlz, hle⟩ := SamplingFiniteMassSubcellNormalization μ (w ω) Q
    (L ∩ Q) (hw ω) (surface.pairedCell_mass ω).symm Set.inter_subset_right
  obtain ⟨r', hr, hrz, hre⟩ := SamplingFiniteMassSubcellNormalization μ (w ω) Q
    (R ∩ Q) (hw ω) (surface.pairedCell_mass ω).symm Set.inter_subset_right
  refine ⟨u, l, r', hu, hl, hr, hue, hle, hre, ?_⟩
  by_cases hz : w ω = 0
  · simp only [huz hz, hlz hz, hrz hz,
      surface.mixedMass_zero_of_zero_weight _ _ hz, zero_add, le_refl, and_self]
  · have hwpos : 0 < w ω := lt_of_le_of_ne (hw ω) (Ne.symm hz)
    have hsum (j : ℕ) (hj : j ≤ n) (b : ℝ) (hb : 0 ≤ b)
        (hbe : ENNReal.ofReal (w ω * b) = μ ((surface.mixedStage j ω \ U) ∩ Q))
        (hsub : U ⊆ surface.mixedStage j ω)
        (hm : MeasurableSet (surface.mixedStage j ω \ U)) :
        surface.mixedMass j ω = u + b := by
      apply (mul_left_cancel₀ hz)
      apply (ENNReal.ofReal_eq_ofReal_iff
        (mul_nonneg (hw ω) (surface.mixedMass_nonneg j ω))
        (mul_nonneg (hw ω) (add_nonneg hu hb))).mp
      rw [surface.mixedMass_measures_stage j hj ω,
        hsplit _ hsub hm, mul_add,
        ENNReal.ofReal_add (mul_nonneg (hw ω) hu) (mul_nonneg (hw ω) hb), hue, hbe]
    refine ⟨hsum k (Nat.le_of_lt k.isLt) l hl hle hUS hmL,
      hsum (k.val + 1) (by omega) r' hr hre hUT hmR, ?_⟩
    apply (mul_le_mul_iff_right₀ hwpos).mp
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hw ω) hr)).mp
    rwa [hle, hre]
