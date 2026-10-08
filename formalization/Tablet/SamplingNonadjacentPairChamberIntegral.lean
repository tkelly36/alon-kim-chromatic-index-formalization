import Tablet.SamplingActivationPriorityPushForwardSupport
import Tablet.SamplingNonadjacentPairSurvivalChamberLaw

open BigOperators

universe u

-- [TABLET NODE: SamplingNonadjacentPairChamberIntegral]
theorem SamplingNonadjacentPairChamberIntegral :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, ∀ gamma : ℝ,
          ∀ μ : Finset V → ℝ,
            ∀ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
              0 < gamma →
              gamma ≤ (Delta : ℝ) →
              (∀ S : Finset V, 0 ≤ μ S) →
              (∀ z : V, G.degree z = Delta) →
              ν Set.univ = 1 →
              (∀ A : Finset V,
                ν {ω | ω.1 = A} =
                  ENNReal.ofReal
                    ((gamma / (Delta : ℝ)) ^ A.card *
                      (1 - gamma / (Delta : ℝ)) ^
                        ((Finset.univ : Finset V).card - A.card))) →
              (∀ A : Finset V,
                ν {ω | ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
                  ν {ω | ω.1 = A}) →
              (∀ A : Finset V, ∀ t : V → ℝ,
                (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                  ν {ω |
                    ω.1 = A ∧
                      ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                    ν {ω | ω.1 = A} *
                      ENNReal.ofReal (∏ v : V, t v)) →
              (∀ A : Finset V, ∀ v : V, v ∈ A →
                ν {ω |
                  ω.1 = A ∧
                    (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
                      ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
                  ν {ω | ω.1 = A} *
                    ENNReal.ofReal
                      (∫ a in (0 : ℝ)..1,
                        a ^
                          ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))) →
              (∀ S : Finset V,
                ENNReal.ofReal (μ S) =
                  ν {ω |
                    S =
                      (Finset.univ.filter fun v : V =>
                        v ∈ ω.1 ∧
                          ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v)}) →
              ∀ u v : V, u ≠ v → ¬ G.Adj u v →
                (∑ S : Finset V, if ({u, v} : Finset V) ⊆ S then μ S else 0) =
                  (2 / (Delta : ℝ)^2) *
                    ∫ x in (0 : ℝ)..gamma,
                      ∫ y in x..gamma,
                        (1 - x / (Delta : ℝ)) ^
                            (Delta -
                              (G.neighborFinset u ∩ G.neighborFinset v).card) *
                          (1 - y / (Delta : ℝ)) ^ Delta := by
-- BODY
  intro V hV hVdec G hGdec Delta gamma μ ν hgamma_pos hgamma_le hμ_nonneg hreg hν_univ
    hactivation hunit hrect hsingle hpush u v huv huv_nonadj
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let out : Finset V × (V → ℝ) → Finset V :=
    fun ω =>
      Finset.univ.filter fun z : V =>
        z ∈ ω.1 ∧ ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z
  let P : Finset V := {u, v}
  let T : Finset (Finset V) := Finset.univ.filter fun S : Finset V => P ⊆ S
  let rhs : ℝ :=
    (2 / (Delta : ℝ)^2) *
      ∫ x in (0 : ℝ)..gamma,
        ∫ y in x..gamma,
          (1 - x / (Delta : ℝ)) ^
              (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
            (1 - y / (Delta : ℝ)) ^ Delta
  have hsum :
      ENNReal.ofReal (∑ S : Finset V, if P ⊆ S then μ S else 0) =
        Finset.sum T (fun S => ENNReal.ofReal (μ S)) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _hS
      by_cases hPS : P ⊆ S <;> simp [hPS]
    · intro S _hS
      by_cases hPS : P ⊆ S
      · simp [hPS, hμ_nonneg S]
      · simp [hPS]
  have hunion :
      {ω | P ⊆ out ω} = ⋃ S ∈ T, {ω | S = out ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hPout
      refine ⟨out ω, ?_, ?_⟩
      · simp [T, hPout]
      · exact rfl
    · rintro ⟨S, hST, hSω⟩
      have hPS : P ⊆ S := by
        simpa [T] using hST
      simpa [hSω] using hPS
  have hfiber_meas (S : Finset V) : MeasurableSet {ω | S = out ω} := by
    let survSet : Finset V → V → Set (Finset V × (V → ℝ)) :=
      fun A z =>
        {ω |
          z ∈ A ∧ ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z}
    let fiberPiece : Finset V → Set (Finset V × (V → ℝ)) :=
      fun A =>
        {ω |
          ω.1 = A ∧
            S =
              Finset.univ.filter fun z : V =>
                z ∈ A ∧
                  ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z}
    have hcoord_meas (z : V) :
        Measurable (fun ω : Finset V × (V → ℝ) => ω.2 z) := by
      exact Measurable.eval (a := z) measurable_snd
    have hsurv_meas (A : Finset V) (z : V) : MeasurableSet (survSet A z) := by
      by_cases hzA : z ∈ A
      · have hcuts :
            MeasurableSet
              ({ω : Finset V × (V → ℝ) |
                ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z}) := by
          let N : Finset V := A.filter fun w => G.Adj z w
          convert Finset.measurableSet_biInter N (fun w _hw => by
            exact measurableSet_lt (hcoord_meas w) (hcoord_meas z)) using 1
          ext ω
          simp [N]
        convert hcuts using 1
        ext ω
        simp [survSet, hzA]
      · have hsurv_empty : survSet A z = ∅ := by
          ext ω
          simp [survSet, hzA]
        rw [hsurv_empty]
        exact MeasurableSet.empty
    have hfilter_meas (A : Finset V) :
        MeasurableSet
          ({ω : Finset V × (V → ℝ) |
            S =
              Finset.univ.filter fun z : V =>
                z ∈ A ∧
                  ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z}) := by
      let memberSet : V → Set (Finset V × (V → ℝ)) :=
        fun z => if z ∈ S then survSet A z else (survSet A z)ᶜ
      have hmember_meas (z : V) : MeasurableSet (memberSet z) := by
        by_cases hzS : z ∈ S
        · simp [memberSet, hzS, hsurv_meas A z]
        · simp [memberSet, hzS, (hsurv_meas A z).compl]
      have hfilter_eq :
          ({ω : Finset V × (V → ℝ) |
            S =
              Finset.univ.filter fun z : V =>
                z ∈ A ∧
                  ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z}) =
            ⋂ z ∈ (Finset.univ : Finset V), memberSet z := by
        ext ω
        constructor
        · intro hSω
          rw [Set.mem_iInter]
          intro z
          rw [Set.mem_iInter]
          intro _hz_univ
          by_cases hzS : z ∈ S
          · have hz_filter :
                z ∈
                  Finset.univ.filter fun z : V =>
                    z ∈ A ∧
                      ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z := by
              rw [← hSω]
              exact hzS
            have hsurv : ω ∈ survSet A z := by
              simpa [survSet] using (Finset.mem_filter.mp hz_filter).2
            simpa [memberSet, hzS] using hsurv
          · have hnot_surv : ω ∉ survSet A z := by
              intro hsurv
              have hz_filter :
                  z ∈
                    Finset.univ.filter fun z : V =>
                      z ∈ A ∧
                        ∀ w : V, w ∈ A → G.Adj z w → ω.2 w < ω.2 z := by
                exact Finset.mem_filter.mpr ⟨by simp, by simpa [survSet] using hsurv⟩
              have hzS' : z ∈ S := by
                rw [hSω]
                exact hz_filter
              exact hzS hzS'
            simpa [memberSet, hzS] using hnot_surv
        · intro hω
          ext z
          constructor
          · intro hzS
            have hz_member : ω ∈ memberSet z := by
              have hz_all := (Set.mem_iInter.mp hω) z
              exact (Set.mem_iInter.mp hz_all) (by simp)
            have hsurv : ω ∈ survSet A z := by
              simpa [memberSet, hzS] using hz_member
            exact Finset.mem_filter.mpr ⟨by simp, by simpa [survSet] using hsurv⟩
          · intro hz_filter
            by_contra hzS
            have hz_member : ω ∈ memberSet z := by
              have hz_all := (Set.mem_iInter.mp hω) z
              exact (Set.mem_iInter.mp hz_all) (by simp)
            have hnot_surv : ω ∉ survSet A z := by
              simpa [memberSet, hzS] using hz_member
            have hsurv : ω ∈ survSet A z := by
              simpa [survSet] using (Finset.mem_filter.mp hz_filter).2
            exact hnot_surv hsurv
      rw [hfilter_eq]
      exact Finset.measurableSet_biInter (Finset.univ : Finset V)
        (fun z _hz => hmember_meas z)
    have hfiberPiece_meas (A : Finset V) : MeasurableSet (fiberPiece A) := by
      have hfirst :
          MeasurableSet ({ω : Finset V × (V → ℝ) | ω.1 = A}) := by
        letI : MeasurableSpace (Finset V) := ⊤
        change MeasurableSet (Prod.fst ⁻¹' ({A} : Set (Finset V)))
        exact (show MeasurableSet ({A} : Set (Finset V)) from trivial).preimage
          measurable_fst
      have hmeas : MeasurableSet (fiberPiece A) := by
        dsimp [fiberPiece]
        exact hfirst.inter (hfilter_meas A)
      exact hmeas
    have hfiber_eq :
        {ω | S = out ω} =
          ⋃ A ∈ (Finset.univ : Finset (Finset V)), fiberPiece A := by
      ext ω
      constructor
      · intro hω
        rw [Set.mem_iUnion]
        refine ⟨ω.1, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨by simp, ?_⟩
        exact ⟨rfl, by simpa [out, fiberPiece] using hω⟩
      · intro hω
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨A, hω⟩
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨_hA, hω⟩
        rcases hω with ⟨hωA, hSω⟩
        simpa [out, hωA] using hSω
    rw [hfiber_eq]
    exact Finset.measurableSet_biUnion (Finset.univ : Finset (Finset V))
      (fun A _hA => hfiberPiece_meas A)
  have hpush_pair :
      ENNReal.ofReal (∑ S : Finset V, if P ⊆ S then μ S else 0) =
        ν {ω | P ⊆ out ω} := by
    rw [hsum, hunion]
    rw [MeasureTheory.measure_biUnion_finset]
    · simp [T, out, hpush]
    · intro S _hS T' _hT hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω hωS hωT
      exact hne (hωS.trans hωT.symm)
    · intro S _hS
      exact hfiber_meas S
  have hpair_event :
      {ω | P ⊆ out ω} =
        {ω |
          u ∈
              (Finset.univ.filter fun z : V =>
                z ∈ ω.1 ∧
                  ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
            v ∈
              (Finset.univ.filter fun z : V =>
                z ∈ ω.1 ∧
                  ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} := by
    ext ω
    constructor
    · intro hP
      exact ⟨hP (by simp [P]), hP (by simp [P])⟩
    · intro huv_out z hz
      have hzuv : z = u ∨ z = v := by
        simpa [P] using hz
      rcases hzuv with rfl | rfl
      · exact huv_out.1
      · exact huv_out.2
  have hsurvival :
      ν {ω |
        u ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
          v ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
        ENNReal.ofReal rhs := by
    simpa [rhs] using
      SamplingNonadjacentPairSurvivalChamberLaw G Delta gamma ν hgamma_pos hgamma_le hreg
        hν_univ hactivation hunit hrect hsingle u v huv huv_nonadj
  have hofReal :
      ENNReal.ofReal (∑ S : Finset V, if P ⊆ S then μ S else 0) =
        ENNReal.ofReal rhs := by
    rw [hpush_pair, hpair_event, hsurvival]
  have hlhs_nonneg : 0 ≤ ∑ S : Finset V, if P ⊆ S then μ S else 0 := by
    exact Finset.sum_nonneg fun S _hS => by
      by_cases hPS : P ⊆ S
      · simp [hPS, hμ_nonneg S]
      · simp [hPS]
  have hDelta_pos : 0 < (Delta : ℝ) := lt_of_lt_of_le hgamma_pos hgamma_le
  have hkernel_nonneg :
      0 ≤
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 - x / (Delta : ℝ)) ^
                (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
              (1 - y / (Delta : ℝ)) ^ Delta := by
    refine intervalIntegral.integral_nonneg (le_of_lt hgamma_pos) ?_
    intro x hx
    refine intervalIntegral.integral_nonneg hx.2 ?_
    intro y hy
    have hxDelta : x ≤ (Delta : ℝ) := hx.2.trans hgamma_le
    have hyDelta : y ≤ (Delta : ℝ) := hy.2.trans hgamma_le
    have hxbase : 0 ≤ 1 - x / (Delta : ℝ) := by
      have hxdiv : x / (Delta : ℝ) ≤ 1 := by
        rw [div_le_one hDelta_pos]
        exact hxDelta
      linarith
    have hybase : 0 ≤ 1 - y / (Delta : ℝ) := by
      have hydiv : y / (Delta : ℝ) ≤ 1 := by
        rw [div_le_one hDelta_pos]
        exact hyDelta
      linarith
    exact mul_nonneg (pow_nonneg hxbase _) (pow_nonneg hybase _)
  have hrhs_nonneg : 0 ≤ rhs := by
    have hfactor_nonneg : 0 ≤ 2 / (Delta : ℝ)^2 := by positivity
    exact mul_nonneg hfactor_nonneg hkernel_nonneg
  have hreal :
      (∑ S : Finset V, if P ⊆ S then μ S else 0) = rhs :=
    (ENNReal.ofReal_eq_ofReal_iff hlhs_nonneg hrhs_nonneg).mp hofReal
  simpa [P, rhs] using hreal
