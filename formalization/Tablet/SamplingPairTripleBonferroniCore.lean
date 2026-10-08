import Tablet.RandomIndependentSetSampling
import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Tablet.SamplingFiniteProductPointwiseLower
import Tablet.SamplingCleanPairEllPositivity
import Tablet.SamplingIndependentPairsHalfDegreeSquare
import Tablet.SamplingPairBonferroniPairLowerBound
import Tablet.SamplingPairBonferroniParameterSelection
import Tablet.SamplingPairHighOverlapWindowLower
import Tablet.SamplingPairHighOverlapExponentialWindowMargin
import Tablet.SamplingPairHighOverlapFiniteProductWindowLower
import Tablet.SamplingPairKernelSplitLowerBound
import Tablet.SamplingPairLowOverlapExponentialWindowMargin
import Tablet.SamplingPairLowOverlapWindowLower
import Tablet.SamplingPairExposureEstimate
import Tablet.SamplingTripleCorrectionReindexing
import Tablet.SamplingTripleExposureEstimate

open BigOperators

-- [TABLET NODE: SamplingPairTripleBonferroniCore]
theorem SamplingPairTripleBonferroniCore (eta : ℝ) (heta : 0 < eta) :
    ∃ Delta0 gamma0 : ℕ, ∀ Delta : ℕ, ∀ gamma : ℝ,
      Delta0 ≤ Delta → (gamma0 : ℝ) ≤ gamma →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              (∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
                ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w) →
              let J2 : Finset (Finset V) :=
                (Finset.univ.filter fun P : Finset V =>
                  P.card = 2 ∧ P ⊆ X ∧
                    ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
              let J3 : Finset (Finset V) :=
                (Finset.univ.filter fun P : Finset V =>
                  P.card = 3 ∧ P ⊆ X ∧
                    ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
              (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) -
                  (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) ≥
                (J2.card : ℝ) / (Delta : ℝ)^2 -
              (J3.card : ℝ) / (Delta : ℝ)^3 - eta := by
-- BODY
  classical
  rcases SamplingPairBonferroniParameterSelection eta heta with
    ⟨alpha, L, gammaR, DeltaPair,
      halpha_pos, halpha_le_one, halpha_one_pos, hL_nonneg, hgammaR_nonneg,
      hthree_alpha, htail, hnumeric, hlarge_pair⟩
  have heta_third_pos : 0 < eta / 3 := by positivity
  rcases SamplingTripleExposureEstimate (eta / 3) heta_third_pos with
    ⟨DeltaTriple, gammaTriple, htriple_est⟩
  rcases exists_nat_ge (max gammaR L) with ⟨gammaPair, hgammaPair_ge⟩
  refine ⟨max DeltaPair DeltaTriple, max gammaPair gammaTriple, ?_⟩
  intro Delta gamma hDelta hgamma V _instFintype _instDecEq G _instDecRel hregular μ hsampling r X hX hclean J2 J3
  have hDeltaPair : DeltaPair ≤ Delta := (le_max_left _ _).trans hDelta
  have hDeltaTriple : DeltaTriple ≤ Delta := (le_max_right _ _).trans hDelta
  have hgamma_real : max (gammaPair : ℝ) (gammaTriple : ℝ) ≤ gamma := by
    simpa [Nat.cast_max] using hgamma
  have hgammaPair_le : (gammaPair : ℝ) ≤ gamma := by
    have hgp_max : (gammaPair : ℝ) ≤ (max gammaPair gammaTriple : ℝ) := by
      exact_mod_cast (le_max_left gammaPair gammaTriple)
    exact hgp_max.trans hgamma_real
  have hgammaTriple_le : (gammaTriple : ℝ) ≤ gamma := by
    have hgt_max : (gammaTriple : ℝ) ≤ (max gammaPair gammaTriple : ℝ) := by
      exact_mod_cast (le_max_right gammaPair gammaTriple)
    exact hgt_max.trans hgamma_real
  have hgammaR_le_gammaPair : gammaR ≤ (gammaPair : ℝ) := by
    exact (le_max_left gammaR L).trans hgammaPair_ge
  have hL_le_gammaPair : L ≤ (gammaPair : ℝ) := by
    exact (le_max_right gammaR L).trans hgammaPair_ge
  have hgammaR_le_gamma : gammaR ≤ gamma := hgammaR_le_gammaPair.trans hgammaPair_le
  have hL_le_gamma : L ≤ gamma := hL_le_gammaPair.trans hgammaPair_le
  rcases hlarge_pair Delta hDeltaPair with
    ⟨hgammaR_lt_Delta, hL_lt_Delta, hlarge_gammaR, hlarge_L⟩
  have hDelta_pos_real : 0 < (Delta : ℝ) :=
    lt_of_le_of_lt hgammaR_nonneg hgammaR_lt_Delta
  have hDelta_pos_nat : 0 < Delta := by exact_mod_cast hDelta_pos_real
  have hgamma_le_Delta : gamma ≤ (Delta : ℝ) :=
    RandomIndependentSetSamplingGammaLeDelta G ⟨r⟩ hDelta_pos_nat hsampling
  let C : Finset V → Finset V := fun P : Finset V =>
    Finset.univ.filter fun w : V => ∀ u : V, u ∈ P → G.Adj u w
  let lambda : Finset V → ℝ := fun P : Finset V =>
    ((Delta - (C P).card : ℕ) : ℝ) / (Delta : ℝ)
  let ell : Finset V → ℝ := fun P : Finset V =>
    ((C P).card : ℝ) / (Delta : ℝ)
  let W : Finset V → ℝ := fun P : Finset V =>
    2 / ((2 - ell P) * (1 - ell P)) - 1
  have hpair_lower :
      (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) ≥
        (J2.card : ℝ) / (Delta : ℝ)^2 +
          (1 / (3 * (Delta : ℝ)^2)) *
            (∑ P : Finset V, if P ∈ J2 then
              lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
            else 0) -
          3 * alpha := by
    simpa [J2, C, lambda] using
      (SamplingPairBonferroniPairLowerBound alpha L gammaR
        halpha_pos halpha_le_one halpha_one_pos hL_nonneg hgammaR_nonneg
        htail hnumeric Delta gamma hDelta_pos_real hL_le_gamma hgammaR_le_gamma
        hgamma_le_Delta hgammaR_lt_Delta hL_lt_Delta hlarge_gammaR hlarge_L
        G hregular μ hsampling r X hX hclean)
  have hell :
      ∀ P : Finset V,
        P.card = 2 → P ⊆ X →
          (∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b) →
            ∃ u : V, ∃ v : V,
              u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                ell P =
                  ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) /
                    (Delta : ℝ) := by
    intro P hPcard _hPX _hPind
    rcases Finset.card_eq_two.mp hPcard with ⟨u, v, huv, hPuv⟩
    refine ⟨u, v, ?_, ?_, huv, ?_⟩
    · simp [hPuv]
    · simp [hPuv]
    · have hC_eq : C P = G.neighborFinset u ∩ G.neighborFinset v := by
        ext w
        simp [C, hPuv, SimpleGraph.mem_neighborFinset]
      simp [ell, hC_eq]
  have htriple_upper :
      (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) ≤
        ((J3.card : ℝ) / (Delta : ℝ)^3) +
          (1 / (3 * (Delta : ℝ)^3)) *
            (∑ Q : Finset V,
              if Q ∈ J3 then
                ∑ P : Finset V,
                  if P.card = 2 ∧ P ⊆ Q then
                    W P
                  else 0
              else 0) + eta / 3 := by
    simpa [J3, ell, W] using
      (htriple_est Delta gamma hDeltaTriple hgammaTriple_le G hregular μ hsampling
        r X hX hclean ell hell)
  have hW_nonneg : ∀ P : Finset V, P ∈ J2 → 0 ≤ W P := by
    intro P hPJ2
    have hPdata := Finset.mem_filter.mp hPJ2
    have hPcard : P.card = 2 := by simpa [J2] using hPdata.2.1
    have hPX : P ⊆ X := by simpa [J2] using hPdata.2.2.1
    have hPind :
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b := by
      intro a ha b hb hab
      exact hPdata.2.2.2 ha hb hab
    rcases SamplingCleanPairEllPositivity G Delta hregular r X P P hX hclean hPX hPind
        hPcard (fun x hx => hx) ell hell with
      ⟨hell_nonneg, hone_pos, htwo_pos⟩
    have hden_pos : 0 < (2 - ell P) * (1 - ell P) := mul_pos htwo_pos hone_pos
    have hden_le_two : (2 - ell P) * (1 - ell P) ≤ 2 := by
      have hone_le : 1 - ell P ≤ 1 := by linarith
      have htwo_le : 2 - ell P ≤ 2 := by linarith
      nlinarith [mul_le_mul htwo_le hone_le (by linarith) (by linarith : 0 ≤ (2 : ℝ))]
    have hone_le_div : 1 ≤ 2 / ((2 - ell P) * (1 - ell P)) := by
      rw [le_div_iff₀ hden_pos]
      linarith
    dsimp [W]
    linarith
  have hreindex :
      (∑ Q : Finset V, if Q ∈ J3 then
          ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
        else 0) ≤
        ∑ P : Finset V, if P ∈ J2 then ((Delta - (C P).card : ℕ) : ℝ) * W P else 0 := by
    simpa [J2, J3, C] using
      (SamplingTripleCorrectionReindexing G Delta hregular r X hX hclean W hW_nonneg)
  have hlambda_eq : ∀ P : Finset V, P ∈ J2 → lambda P = 1 - ell P := by
    intro P hPJ2
    have hPdata := Finset.mem_filter.mp hPJ2
    have hPcard : P.card = 2 := by simpa [J2] using hPdata.2.1
    have hPX : P ⊆ X := by simpa [J2] using hPdata.2.2.1
    have hPind :
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b := by
      intro a ha b hb hab
      exact hPdata.2.2.2 ha hb hab
    rcases SamplingCleanPairEllPositivity G Delta hregular r X P P hX hclean hPX hPind
        hPcard (fun x hx => hx) ell hell with
      ⟨_hell_nonneg, hone_pos, _htwo_pos⟩
    have hell_lt_one : ell P < 1 := by linarith
    have hC_le_Delta_real : ((C P).card : ℝ) ≤ (Delta : ℝ) := by
      have := div_lt_one hDelta_pos_real |>.mp hell_lt_one
      simpa [ell] using le_of_lt this
    have hC_le_Delta_nat : (C P).card ≤ Delta := by exact_mod_cast hC_le_Delta_real
    dsimp [lambda, ell]
    rw [Nat.cast_sub hC_le_Delta_nat]
    field_simp [ne_of_gt hDelta_pos_real]
  have hcorr_eq :
      (∑ P : Finset V, if P ∈ J2 then
        lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
      else 0) =
        (∑ P : Finset V, if P ∈ J2 then
          (Delta : ℝ)⁻¹ * (((Delta - (C P).card : ℕ) : ℝ) * W P)
        else 0) := by
    apply Finset.sum_congr rfl
    intro P _hP
    by_cases hPJ2 : P ∈ J2
    · have hleq := hlambda_eq P hPJ2
      have hlpos : 0 < lambda P := by
        rw [hleq]
        exact (SamplingCleanPairEllPositivity G Delta hregular r X P P hX hclean
          (by
            have hPdata := Finset.mem_filter.mp hPJ2
            simpa [J2] using hPdata.2.2.1)
          (by
            have hPdata := Finset.mem_filter.mp hPJ2
            intro a ha b hb hab
            exact hPdata.2.2.2 ha hb hab)
          (by
            have hPdata := Finset.mem_filter.mp hPJ2
            simpa [J2] using hPdata.2.1)
          (fun x hx => hx) ell hell).2.1
      have hDelta_ne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_pos_real
      have hmul : ((Delta - (C P).card : ℕ) : ℝ) = (Delta : ℝ) * lambda P := by
        dsimp [lambda]
        field_simp [hDelta_ne]
      simp [hPJ2, W, hleq, hmul]
      field_simp [hDelta_ne, ne_of_gt hlpos]
      ring
    · simp [hPJ2]
  have htriple_corr_bound :
      (1 / (3 * (Delta : ℝ)^3)) *
          (∑ Q : Finset V, if Q ∈ J3 then
            ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
          else 0) ≤
        (1 / (3 * (Delta : ℝ)^2)) *
          (∑ P : Finset V, if P ∈ J2 then
            lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
          else 0) := by
    have hcoef_nonneg : 0 ≤ 1 / (3 * (Delta : ℝ)^3) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hreindex hcoef_nonneg
    have hrewrite_rhs :
        (1 / (3 * (Delta : ℝ)^3)) *
            (∑ P : Finset V, if P ∈ J2 then ((Delta - (C P).card : ℕ) : ℝ) * W P else 0) =
          (1 / (3 * (Delta : ℝ)^2)) *
            (∑ P : Finset V, if P ∈ J2 then
              lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
            else 0) := by
      rw [hcorr_eq]
      have hsum_inv :
          (∑ P : Finset V, if P ∈ J2 then
            (Delta : ℝ)⁻¹ * (((Delta - (C P).card : ℕ) : ℝ) * W P)
          else 0) =
            (Delta : ℝ)⁻¹ *
              (∑ P : Finset V, if P ∈ J2 then
                ((Delta - (C P).card : ℕ) : ℝ) * W P
              else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P _hP
        by_cases hPJ2 : P ∈ J2 <;> simp [hPJ2]
      rw [hsum_inv]
      have hDelta_ne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_pos_real
      field_simp [hDelta_ne]
    calc
      (1 / (3 * (Delta : ℝ)^3)) *
          (∑ Q : Finset V, if Q ∈ J3 then
            ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
          else 0)
          ≤ (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V, if P ∈ J2 then
                ((Delta - (C P).card : ℕ) : ℝ) * W P
              else 0) := hscaled
      _ = (1 / (3 * (Delta : ℝ)^2)) *
          (∑ P : Finset V, if P ∈ J2 then
            lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
          else 0) := hrewrite_rhs
  have herrors : 3 * alpha + eta / 3 ≤ eta := by
    linarith
  linarith [hpair_lower, htriple_upper, htriple_corr_bound, herrors]
