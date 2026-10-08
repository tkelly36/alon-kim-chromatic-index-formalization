import Tablet.RandomIndependentSetSampling
import Tablet.SamplingIndependentPairsHalfDegreeSquare
import Tablet.SamplingPairHighOverlapExponentialWindowMargin
import Tablet.SamplingPairHighOverlapFiniteProductWindowLower
import Tablet.SamplingPairKernelSplitLowerBound
import Tablet.SamplingPairLowOverlapExponentialWindowMargin
import Tablet.SamplingPairLowOverlapWindowLower
import Tablet.SamplingPairExposureEstimate

open BigOperators

set_option maxHeartbeats 2000000

-- [TABLET NODE: SamplingPairBonferroniPairLowerBound]
theorem SamplingPairBonferroniPairLowerBound
    (alpha L gamma0 : ℝ)
    (halpha_pos : 0 < alpha)
    (halpha_le_one : alpha ≤ 1)
    (halpha_one_pos : 0 < 1 - alpha)
    (hL_nonneg : 0 ≤ L)
    (hgamma0_nonneg : 0 ≤ gamma0)
    (htail : Real.exp (-gamma0) * (1 + 1 / alpha) ≤ alpha)
    (hnumeric :
      (5 / 3 + 2 * alpha) ≤
        2 * ((1 - alpha)^2 * Real.exp (-(alpha * L)) *
          (∫ x in (0 : ℝ)..L, Real.exp (-x) - Real.exp (-L))))
    (Delta : ℕ) (gamma : ℝ)
    (hD : 0 < (Delta : ℝ))
    (hL_le_gamma : L ≤ gamma)
    (hgamma0_le_gamma : gamma0 ≤ gamma)
    (hgamma_le : gamma ≤ (Delta : ℝ))
    (hgamma0_lt : gamma0 < (Delta : ℝ))
    (hL_lt : L < (Delta : ℝ))
    (hlarge_gamma0 :
      gamma0^2 / ((Delta : ℝ) - gamma0) ≤ - Real.log (1 - alpha))
    (hlarge_L :
      L^2 / ((Delta : ℝ) - L) ≤ - Real.log (1 - alpha)) :
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
            let C : Finset V → Finset V := fun P : Finset V =>
              Finset.univ.filter fun w : V => ∀ u : V, u ∈ P → G.Adj u w
            let lambda : Finset V → ℝ := fun P : Finset V =>
              ((Delta - (C P).card : ℕ) : ℝ) / (Delta : ℝ)
            (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) ≥
              (J2.card : ℝ) / (Delta : ℝ)^2 +
                (1 / (3 * (Delta : ℝ)^2)) *
                  (∑ P : Finset V, if P ∈ J2 then
                    lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
                  else 0) -
                3 * alpha := by
-- BODY
  classical
  intro V _ _ G _ hregular μ hsampling r X hX hclean J2 C lambda
  rcases SamplingPairExposureEstimate Delta gamma G hregular μ hsampling r X hX hclean with
    ⟨K, hKspec, hpair_sum⟩
  have hDelta_nonneg : 0 ≤ (Delta : ℝ) := le_of_lt hD
  have hDsq_pos : 0 < (Delta : ℝ)^2 := sq_pos_of_pos hD
  have hhigh_margin :
      (5 / 3 + 2 * alpha) ≤
        2 *
          (∫ x in (0 : ℝ)..L,
            ∫ y in x..L,
              ((1 - alpha) * Real.exp (-(alpha * L))) *
                ((1 - alpha) * Real.exp (-y))) :=
    SamplingPairHighOverlapExponentialWindowMargin L alpha hnumeric
  have hpair_card_bound :
      (J2.card : ℝ) ≤ (Delta : ℝ)^2 / 2 := by
    simpa [J2] using SamplingIndependentPairsHalfDegreeSquare G Delta r X hregular hX
  have hC_eq_inter :
      ∀ P : Finset V, P ∈ J2 → ∀ u v : V,
        u ∈ P → v ∈ P → u ≠ v →
          C P = G.neighborFinset u ∩ G.neighborFinset v := by
    intro P hP u v huP hvP huv
    have hPcard : P.card = 2 := by
      simpa [J2] using (Finset.mem_filter.mp hP).2.1
    have hPuv : P = ({u, v} : Finset V) := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hzP
        by_contra hznot
        have hu_ne_z : u ≠ z := by
          intro h; subst z; exact hznot (by simp)
        have hv_ne_z : v ≠ z := by
          intro h; subst z; exact hznot (by simp)
        have hthree_sub : ({u, v, z} : Finset V) ⊆ P := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> assumption
        have hthree_card : ({u, v, z} : Finset V).card = 3 := by
          simp [huv, hu_ne_z, hv_ne_z]
        have : 3 ≤ P.card := by
          calc
            3 = ({u, v, z} : Finset V).card := hthree_card.symm
            _ ≤ P.card := Finset.card_le_card hthree_sub
        omega
      · rw [hPcard]
        exact Finset.card_le_two
    ext w
    simp [C, hPuv, SimpleGraph.mem_neighborFinset]
  have hlambda_pos :
      ∀ P : Finset V, P ∈ J2 → 0 < lambda P := by
    intro P hP
    rcases hKspec P hP with ⟨u, v, huP, hvP, huv, _hK⟩
    have hPdata := Finset.mem_filter.mp hP
    have hPX : P ⊆ X := by simpa [J2] using hPdata.2.2.1
    have huX : u ∈ X := hPX huP
    have hvX : v ∈ X := hPX hvP
    have hur_adj : G.Adj r u := hX u huX
    have hvr_adj : G.Adj r v := hX v hvX
    have hur_mem : u ∈ G.neighborFinset r := by
      simpa [SimpleGraph.mem_neighborFinset] using hur_adj
    have hvr_mem : v ∈ G.neighborFinset r := by
      simpa [SimpleGraph.mem_neighborFinset] using hvr_adj
    have hpair_sub : ({u, v} : Finset V) ⊆ G.neighborFinset r := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hur_mem
      · exact hvr_mem
    have hDelta_two : 2 ≤ Delta := by
      have hcard_le : ({u, v} : Finset V).card ≤ (G.neighborFinset r).card :=
        Finset.card_le_card hpair_sub
      have hpair_card : ({u, v} : Finset V).card = 2 := by
        simp [huv]
      rw [hpair_card, SimpleGraph.card_neighborFinset_eq_degree, hregular r] at hcard_le
      exact hcard_le
    let Cuv : Finset V := G.neighborFinset u ∩ G.neighborFinset v
    let T : Finset V := insert r (G.neighborFinset r \ ({u, v} : Finset V))
    have hCsub : Cuv ⊆ T := by
      intro w hwC
      have huw_adj : G.Adj u w := by
        simpa [Cuv, SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hwC).1
      have hvw_adj : G.Adj v w := by
        simpa [Cuv, SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hwC).2
      by_cases hwr : w = r
      · simp [T, hwr]
      · have hrw_adj : G.Adj r w := by
          by_contra hnot
          exact (hclean u huX v hvX huv) ⟨w, huw_adj, hvw_adj, hwr, hnot⟩
        have hwr_ne_u : w ≠ u := (G.ne_of_adj huw_adj).symm
        have hwr_ne_v : w ≠ v := (G.ne_of_adj hvw_adj).symm
        have hw_nei : w ∈ G.neighborFinset r := by
          simpa [SimpleGraph.mem_neighborFinset] using hrw_adj
        have hw_not_pair : w ∉ ({u, v} : Finset V) := by
          simp [hwr_ne_u, hwr_ne_v]
        simp [T, hw_nei, hw_not_pair]
    have hT_card : T.card = Delta - 1 := by
      have hr_not_nei : r ∉ G.neighborFinset r := by
        simp [SimpleGraph.mem_neighborFinset]
      have hr_not_diff : r ∉ G.neighborFinset r \ ({u, v} : Finset V) := by
        simp [hr_not_nei]
      have hdiff :
          (G.neighborFinset r \ ({u, v} : Finset V)).card = Delta - 2 := by
        rw [Finset.card_sdiff_of_subset hpair_sub]
        simp [SimpleGraph.card_neighborFinset_eq_degree, hregular r, huv]
      dsimp [T]
      rw [Finset.card_insert_of_notMem hr_not_diff, hdiff]
      omega
    have hC_card_lt : (C P).card < Delta := by
      have hCP_eq : C P = Cuv := hC_eq_inter P hP u v huP hvP huv
      have hCuv_card_le : Cuv.card ≤ Delta - 1 := by
        calc
          Cuv.card ≤ T.card := Finset.card_le_card hCsub
          _ = Delta - 1 := hT_card
      rw [hCP_eq]
      omega
    have hsub_pos : 0 < Delta - (C P).card := Nat.sub_pos_of_lt hC_card_lt
    have hcast_pos : 0 < ((Delta - (C P).card : ℕ) : ℝ) := by
      exact_mod_cast hsub_pos
    dsimp [lambda]
    exact div_pos hcast_pos hD
  have hlambda_le_one :
      ∀ P : Finset V, P ∈ J2 → lambda P ≤ 1 := by
    intro P hP
    dsimp [lambda]
    have hnum_le : ((Delta - (C P).card : ℕ) : ℝ) ≤ (Delta : ℝ) := by
      exact_mod_cast Nat.sub_le Delta (C P).card
    exact (div_le_one hD).2 hnum_le
  have hK_lower :
      ∀ P : Finset V, P ∈ J2 →
        K P ≥
          (1 + (1 / 3) * lambda P *
                (2 / (lambda P * (1 + lambda P)) - 1)) / (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2 := by
    intro P hP
    rcases hKspec P hP with ⟨u, v, huP, hvP, huv, hK⟩
    let N : ℕ := Delta - (G.neighborFinset u ∩ G.neighborFinset v).card
    have hCP_eq : C P = G.neighborFinset u ∩ G.neighborFinset v :=
      hC_eq_inter P hP u v huP hvP huv
    have hlambda_eq : lambda P = (N : ℝ) / (Delta : ℝ) := by
      dsimp [lambda, N]
      rw [hCP_eq]
    rw [hK]
    have hN_le : (N : ℝ) ≤ (Delta : ℝ) := by
      dsimp [N]
      exact_mod_cast Nat.sub_le Delta (G.neighborFinset u ∩ G.neighborFinset v).card
    refine SamplingPairKernelSplitLowerBound Delta alpha (lambda P)
      ((2 / (Delta : ℝ)^2) *
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 - x / (Delta : ℝ)) ^ N *
              (1 - y / (Delta : ℝ)) ^ Delta))
      hD halpha_le_one (hlambda_pos P hP) (hlambda_le_one P hP) ?_ ?_
    · intro halpha_le_lambda
      rw [hlambda_eq] at halpha_le_lambda ⊢
      exact SamplingPairLowOverlapWindowLower Delta N gamma gamma0 alpha ((N : ℝ) / (Delta : ℝ))
        hD hgamma0_nonneg hgamma0_le_gamma hgamma_le hgamma0_lt halpha_one_pos hN_le rfl
        hlarge_gamma0
        (SamplingPairLowOverlapExponentialWindowMargin alpha gamma0 ((N : ℝ) / (Delta : ℝ))
          halpha_pos halpha_le_one hgamma0_nonneg halpha_le_lambda
          (by simpa [← hlambda_eq] using hlambda_le_one P hP) htail)
    · intro hlambda_lt_alpha
      rw [hlambda_eq] at hlambda_lt_alpha
      have hN_ratio_le : (N : ℝ) / (Delta : ℝ) ≤ alpha := le_of_lt hlambda_lt_alpha
      have hwindow :=
        SamplingPairHighOverlapFiniteProductWindowLower Delta N L alpha hD hL_nonneg
          hL_lt halpha_one_pos hN_le hN_ratio_le hlarge_L hhigh_margin
      let F : ℝ → ℝ → ℝ := fun x y =>
        (1 - x / (Delta : ℝ)) ^ N * (1 - y / (Delta : ℝ)) ^ Delta
      have hF_cont : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
        dsimp [F]
        fun_prop
      have hF_inner_int (a b x : ℝ) :
          IntervalIntegrable (fun y : ℝ => F x y) MeasureTheory.volume a b := by
        exact ((hF_cont.comp (by fun_prop : Continuous fun y : ℝ => (x, y))).intervalIntegrable a b)
      have hF_outer_cont (b : ℝ) :
          Continuous fun x : ℝ => ∫ y in x..b, F x y := by
        have htop : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..b, F x y :=
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
            (s := fun _x : ℝ => b) hF_cont (by fun_prop)
        have hbot : Continuous fun x : ℝ => ∫ y in (0 : ℝ)..x, F x y :=
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (f := F) (a₀ := (0 : ℝ))
            (s := fun x : ℝ => x) hF_cont (by fun_prop)
        have heq :
            (fun x : ℝ => ∫ y in x..b, F x y) =
              fun x : ℝ => (∫ y in (0 : ℝ)..b, F x y) -
                ∫ y in (0 : ℝ)..x, F x y := by
          ext x
          exact (intervalIntegral.integral_interval_sub_left
            (hF_inner_int 0 b x) (hF_inner_int 0 x x)).symm
        rw [heq]
        exact htop.sub hbot
      have hF_outer_int (a b c : ℝ) :
          IntervalIntegrable (fun x : ℝ => ∫ y in x..c, F x y)
            MeasureTheory.volume a b :=
        (hF_outer_cont c).intervalIntegrable a b
      have hF_nonneg_on :
          ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) gamma →
            0 ≤ ∫ y in x..gamma, F x y := by
        intro x hx
        refine intervalIntegral.integral_nonneg hx.2 ?_
        intro y hy
        have hx_le_d : x ≤ (Delta : ℝ) := hx.2.trans hgamma_le
        have hbase_x_nonneg : 0 ≤ 1 - x / (Delta : ℝ) := by
          have hdiv : x / (Delta : ℝ) ≤ 1 := (div_le_one hD).2 hx_le_d
          linarith
        have hbase_y_nonneg : 0 ≤ 1 - y / (Delta : ℝ) := by
          have hyd : y ≤ (Delta : ℝ) := hy.2.trans hgamma_le
          have hdiv : y / (Delta : ℝ) ≤ 1 := (div_le_one hD).2 hyd
          linarith
        exact mul_nonneg (pow_nonneg hbase_x_nonneg _) (pow_nonneg hbase_y_nonneg _)
      have hwindow_finite_le_full :
          (∫ x in (0 : ℝ)..L, ∫ y in x..L, F x y) ≤
            ∫ x in (0 : ℝ)..gamma, ∫ y in x..gamma, F x y := by
        have hinner_mono :
            (∫ x in (0 : ℝ)..L, ∫ y in x..L, F x y) ≤
              ∫ x in (0 : ℝ)..L, ∫ y in x..gamma, F x y := by
          refine intervalIntegral.integral_mono_on hL_nonneg
            (hF_outer_int 0 L L) (hF_outer_int 0 L gamma) ?_
          intro x hx
          refine intervalIntegral.integral_mono_interval
            (f := fun y : ℝ => F x y) (μ := MeasureTheory.volume)
            (a := x) (b := L) (c := x) (d := gamma)
            le_rfl hx.2 hL_le_gamma ?_ (hF_inner_int x gamma x)
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
          have hbase_x_nonneg : 0 ≤ 1 - x / (Delta : ℝ) := by
            have hx_lt_d : x < (Delta : ℝ) := lt_of_le_of_lt hx.2 hL_lt
            have hdiv : x / (Delta : ℝ) ≤ 1 := (div_le_one hD).2 (le_of_lt hx_lt_d)
            linarith
          have hbase_y_nonneg : 0 ≤ 1 - y / (Delta : ℝ) := by
            have hyd : y ≤ (Delta : ℝ) := hy.2.trans hgamma_le
            have hdiv : y / (Delta : ℝ) ≤ 1 := (div_le_one hD).2 hyd
            linarith
          exact mul_nonneg (pow_nonneg hbase_x_nonneg _) (pow_nonneg hbase_y_nonneg _)
        have houter_mono :
            (∫ x in (0 : ℝ)..L, ∫ y in x..gamma, F x y) ≤
              ∫ x in (0 : ℝ)..gamma, ∫ y in x..gamma, F x y := by
          refine intervalIntegral.integral_mono_interval
            (f := fun x : ℝ => ∫ y in x..gamma, F x y) (μ := MeasureTheory.volume)
            (a := (0 : ℝ)) (b := L) (c := (0 : ℝ)) (d := gamma)
            le_rfl hL_nonneg hL_le_gamma ?_ (hF_outer_int 0 gamma gamma)
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hF_nonneg_on x ⟨le_of_lt hx.1, hx.2⟩
        exact hinner_mono.trans houter_mono
      calc
        (2 / (Delta : ℝ)^2) *
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 - x / (Delta : ℝ)) ^ N *
                  (1 - y / (Delta : ℝ)) ^ Delta)
            ≥ (2 / (Delta : ℝ)^2) * (∫ x in (0 : ℝ)..L, ∫ y in x..L, F x y) := by
              gcongr
        _ ≥ (5 / 3 + 2 * alpha) / (Delta : ℝ)^2 := by
              simpa [F] using hwindow
  have hsum_lower :
      (∑ P : Finset V, if P ∈ J2 then K P else 0) ≥
        ∑ P : Finset V, if P ∈ J2 then
          ((1 + (1 / 3) * lambda P *
                (2 / (lambda P * (1 + lambda P)) - 1)) / (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2)
        else 0 := by
    refine Finset.sum_le_sum ?_
    intro P _hP
    by_cases hPJ2 : P ∈ J2
    · rw [if_pos hPJ2, if_pos hPJ2]
      linarith [hK_lower P hPJ2]
    · simp [hPJ2]
  have hsum_expand :
      (∑ P : Finset V, if P ∈ J2 then
          ((1 + (1 / 3) * lambda P *
                (2 / (lambda P * (1 + lambda P)) - 1)) / (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2)
        else 0) =
        (J2.card : ℝ) / (Delta : ℝ)^2 +
          (1 / (3 * (Delta : ℝ)^2)) *
            (∑ P : Finset V, if P ∈ J2 then
              lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
            else 0) -
          (J2.card : ℝ) * ((6 * alpha) / (Delta : ℝ)^2) := by
    let d2 : ℝ := (Delta : ℝ)^2
    let corr : Finset V → ℝ := fun P =>
      lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
    let loss : ℝ := (6 * alpha) / d2
    have hpoint : ∀ P : Finset V,
        (if P ∈ J2 then
          ((1 + (1 / 3) * lambda P *
                (2 / (lambda P * (1 + lambda P)) - 1)) / d2 - loss)
        else 0) =
          (if P ∈ J2 then 1 / d2 else 0) +
            (if P ∈ J2 then (1 / (3 * d2)) * corr P else 0) -
            (if P ∈ J2 then loss else 0) := by
      intro P
      by_cases hP : P ∈ J2
      · simp [hP, corr, loss, d2]
        field_simp [ne_of_gt hDsq_pos]
      · simp [hP]
    simp_rw [show (Delta : ℝ)^2 = d2 by rfl]
    simp_rw [show (6 * alpha / d2) = loss by rfl]
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hones :
        (∑ P : Finset V, if P ∈ J2 then 1 / d2 else 0) =
          (J2.card : ℝ) / d2 := by
      rw [← Finset.sum_filter]
      have hfilter :
          ((Finset.univ : Finset (Finset V)).filter fun P : Finset V => P ∈ J2) = J2 := by
        ext P
        simp
      rw [hfilter]
      simp [div_eq_mul_inv]
    have hcorr :
        (∑ P : Finset V, if P ∈ J2 then (1 / (3 * d2)) * corr P else 0) =
          (1 / (3 * d2)) * (∑ P : Finset V, if P ∈ J2 then corr P else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _hP
      by_cases hP : P ∈ J2 <;> simp [hP]
    have hloss :
        (∑ P : Finset V, if P ∈ J2 then loss else 0) =
          (J2.card : ℝ) * loss := by
      rw [← Finset.sum_filter]
      have hfilter :
          ((Finset.univ : Finset (Finset V)).filter fun P : Finset V => P ∈ J2) = J2 := by
        ext P
        simp
      rw [hfilter]
      simp
    rw [hones, hcorr, hloss]
  calc
    (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ))
        = (∑ P : Finset V, if P ∈ J2 then K P else 0) := by
          simpa [J2] using hpair_sum
    _ ≥ ∑ P : Finset V, if P ∈ J2 then
          ((1 + (1 / 3) * lambda P *
                (2 / (lambda P * (1 + lambda P)) - 1)) / (Delta : ℝ)^2 -
            (6 * alpha) / (Delta : ℝ)^2)
        else 0 := hsum_lower
    _ = (J2.card : ℝ) / (Delta : ℝ)^2 +
          (1 / (3 * (Delta : ℝ)^2)) *
            (∑ P : Finset V, if P ∈ J2 then
              lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
            else 0) -
          (J2.card : ℝ) * ((6 * alpha) / (Delta : ℝ)^2) := hsum_expand
    _ ≥ (J2.card : ℝ) / (Delta : ℝ)^2 +
          (1 / (3 * (Delta : ℝ)^2)) *
            (∑ P : Finset V, if P ∈ J2 then
              lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
            else 0) -
          3 * alpha := by
        have hloss_le :
            (J2.card : ℝ) * ((6 * alpha) / (Delta : ℝ)^2) ≤ 3 * alpha := by
          have hfactor_nonneg : 0 ≤ (6 * alpha) / (Delta : ℝ)^2 := by positivity
          calc
            (J2.card : ℝ) * ((6 * alpha) / (Delta : ℝ)^2)
                ≤ ((Delta : ℝ)^2 / 2) * ((6 * alpha) / (Delta : ℝ)^2) := by
                  exact mul_le_mul_of_nonneg_right hpair_card_bound hfactor_nonneg
            _ = 3 * alpha := by
                  field_simp [ne_of_gt hDsq_pos]
                  ring
        let M : ℝ :=
            (J2.card : ℝ) / (Delta : ℝ)^2 +
              (1 / (3 * (Delta : ℝ)^2)) *
              (∑ P : Finset V, if P ∈ J2 then
                lambda P * (2 / (lambda P * (1 + lambda P)) - 1)
              else 0)
        change M - (J2.card : ℝ) * ((6 * alpha) / (Delta : ℝ)^2) ≥
          M - 3 * alpha
        linarith
