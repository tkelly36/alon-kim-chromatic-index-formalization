import Tablet.RandomIndependentSetSampling
import Tablet.SamplingFixedPairChamberSurvival
import Tablet.SamplingPairPushForwardEvent

open BigOperators

-- [TABLET NODE: SamplingPairExposureEstimate]
theorem SamplingPairExposureEstimate :
    ∀ Delta : ℕ, ∀ gamma : ℝ,
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
              ∃ K : Finset V → ℝ,
                (∀ P : Finset V, P ∈ J2 →
                  ∃ u : V, ∃ v : V,
                    u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                      K P =
                        (2 / (Delta : ℝ)^2) *
                          ∫ x in (0 : ℝ)..gamma,
                            ∫ y in x..gamma,
                              (1 - x / (Delta : ℝ)) ^
                                  (Delta -
                                    (G.neighborFinset u ∩ G.neighborFinset v).card) *
                                (1 - y / (Delta : ℝ)) ^
                                  Delta) ∧
                (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ)) =
                  ∑ P : Finset V, if P ∈ J2 then K P else 0 := by
-- BODY
  classical
  intro Delta gamma V _ _ G _ hregular μ hsampling r X hX hclean
  let J2 : Finset (Finset V) :=
    Finset.univ.filter fun P : Finset V =>
      P.card = 2 ∧ P ⊆ X ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b
  let pairWitness : Finset V → Prop := fun P : Finset V =>
    ∃ u : V, ∃ v : V, u ∈ P ∧ v ∈ P ∧ u ≠ v
  let kernel : V → V → ℝ := fun u v =>
    (2 / (Delta : ℝ)^2) *
      ∫ x in (0 : ℝ)..gamma,
        ∫ y in x..gamma,
          (1 - x / (Delta : ℝ)) ^
              (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
            (1 - y / (Delta : ℝ)) ^ Delta
  let K : Finset V → ℝ := fun P =>
    if hP : pairWitness P then
      kernel (Classical.choose hP)
        (Classical.choose (Classical.choose_spec hP))
    else 0
  have hpair_pushforward :
      ∃ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
        ∀ u v : V,
          ENNReal.ofReal
              (∑ S : Finset V, if ({u, v} : Finset V) ⊆ S then μ S else 0) =
            ν {ω |
              ({u, v} : Finset V) ⊆
                (Finset.univ.filter fun z : V =>
                  z ∈ ω.1 ∧
                    ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} := by
    rcases hsampling with
      ⟨_hgamma, hμmass, ν, _hνuniv, _hbern, _hcube, _hrect, _hcompare,
        hpush, _hind⟩
    exact ⟨ν, fun u v => SamplingPairPushForwardEvent G μ ν hμmass.1 hpush u v⟩
  refine ⟨K, ?_, ?_⟩
  · intro P hP
    have hP_mem : P ∈ J2 := hP
    have hP_card : P.card = 2 := by
      simpa [J2] using (Finset.mem_filter.mp hP_mem).2.1
    obtain ⟨u, v, huv⟩ := Finset.card_eq_two.mp hP_card
    have huP : u ∈ P := by simp [huv]
    have hvP : v ∈ P := by simp [huv]
    have huv_ne : u ≠ v := by
      intro hsame
      subst v
      simp at huv
    have hpw : pairWitness P := ⟨u, v, huP, hvP, huv_ne⟩
    refine ⟨Classical.choose hpw, Classical.choose (Classical.choose_spec hpw), ?_⟩
    have hspec₁ := Classical.choose_spec hpw
    have hspec₂ := Classical.choose_spec hspec₁
    refine ⟨hspec₂.1, hspec₂.2.1, hspec₂.2.2, ?_⟩
    change K P = kernel (Classical.choose hpw) (Classical.choose hspec₁)
    dsimp [K]
    rw [dif_pos hpw]
  · have hμ_nonneg : ∀ S : Finset V, 0 ≤ μ S := by
      rcases hsampling with ⟨_hgamma, hμmass, _⟩
      exact hμmass.1
    have hμ_ind :
        ∀ S : Finset V, μ S ≠ 0 →
          ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v := by
      rcases hsampling with
        ⟨_hgamma, _hμmass, _ν, _hνuniv, _hbern, _hcube, _hrect, _hcompare,
          _hpush, hind⟩
      exact hind
    have hK_value :
        ∀ P : Finset V, P ∈ J2 →
          K P = ∑ S : Finset V, if P ⊆ S then μ S else 0 := by
      intro P hP
      have hP_card : P.card = 2 := by
        simpa [J2] using (Finset.mem_filter.mp hP).2.1
      obtain ⟨u, v, huv⟩ := Finset.card_eq_two.mp hP_card
      have huP : u ∈ P := by simp [huv]
      have hvP : v ∈ P := by simp [huv]
      have huv_ne : u ≠ v := by
        intro hsame
        subst v
        simp at huv
      have hPX : P ⊆ X := by
        simpa [J2] using (Finset.mem_filter.mp hP).2.2.1
      have huX : u ∈ X := hPX huP
      have hvX : v ∈ X := hPX hvP
      have huv_nonadj : ¬ G.Adj u v := by
        exact (Finset.mem_filter.mp hP).2.2.2 huP hvP huv_ne
      have hpw : pairWitness P := ⟨u, v, huP, hvP, huv_ne⟩
      have hspec₁ := Classical.choose_spec hpw
      have hspec₂ := Classical.choose_spec hspec₁
      have hchoose_set :
          ({Classical.choose hpw, Classical.choose hspec₁} : Finset V) = P := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hspec₂.1
          · exact hspec₂.2.1
        · rw [hP_card, Finset.card_pair hspec₂.2.2]
      have hchosen_X₁ : Classical.choose hpw ∈ X := hPX hspec₂.1
      have hchosen_X₂ : Classical.choose hspec₁ ∈ X := hPX hspec₂.2.1
      have hchosen_nonadj : ¬ G.Adj (Classical.choose hpw) (Classical.choose hspec₁) := by
        exact (Finset.mem_filter.mp hP).2.2.2 hspec₂.1 hspec₂.2.1 hspec₂.2.2
      have hsurv :=
        SamplingFixedPairChamberSurvival Delta gamma G hregular μ hsampling r X hX hclean
          (Classical.choose hpw) hchosen_X₁ (Classical.choose hspec₁) hchosen_X₂
          hspec₂.2.2 hchosen_nonadj
      have hK :
          K P =
            (2 / (Delta : ℝ)^2) *
              ∫ x in (0 : ℝ)..gamma,
                ∫ y in x..gamma,
                  (1 - x / (Delta : ℝ)) ^
                      (Delta -
                        (G.neighborFinset (Classical.choose hpw) ∩
                          G.neighborFinset (Classical.choose hspec₁)).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta := by
        change K P = kernel (Classical.choose hpw) (Classical.choose hspec₁)
        dsimp [K]
        rw [dif_pos hpw]
      rw [hK, ← hsurv]
      apply Finset.sum_congr rfl
      intro S _hS
      rw [hchoose_set]
    have hpair_count :
        ∀ S : Finset V,
          μ S * (Nat.choose (S ∩ X).card 2 : ℝ) =
            μ S * ∑ P : Finset V, if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0 := by
      intro S
      by_cases hzero : μ S = 0
      · simp [hzero]
      · have hfilter_eq :
            J2.filter (fun P : Finset V => P ⊆ S) = (S ∩ X).powersetCard 2 := by
          ext P
          constructor
          · intro hP
            have hPJ2 : P ∈ J2 := (Finset.mem_filter.mp hP).1
            have hPS : P ⊆ S := (Finset.mem_filter.mp hP).2
            have hP_card : P.card = 2 := by
              simpa [J2] using (Finset.mem_filter.mp hPJ2).2.1
            have hPX : P ⊆ X := by
              simpa [J2] using (Finset.mem_filter.mp hPJ2).2.2.1
            exact Finset.mem_powersetCard.mpr
              ⟨fun z hz => by simp [hPS hz, hPX hz], hP_card⟩
          · intro hP
            have hPsub : P ⊆ S ∩ X := (Finset.mem_powersetCard.mp hP).1
            have hP_card : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
            have hPS : P ⊆ S := fun z hz => by
              exact (Finset.mem_inter.mp (hPsub hz)).1
            have hPX : P ⊆ X := fun z hz => by
              exact (Finset.mem_inter.mp (hPsub hz)).2
            have hindP :
                ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b := by
              intro a ha b hb hab
              exact hμ_ind S hzero (hPS ha) (hPS hb) hab
            exact Finset.mem_filter.mpr
              ⟨by
                simp only [J2, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hP_card, hPX, by
                  intro a ha b hb hab
                  exact hindP ha hb hab⟩,
                hPS⟩
        have hsum_ones :
            (∑ P : Finset V, if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0) =
              ((J2.filter (fun P : Finset V => P ⊆ S)).card : ℝ) := by
          let T : Finset (Finset V) :=
            (Finset.univ : Finset (Finset V)).filter
              (fun P : Finset V => P ∈ J2 ∧ P ⊆ S)
          have hT_eq : T = J2.filter (fun P : Finset V => P ⊆ S) := by
            ext P
            simp [T]
          calc
            (∑ P : Finset V, if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0)
                = Finset.sum T (fun _P : Finset V => (1 : ℝ)) := by
                  dsimp [T]
                  rw [Finset.sum_filter]
            _ = (T.card : ℝ) := by
                  simp
            _ = ((J2.filter (fun P : Finset V => P ⊆ S)).card : ℝ) := by
                  rw [hT_eq]
        rw [hsum_ones, hfilter_eq, Finset.card_powersetCard]
    calc
      (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 2 : ℝ))
          = ∑ S : Finset V,
              μ S * ∑ P : Finset V, if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro S _hS
            exact hpair_count S
      _ = ∑ P : Finset V, ∑ S : Finset V,
              μ S * if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0 := by
            calc
              (∑ S : Finset V,
                  μ S * ∑ P : Finset V, if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0)
                  = ∑ S : Finset V, ∑ P : Finset V,
                      μ S * if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0 := by
                    apply Finset.sum_congr rfl
                    intro S _hS
                    rw [Finset.mul_sum]
              _ = ∑ P : Finset V, ∑ S : Finset V,
                      μ S * if P ∈ J2 ∧ P ⊆ S then (1 : ℝ) else 0 := by
                    rw [Finset.sum_comm]
      _ = ∑ P : Finset V, if P ∈ J2 then K P else 0 := by
            apply Finset.sum_congr rfl
            intro P _hP
            by_cases hPJ2 : P ∈ J2
            · rw [if_pos hPJ2, hK_value P hPJ2]
              apply Finset.sum_congr rfl
              intro S _hS
              by_cases hPS : P ⊆ S
              · simp [hPJ2, hPS]
              · simp [hPJ2, hPS]
            · rw [if_neg hPJ2]
              simp [hPJ2]
