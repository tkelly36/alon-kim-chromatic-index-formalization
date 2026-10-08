import Tablet.RandomIndependentSetSampling
import Tablet.SamplingCleanPairEllPositivity
import Tablet.SamplingActivationENNRealWeightedSumConversion
import Tablet.SamplingFiniteSetActivationPartition
import Tablet.SamplingFiniteSetPushForwardEvent
import Tablet.SamplingTripleActivationChamberSum
import Tablet.SamplingTripleActivationChamberCover
import Tablet.SamplingTripleFixedActivationSixChamberAssembly
import Tablet.SamplingTripleActivationSummedSixChamberBound
import Tablet.SamplingTripleSummedChamberPairBound
import Tablet.SamplingTripleFullChamberIntegralEstimate
import Tablet.SamplingTriplePairedChamberParameterNormalizer
import Tablet.SamplingTriplePatternCountingBridge
import Tablet.SamplingTriplePriorityChamberSurvival
import Tablet.SamplingTripleRealChamberEstimate
import Tablet.SamplingTripleOrderedExponentNormalizer
import Tablet.SamplingThreeSetPairSumNormalizer

open BigOperators

-- [TABLET NODE: SamplingFixedIndependentTripleSurvivalBound]
theorem SamplingFixedIndependentTripleSurvivalBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (μ : Finset V → ℝ)
    (hsample : RandomIndependentSetSampling G Delta gamma μ)
    (hregular : ∀ v : V, G.degree v = Delta)
    (r : V) (X Q : Finset V)
    (hXnbr : ∀ x : V, x ∈ X → G.Adj r x)
    (hclean :
      ∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
        ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w)
    (hQcard : Q.card = 3) (hQX : Q ⊆ X)
    (hQind :
      ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b)
    (ell : Finset V → ℝ)
    (hell :
      ∀ P : Finset V,
        P.card = 2 → P ⊆ X →
          (∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b) →
            ∃ u : V, ∃ v : V,
              u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                ell P =
                  ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) /
                    (Delta : ℝ)) :
    (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
      (1 / (Delta : ℝ)^3) +
        (1 / (3 * (Delta : ℝ)^3)) *
          (∑ P : Finset V,
            if P.card = 2 ∧ P ⊆ Q then
              (2 / ((2 - ell P) * (1 - ell P)) - 1)
            else 0) := by
-- BODY
  have hsample_orig : RandomIndependentSetSampling G Delta gamma μ := hsample
  rcases hsample with ⟨_hgamma_pos, hsample_data, hν⟩
  rcases hsample_data with ⟨hμ_nonneg, _hμ_sum, _hpairlaw⟩
  rcases hν with
    ⟨ν, _hν_univ, _hactivation, _hcube, _hlower_rect, _hone_vertex,
      hpush, _hind_support⟩
  have hpush_Q :
      ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) =
        ν {ω |
          Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} := by
    exact SamplingFiniteSetPushForwardEvent G μ ν hμ_nonneg hpush Q
  have hactivation_partition :
      ν {ω |
          Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
        ∑ A : Finset V,
          if Q ⊆ A then
            ν {ω |
              ω.1 = A ∧
                ∀ q : V, q ∈ Q →
                  ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
          else 0 := by
    exact (SamplingFiniteSetActivationPartition G ν Q).1
  have hactivation_characterization :
      ∀ A : Finset V, ∀ π : V → ℝ,
        Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ A ∧
                ∀ w : V, w ∈ A → G.Adj z w → π w < π z) ↔
          Q ⊆ A ∧
            ∀ q : V, q ∈ Q →
              ∀ w : V, w ∈ A → G.Adj q w → π w < π q := by
    exact (SamplingFiniteSetActivationPartition G ν Q).2
  have hell_pair_positive :
      ∀ P : Finset V, P.card = 2 → P ⊆ Q →
        0 ≤ ell P ∧ 0 < 1 - ell P ∧ 0 < 2 - ell P := by
    intro P hPcard hPQ
    exact
      SamplingCleanPairEllPositivity (G := G) (Delta := Delta) hregular r X Q P
        hXnbr hclean hQX hQind hPcard hPQ ell hell
  have htriple_pattern_counting :
      ∀ a : V, a ∈ Q → ∀ b : V, b ∈ Q → ∀ c : V, c ∈ Q →
        a ≠ b → a ≠ c → b ≠ c →
          let Qabc : Finset V := {a, b, c}
          let n_a : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card
          let n_b : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
          let n_c : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
          let n_ab : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
          let n_ac : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
          let n_bc : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
          let n_abc : ℕ :=
            ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
          ell ({a, b} : Finset V) =
              ((n_ab + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
            ell ({a, c} : Finset V) =
              ((n_ac + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
            ell ({b, c} : Finset V) =
              ((n_bc + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
            n_a + n_ab + n_ac + n_abc = Delta ∧
            n_b + n_ab + n_bc + n_abc = Delta ∧
            n_c + n_ac + n_bc + n_abc = Delta ∧
            n_b + n_bc = Delta - n_ab - n_abc ∧
            n_c = Delta - n_ac - n_bc - n_abc ∧
            r ∈ ((Finset.univ : Finset V).filter fun w : V =>
              w ∉ Qabc ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w) := by
    intro a ha b hb c hc hab hac hbc
    exact
      SamplingTriplePatternCountingBridge (G := G) (Delta := Delta) hregular r X a b c
        (hQX ha) (hQX hb) (hQX hc) hXnbr hclean hab hac hbc
        (hQind ha hb hab) (hQind ha hc hac) (hQind hb hc hbc) ell hell
  classical
  let F : Finset V → ℝ := fun P =>
    2 / ((2 - ell P) * (1 - ell P)) - 1
  rcases SamplingThreeSetPairSumNormalizer Q hQcard F with
    ⟨a, b, c, haQ, hbQ, hcQ, hab, hac, hbc, hQ, _hpairs, hpair_sum⟩
  have hab_ind : ¬ G.Adj a b := hQind haQ hbQ hab
  have hac_ind : ¬ G.Adj a c := hQind haQ hcQ hac
  have hbc_ind : ¬ G.Adj b c := hQind hbQ hcQ hbc
  have hDelta_pos_nat : 0 < Delta := by
    have haX : a ∈ X := hQX haQ
    have har : G.Adj a r := G.adj_symm (hXnbr a haX)
    have hr_mem : r ∈ G.neighborFinset a := by
      simpa [SimpleGraph.mem_neighborFinset] using har
    have hcard_pos : 0 < (G.neighborFinset a).card :=
      Finset.card_pos.mpr ⟨r, hr_mem⟩
    simpa [hregular a] using hcard_pos
  have hDelta_pos_real : 0 < (Delta : ℝ) := by
    exact_mod_cast hDelta_pos_nat
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt _hgamma_pos
  have hgamma_le : gamma ≤ (Delta : ℝ) :=
    RandomIndependentSetSamplingGammaLeDelta (G := G) (μ := μ)
      ⟨a⟩ hDelta_pos_nat hsample_orig
  let n_a : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card
  let n_b : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
  let n_c : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
  let n_ab : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
  let n_ac : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
  let n_bc : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
  let n_abc : ℕ :=
    ((Finset.univ : Finset V).filter fun w : V =>
      w ∉ ({a, b, c} : Finset V) ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
  rcases htriple_pattern_counting a haQ b hbQ c hcQ hab hac hbc with
    ⟨hell_ab, hell_ac, hell_bc, hdeg_a, hdeg_b, hdeg_c, _hdeg_b_sub,
      _hdeg_c_sub, _hr_abc⟩
  have h_ab_card : ({a, b} : Finset V).card = 2 := by simp [hab]
  have h_ac_card : ({a, c} : Finset V).card = 2 := by simp [hac]
  have h_bc_card : ({b, c} : Finset V).card = 2 := by simp [hbc]
  have h_ab_sub_Q : ({a, b} : Finset V) ⊆ Q := by
    rw [hQ]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have h_ac_sub_Q : ({a, c} : Finset V) ⊆ Q := by
    rw [hQ]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  have h_bc_sub_Q : ({b, c} : Finset V) ⊆ Q := by
    rw [hQ]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hell_ab_data := hell_pair_positive ({a, b} : Finset V) h_ab_card h_ab_sub_Q
  have hell_ac_data := hell_pair_positive ({a, c} : Finset V) h_ac_card h_ac_sub_Q
  have hell_bc_data := hell_pair_positive ({b, c} : Finset V) h_bc_card h_bc_sub_Q
  have hell_ab_nonneg : 0 ≤ ell ({a, b} : Finset V) := hell_ab_data.1
  have hell_ac_nonneg : 0 ≤ ell ({a, c} : Finset V) := hell_ac_data.1
  have hell_bc_nonneg : 0 ≤ ell ({b, c} : Finset V) := hell_bc_data.1
  have hell_ab_pos : 0 < 1 - ell ({a, b} : Finset V) := hell_ab_data.2.1
  have hell_ac_pos : 0 < 1 - ell ({a, c} : Finset V) := hell_ac_data.2.1
  have hell_bc_pos : 0 < 1 - ell ({b, c} : Finset V) := hell_bc_data.2.1
  have hell_ab_two_pos : 0 < 2 - ell ({a, b} : Finset V) := hell_ab_data.2.2
  have hell_ac_two_pos : 0 < 2 - ell ({a, c} : Finset V) := hell_ac_data.2.2
  have hell_bc_two_pos : 0 < 2 - ell ({b, c} : Finset V) := hell_bc_data.2.2
  have hcount_a : n_a =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card := rfl
  have hcount_b : n_b =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card := rfl
  have hcount_c : n_c =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card := rfl
  have hcount_ab : n_ab =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card := rfl
  have hcount_ac : n_ac =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card := rfl
  have hcount_bc : n_bc =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card := rfl
  have hcount_abc : n_abc =
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ ({a, b, c} : Finset V) ∧
          G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card := rfl
  have hsix_enn :
      ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
        ENNReal.ofReal
          ((∑ t ∈
              ({((a, b, c) : V × V × V), (a, c, b), (b, a, c),
                (b, c, a), (c, a, b), (c, b, a)} : Finset (V × V × V)),
              (1 / (Delta : ℝ) ^ 3) *
                ∫ z in (0 : ℝ)..gamma,
                  ∫ y in z..gamma,
                    ∫ x in y..gamma,
                      (1 - x / (Delta : ℝ)) ^
                          (((Finset.univ : Finset V).filter fun w : V =>
                            w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                              G.Adj t.1 w).card) *
                        (1 - y / (Delta : ℝ)) ^
                          (((Finset.univ : Finset V).filter fun w : V =>
                            w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                              ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                          (1 - z / (Delta : ℝ)) ^
                            (((Finset.univ : Finset V).filter fun w : V =>
                              w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                                ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧
                                  G.Adj t.2.2 w).card))) := by
    have hsix :=
      SamplingTripleActivationSummedSixChamberBound (G := G) (Delta := Delta)
        (gamma := gamma) (μ := μ) hsample_orig hDelta_pos_nat a b c
        hab hac hbc hab_ind hac_ind hbc_ind
    simpa [hQ] using hsix
  have hsix_real :
      (∑ t ∈
          ({((a, b, c) : V × V × V), (a, c, b), (b, a, c),
            (b, c, a), (c, a, b), (c, b, a)} : Finset (V × V × V)),
          (1 / (Delta : ℝ) ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / (Delta : ℝ)) ^
                      (((Finset.univ : Finset V).filter fun w : V =>
                        w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                          G.Adj t.1 w).card) *
                    (1 - y / (Delta : ℝ)) ^
                      (((Finset.univ : Finset V).filter fun w : V =>
                        w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                          ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                      (1 - z / (Delta : ℝ)) ^
                        (((Finset.univ : Finset V).filter fun w : V =>
                          w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                            ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧
                              G.Adj t.2.2 w).card)) ≤
        (1 / (Delta : ℝ) ^ 3) *
          (1 + (1 / 3) *
            ((2 / ((2 - ell ({a, b} : Finset V)) *
                    (1 - ell ({a, b} : Finset V))) - 1) +
              (2 / ((2 - ell ({a, c} : Finset V)) *
                      (1 - ell ({a, c} : Finset V))) - 1) +
                (2 / ((2 - ell ({b, c} : Finset V)) *
                        (1 - ell ({b, c} : Finset V))) - 1))) := by
    exact
      SamplingTripleSummedChamberPairBound (G := G) (Delta := Delta)
        (gamma := gamma) a b c hab hac hbc hab_ind hac_ind hbc_ind
        (ell ({a, b} : Finset V)) (ell ({a, c} : Finset V))
        (ell ({b, c} : Finset V)) n_a n_b n_c n_ab n_ac n_bc n_abc
        hDelta_pos_real hgamma_nonneg hgamma_le
        hell_ab_pos hell_ac_pos hell_bc_pos hcount_a hcount_b hcount_c
        hcount_ab hcount_ac hcount_bc hcount_abc hell_ab hell_ac hell_bc
        hdeg_a hdeg_b hdeg_c
  have hterm_ab_nonneg :
      0 ≤ 2 / ((2 - ell ({a, b} : Finset V)) *
          (1 - ell ({a, b} : Finset V))) - 1 := by
    have hden_pos :
        0 < (2 - ell ({a, b} : Finset V)) *
          (1 - ell ({a, b} : Finset V)) :=
      mul_pos hell_ab_two_pos hell_ab_pos
    have hden_le :
        (2 - ell ({a, b} : Finset V)) *
          (1 - ell ({a, b} : Finset V)) ≤ 2 := by
      nlinarith [hell_ab_nonneg, hell_ab_pos]
    have hone_le :
        (1 : ℝ) ≤ 2 / ((2 - ell ({a, b} : Finset V)) *
          (1 - ell ({a, b} : Finset V))) := by
      rw [le_div_iff₀ hden_pos]
      simpa using hden_le
    linarith
  have hterm_ac_nonneg :
      0 ≤ 2 / ((2 - ell ({a, c} : Finset V)) *
          (1 - ell ({a, c} : Finset V))) - 1 := by
    have hden_pos :
        0 < (2 - ell ({a, c} : Finset V)) *
          (1 - ell ({a, c} : Finset V)) :=
      mul_pos hell_ac_two_pos hell_ac_pos
    have hden_le :
        (2 - ell ({a, c} : Finset V)) *
          (1 - ell ({a, c} : Finset V)) ≤ 2 := by
      nlinarith [hell_ac_nonneg, hell_ac_pos]
    have hone_le :
        (1 : ℝ) ≤ 2 / ((2 - ell ({a, c} : Finset V)) *
          (1 - ell ({a, c} : Finset V))) := by
      rw [le_div_iff₀ hden_pos]
      simpa using hden_le
    linarith
  have hterm_bc_nonneg :
      0 ≤ 2 / ((2 - ell ({b, c} : Finset V)) *
          (1 - ell ({b, c} : Finset V))) - 1 := by
    have hden_pos :
        0 < (2 - ell ({b, c} : Finset V)) *
          (1 - ell ({b, c} : Finset V)) :=
      mul_pos hell_bc_two_pos hell_bc_pos
    have hden_le :
        (2 - ell ({b, c} : Finset V)) *
          (1 - ell ({b, c} : Finset V)) ≤ 2 := by
      nlinarith [hell_bc_nonneg, hell_bc_pos]
    have hone_le :
        (1 : ℝ) ≤ 2 / ((2 - ell ({b, c} : Finset V)) *
          (1 - ell ({b, c} : Finset V))) := by
      rw [le_div_iff₀ hden_pos]
      simpa using hden_le
    linarith
  have hmid_nonneg :
      0 ≤ (1 / (Delta : ℝ) ^ 3) *
          (1 + (1 / 3) *
            ((2 / ((2 - ell ({a, b} : Finset V)) *
                    (1 - ell ({a, b} : Finset V))) - 1) +
              (2 / ((2 - ell ({a, c} : Finset V)) *
                      (1 - ell ({a, c} : Finset V))) - 1) +
                (2 / ((2 - ell ({b, c} : Finset V)) *
                        (1 - ell ({b, c} : Finset V))) - 1))) := by
    have hfactor : 0 ≤ 1 / (Delta : ℝ) ^ 3 := by positivity
    have hinside :
        0 ≤ 1 + (1 / 3) *
          ((2 / ((2 - ell ({a, b} : Finset V)) *
                  (1 - ell ({a, b} : Finset V))) - 1) +
            (2 / ((2 - ell ({a, c} : Finset V)) *
                    (1 - ell ({a, c} : Finset V))) - 1) +
              (2 / ((2 - ell ({b, c} : Finset V)) *
                      (1 - ell ({b, c} : Finset V))) - 1)) := by
      have hsum_nonneg :
          0 ≤
            ((2 / ((2 - ell ({a, b} : Finset V)) *
                    (1 - ell ({a, b} : Finset V))) - 1) +
              (2 / ((2 - ell ({a, c} : Finset V)) *
                      (1 - ell ({a, c} : Finset V))) - 1) +
                (2 / ((2 - ell ({b, c} : Finset V)) *
                        (1 - ell ({b, c} : Finset V))) - 1)) :=
        add_nonneg (add_nonneg hterm_ab_nonneg hterm_ac_nonneg) hterm_bc_nonneg
      exact add_nonneg zero_le_one (mul_nonneg (by norm_num) hsum_nonneg)
    exact mul_nonneg hfactor hinside
  have hfinal_eq :
      (1 / (Delta : ℝ) ^ 3) *
          (1 + (1 / 3) *
            ((2 / ((2 - ell ({a, b} : Finset V)) *
                    (1 - ell ({a, b} : Finset V))) - 1) +
              (2 / ((2 - ell ({a, c} : Finset V)) *
                      (1 - ell ({a, c} : Finset V))) - 1) +
                (2 / ((2 - ell ({b, c} : Finset V)) *
                        (1 - ell ({b, c} : Finset V))) - 1))) =
        (1 / (Delta : ℝ)^3) +
          (1 / (3 * (Delta : ℝ)^3)) *
            (∑ P : Finset V,
              if P.card = 2 ∧ P ⊆ Q then
                (2 / ((2 - ell P) * (1 - ell P)) - 1)
              else 0) := by
    rw [hpair_sum]
    dsimp [F]
    ring
  have hfinal_nonneg :
      0 ≤ (1 / (Delta : ℝ)^3) +
        (1 / (3 * (Delta : ℝ)^3)) *
          (∑ P : Finset V,
            if P.card = 2 ∧ P ⊆ Q then
              (2 / ((2 - ell P) * (1 - ell P)) - 1)
            else 0) := by
    rw [← hfinal_eq]
    exact hmid_nonneg
  have henn_final :
      ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
        ENNReal.ofReal
          ((1 / (Delta : ℝ)^3) +
            (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V,
                if P.card = 2 ∧ P ⊆ Q then
                  (2 / ((2 - ell P) * (1 - ell P)) - 1)
                else 0)) := by
    exact hsix_enn.trans (ENNReal.ofReal_le_ofReal (hsix_real.trans_eq hfinal_eq))
  exact (ENNReal.ofReal_le_ofReal_iff hfinal_nonneg).mp henn_final
