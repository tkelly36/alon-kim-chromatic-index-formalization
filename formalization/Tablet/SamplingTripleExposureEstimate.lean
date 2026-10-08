import Tablet.RandomIndependentSetSampling
import Tablet.SamplingFixedIndependentTripleSurvivalBound
import Tablet.SamplingTripleExpectationByIndependentTriples

open BigOperators

-- [TABLET NODE: SamplingTripleExposureEstimate]
theorem SamplingTripleExposureEstimate (eta : ℝ) (heta : 0 < eta) :
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
              let J3 : Finset (Finset V) :=
                (Finset.univ.filter fun Q : Finset V =>
                  Q.card = 3 ∧ Q ⊆ X ∧
                    ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b)
              ∀ ell : Finset V → ℝ,
                (∀ P : Finset V,
                  P.card = 2 → P ⊆ X →
                    (∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b) →
                      ∃ u : V, ∃ v : V,
                        u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                          ell P =
                            ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) /
                              (Delta : ℝ)) →
              (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ)) ≤
                ((J3.card : ℝ) / (Delta : ℝ)^3) +
                  (1 / (3 * (Delta : ℝ)^3)) *
                    (∑ Q : Finset V,
                      if Q ∈ J3 then
                        ∑ P : Finset V,
                          if P.card = 2 ∧ P ⊆ Q then
                            (2 / ((2 - ell P) * (1 - ell P)) - 1)
                          else 0
                      else 0) + eta := by
-- BODY
  classical
  refine ⟨1, 1, ?_⟩
  intro Delta gamma hDelta hgamma V _instFintype _instDecEq G _instDecRel hregular μ hsample r X
    hXnbr hclean J3 ell hell
  have hsupp :
      ∀ S : Finset V, μ S ≠ 0 →
        ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v := by
    rcases hsample with
      ⟨_hgamma_pos, _hmu_nonneg, _hmu_sum, _hpairlaw, ν, _hνuniv, _hνact,
        _hνrange, _hνrect, hsupp⟩
    exact hsupp
  have htriple :=
    SamplingTripleExpectationByIndependentTriples (G := G) (μ := μ) (X := X) hsupp
  have hpoint :
      ∀ Q : Finset V, Q ∈ J3 →
        (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
          (1 / (Delta : ℝ)^3) +
            (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V,
                if P.card = 2 ∧ P ⊆ Q then
                  (2 / ((2 - ell P) * (1 - ell P)) - 1)
                else 0) := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hQcard : Q.card = 3 := hQdata.2.1
    have hQX : Q ⊆ X := hQdata.2.2.1
    have hQind :
        ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b := by
      intro a ha b hb hab
      exact hQdata.2.2.2 ha hb hab
    exact
      SamplingFixedIndependentTripleSurvivalBound (G := G) (Delta := Delta)
        (gamma := gamma) (μ := μ) hsample hregular r X Q hXnbr hclean hQcard hQX
        hQind ell hell
  have hsum :
      (∑ Q : Finset V, if Q ∈ J3 then
          ∑ S : Finset V, if Q ⊆ S then μ S else 0
        else 0) ≤
        ∑ Q : Finset V, if Q ∈ J3 then
          (1 / (Delta : ℝ)^3) +
            (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V,
                if P.card = 2 ∧ P ⊆ Q then
                  (2 / ((2 - ell P) * (1 - ell P)) - 1)
                else 0)
        else 0 := by
    refine Finset.sum_le_sum ?_
    intro Q _hQ
    by_cases hQJ3 : Q ∈ J3
    · simp only [if_pos hQJ3]
      exact hpoint Q hQJ3
    · simp only [if_neg hQJ3]
      exact le_rfl
  have hrewrite :
      (∑ Q : Finset V, if Q ∈ J3 then
          (1 / (Delta : ℝ)^3) +
            (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V,
                if P.card = 2 ∧ P ⊆ Q then
                  (2 / ((2 - ell P) * (1 - ell P)) - 1)
                else 0)
        else 0) =
        ((J3.card : ℝ) / (Delta : ℝ)^3) +
          (1 / (3 * (Delta : ℝ)^3)) *
            (∑ Q : Finset V,
              if Q ∈ J3 then
                ∑ P : Finset V,
                  if P.card = 2 ∧ P ⊆ Q then
                    (2 / ((2 - ell P) * (1 - ell P)) - 1)
                  else 0
              else 0) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero]
    rw [add_zero]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [div_eq_mul_inv]
    · rw [Finset.mul_sum]
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
  have heta_nonneg : 0 ≤ eta := le_of_lt heta
  calc
    (∑ S : Finset V, μ S * (Nat.choose (S ∩ X).card 3 : ℝ))
        = ∑ Q : Finset V, if Q ∈ J3 then
            ∑ S : Finset V, if Q ⊆ S then μ S else 0
          else 0 := htriple
    _ ≤ ∑ Q : Finset V, if Q ∈ J3 then
          (1 / (Delta : ℝ)^3) +
            (1 / (3 * (Delta : ℝ)^3)) *
              (∑ P : Finset V,
                if P.card = 2 ∧ P ⊆ Q then
                  (2 / ((2 - ell P) * (1 - ell P)) - 1)
                else 0)
        else 0 := hsum
    _ =
        ((J3.card : ℝ) / (Delta : ℝ)^3) +
          (1 / (3 * (Delta : ℝ)^3)) *
            (∑ Q : Finset V,
              if Q ∈ J3 then
                ∑ P : Finset V,
                  if P.card = 2 ∧ P ⊆ Q then
                    (2 / ((2 - ell P) * (1 - ell P)) - 1)
                  else 0
              else 0) := hrewrite
    _ ≤
        ((J3.card : ℝ) / (Delta : ℝ)^3) +
          (1 / (3 * (Delta : ℝ)^3)) *
            (∑ Q : Finset V,
              if Q ∈ J3 then
                ∑ P : Finset V,
                  if P.card = 2 ∧ P ⊆ Q then
                    (2 / ((2 - ell P) * (1 - ell P)) - 1)
                  else 0
              else 0) + eta := by
          exact le_add_of_nonneg_right heta_nonneg
