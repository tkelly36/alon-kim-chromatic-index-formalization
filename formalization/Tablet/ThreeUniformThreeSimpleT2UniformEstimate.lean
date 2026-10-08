import Tablet.ThreeUniformThreeSimplePairLowerBound
import Tablet.ThreeUniformThreeSimpleSmallXs
import Tablet.ThreeUniformThreeSimpleBigPartSize
import Tablet.ThreeUniformThreeSimpleBalancedBigDegree
import Tablet.ThreeUniformThreeSimpleT2TriangleBound

-- [TABLET NODE: ThreeUniformThreeSimpleT2UniformEstimate]
theorem ThreeUniformThreeSimpleT2UniformEstimate
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ D : ℕ in Filter.atTop,
      ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
        ∀ F : MultiHypergraph V E, ∀ f : E,
          ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
            ∀ delta : ℝ, 0 ≤ delta → delta ≤ 0.031 →
              S.P = (1 + delta) * (D : ℝ) ^ 2 - 9 * (D : ℝ) →
              S.T2 ≤ ((1 / 9 : ℝ) + 1.33 * delta + eta) * (D : ℝ) ^ 3 := by
-- BODY
  classical
  filter_upwards [] with D
  intro V E _ _ _ _ F f S delta hdelta hdelta31 hP
  have hd : (0 : ℝ) < D := by
    exact_mod_cast (show 0 < D by have := S.D_large; omega)
  have hcut : S.P ≤ 1.031 * (D : ℝ) ^ 2 - 9 * D := by
    have := mul_le_mul_of_nonneg_right hdelta31 (sq_nonneg (D : ℝ))
    nlinarith only [hP, this]
  obtain ⟨_, hsmall⟩ :=
    ThreeUniformThreeSimpleSmallXs D F f S hcut delta hdelta hP.le
  have hY : S.Y ≤ delta * (D : ℝ) ^ 2 := by
    have := ThreeUniformThreeSimplePairLowerBound D F f S
    linarith
  have hbig : (2 - (77 / 75 : ℝ) * delta) * (D : ℝ) ^ 2 ≤ S.WXb := by
    nlinarith only [S.pair_identity, S.W_split, S.Y_nonnegative, hP, hsmall, hd]
  have hcard := ThreeUniformThreeSimpleBigPartSize D F f S delta hdelta hdelta31 hP
  let q : ℝ := min eta (1 / 10)
  have hq : 0 < q := lt_min heta (by norm_num)
  have hqeta : q ≤ eta := min_le_left _ _
  have hq10 : q ≤ 1 / 10 := min_le_right _ _
  let eps : ℝ := Real.sqrt ((8 / 3 : ℝ) * ((77 / 75 : ℝ) * delta) + q)
  have hrad : 0 < (8 / 3 : ℝ) * ((77 / 75 : ℝ) * delta) + q := by positivity
  have heps : 0 < eps := Real.sqrt_pos.2 hrad
  have hepssq : eps ^ 2 = (8 / 3 : ℝ) * ((77 / 75 : ℝ) * delta) + q :=
    Real.sq_sqrt hrad.le
  have hepshalf : eps ≤ 1 / 2 := by
    nlinarith only [hepssq, hdelta31, hq10, heps]
  have hbalance : ∀ g : E, g ∈ S.V2 →
      |S.crossDegree g - (4 / 3 : ℝ) * D| ≤ eps * D := by
    intro g hg
    have h := ThreeUniformThreeSimpleBalancedBigDegree D F f S
      ((77 / 75 : ℝ) * delta) (by positivity) hcard hbig g hg
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hd.le
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hq.le)
  have ht := ThreeUniformThreeSimpleT2TriangleBound D F f S eps heps hepshalf hbalance
  have hdiv :
      ((((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) /
        (D : ℝ) ^ 2 - (4 / 3 : ℝ) + 3 * eps ^ 2) * (D : ℝ) ^ 3) =
      ((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) * D +
      (-(4 / 3 : ℝ) + 3 * eps ^ 2) * (D : ℝ) ^ 3 := by
    field_simp
    <;> ring
  rw [hdiv, hepssq] at ht
  have hYeps : (4 + 2 * eps) * S.Y ≤ 5 * (delta * (D : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_right hepshalf S.Y_nonnegative
    nlinarith only [this, hY]
  have hsmallD := mul_le_mul_of_nonneg_right hsmall hd.le
  have hYD := mul_le_mul_of_nonneg_right hYeps hd.le
  have hqD := mul_le_mul_of_nonneg_right hqeta (pow_nonneg hd.le 3)
  have hdeltanonneg := mul_nonneg hdelta (pow_nonneg hd.le 3)
  have hetanonneg := mul_nonneg heta.le (pow_nonneg hd.le 3)
  rw [hP] at ht
  nlinarith only [ht, hsmallD, hYD, hqD, hdeltanonneg, hetanonneg,
    sq_nonneg (D : ℝ)]
