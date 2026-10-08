import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformT2AmbientCherryBound
import Tablet.ThreeUniformT2ExceptionalDegreeBounds
import Tablet.ThreeUniformT2OrientedIncidenceBound
import Tablet.T2DegreeSquareAssembly

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleT2TriangleBound]
theorem ThreeUniformThreeSimpleT2TriangleBound :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
      ∀ F : MultiHypergraph V E, ∀ f : E,
        ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
          ∀ eps : ℝ,
            0 < eps →
            eps ≤ (1 / 2 : ℝ) →
            (∀ g : E, g ∈ S.V2 →
              |S.crossDegree g - (4 / 3 : ℝ) * (D : ℝ)| ≤ eps * (D : ℝ)) →
            S.T2 ≤
              (1 / 12 : ℝ) *
                ((((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) /
                    (D : ℝ) ^ (2 : ℕ) -
                  (4 / 3 : ℝ) + 3 * eps ^ (2 : ℕ)) * (D : ℝ) ^ (3 : ℕ)) +
                (4 / 3 : ℝ) * (D : ℝ) ^ (2 : ℕ) := by
-- BODY
  classical
  intro D V E _ _ _ _ F f S eps he he' hc
  let N := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  let q := fun g => ((N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card : ℝ)
  let y := fun g => ((N.filter (fun h =>
    F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
    (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card : ℝ)
  have hch : S.T2 ≤ (1 / 12 : ℝ) * ∑ g ∈ S.V2, q g ^ 2 :=
    ThreeUniformT2AmbientCherryBound D F f S
  obtain ⟨hq, hy, hY⟩ := ThreeUniformT2ExceptionalDegreeBounds D F f S
  have hs := ThreeUniformT2OrientedIncidenceBound D F f S
  have hsq := T2DegreeSquareAssembly
    (fun g : S.V2 => q g) (fun g : S.V2 => S.crossDegree g)
    (fun g : S.V2 => y g) (D : ℝ) eps S.V1.card S.WXb S.Y
    (Nat.cast_nonneg D) he he' (fun g => hq g g.2) (fun g => hy g g.2)
    (by simpa only [Finset.sum_coe_sort] using hY)
    (fun g => hc g g.2) (by simpa only [Finset.sum_coe_sort] using hs)
  rw [Finset.sum_coe_sort S.V2 (fun g : E => q g ^ 2), Fintype.card_coe] at hsq
  have hcard : (S.V1.card : ℝ) + S.V2.card ≤ 3 * (D : ℝ) := by
    have hnat : S.V1.card + S.V2.card = 3 * (D - 1) := by
      rw [← Finset.card_union_of_disjoint S.V1_disjoint_V2,
        S.V_partition, S.saturated_neighbors]
    exact_mod_cast (show S.V1.card + S.V2.card ≤ 3 * D by omega)
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by have := S.D_large; omega)
  have hweight : S.WXb = 3 * (D : ℝ) ^ 2 - 6 * D + 3 - S.P - S.WXs + S.Y := by
    linarith [S.pair_identity, S.W_split]
  have hcoef : 0 ≤ (20 / 9 : ℝ) + eps ^ 2 := by positivity
  have hsize := mul_le_mul_of_nonneg_right hcard
    (mul_nonneg hcoef (sq_nonneg (D : ℝ)))
  have hsmall : (4 / 3 : ℝ) * S.V1.card * (D : ℝ) ^ 2 ≤
      ((20 / 9 : ℝ) + eps ^ 2) * S.V1.card * (D : ℝ) ^ 2 := by
    have := mul_nonneg (sq_nonneg eps)
      (mul_nonneg (Nat.cast_nonneg S.V1.card) (sq_nonneg (D : ℝ)))
    have := mul_nonneg (Nat.cast_nonneg S.V1.card) (sq_nonneg (D : ℝ))
    nlinarith
  have hsum : (∑ g ∈ S.V2, q g ^ 2) ≤
      ((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) * D +
      (-(4 / 3 : ℝ) + 3 * eps ^ 2) * (D : ℝ) ^ 3 + 16 * (D : ℝ) ^ 2 := by
    rw [hweight] at hsq
    have := mul_nonneg (le_of_lt hd) S.Y_nonnegative
    nlinarith only [hsq, hsize, hsmall, this, hd]
  have hdiv :
      ((((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) /
        (D : ℝ) ^ 2 - (4 / 3 : ℝ) + 3 * eps ^ 2) * (D : ℝ) ^ 3) =
      ((8 / 3 : ℝ) * (S.P + S.WXs) + (4 + 2 * eps) * S.Y) * D +
      (-(4 / 3 : ℝ) + 3 * eps ^ 2) * (D : ℝ) ^ 3 := by
    field_simp [ne_of_gt hd]
    <;> ring
  rw [hdiv]
  linarith
