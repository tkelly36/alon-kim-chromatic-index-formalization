import Tablet.ChromaticIndexAtMostReal
import Tablet.GeneralColoringTheorem
import Tablet.HypergraphClass
import Tablet.ThreeUniformTwoSimpleBParameterEstimate
import Tablet.SubhypergraphInheritance
import Tablet.RealDegreeFloorBound
import Tablet.LocalBParameterRealFloorTransfer

-- [TABLET NODE: ThreeUniformTwoSimpleChromaticIndexBound]
theorem ThreeUniformTwoSimpleChromaticIndexBound :
    (∀ iota : ℝ, 0 < iota →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
            ChromaticIndexAtMostReal H
              ((1 - (2 : ℝ) / 9 + 2 / (3 : ℝ) ^ 5 + iota) * 3 * (D : ℝ))) ∧
    (∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
          ChromaticIndexAtMostReal H (2.3581 * (D : ℝ))) := by
-- BODY
  classical
  constructor <;> (
  have main : ∀ iota : ℝ, 0 < iota →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type _} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
            ChromaticIndexAtMostReal H
              ((1 - (2 : ℝ) / 9 + 2 / (3 : ℝ) ^ 5 + iota) * 3 * (D : ℝ)) := by
    intro iota hiota
    let c : ℝ := 1 - (2 : ℝ) / 9 + 2 / (3 : ℝ) ^ 5
    have hcpos : 0 < c := by norm_num [c]
    have hclt : c < 1 := by norm_num [c]
    let alpha : ℝ := min iota (1 - c)
    let eps : ℝ := alpha / 2
    let theta : ℝ := c + alpha / 2
    have ha : 0 < alpha := lt_min hiota (by linarith)
    have hai : alpha ≤ iota := min_le_left _ _
    have hac : alpha ≤ 1 - c := min_le_right _ _
    have heps : 0 < eps := by dsimp [eps]; positivity
    have ht : 0 < theta := by dsimp [theta]; linarith
    have ht1 : theta < 1 := by
      change c + alpha / 2 < 1
      norm_num [c] at hac ⊢
      linarith only [hac]
    obtain ⟨Dg, hg⟩ := GeneralColoringTheorem eps 3 heps (by decide)
    obtain ⟨Db, hb⟩ := ThreeUniformTwoSimpleBParameterEstimate eps heps
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 * ((Db : ℝ) + 1) / eps < N :=
      exists_nat_gt _
    refine ⟨max Dg N, ?_⟩
    intro D hD V E _ _ _ H hH
    have hDg : Dg ≤ D := (Nat.le_max_left _ _).trans hD
    have hDn : N ≤ D := (Nat.le_max_right _ _).trans hD
    have hout := hg (D : ℝ) (by exact_mod_cast hDg) theta ht ht1 H hH.1
      (fun v => by exact_mod_cast hH.2.2 v) (by
        intro (F : Type 0) _ _ r hr H' hsub hmax e
        have hcross : 3 * ((Db : ℝ) + 1) < eps * (N : ℝ) := by
          simpa [mul_comm] using (div_lt_iff₀ heps).mp hN
        have hmono : eps * (N : ℝ) ≤ eps * (D : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hDn) heps.le
        have hDb : (Db : ℝ) + 1 ≤ r := by nlinarith
        have hn : Db ≤ ⌊r⌋₊ := Nat.le_floor (by linarith)
        have hrone : 1 ≤ r := by
          have := Nat.cast_nonneg (α := ℝ) Db
          linarith
        have hinherit := SubhypergraphInheritance H' H hsub
        have hu := hinherit.1 3 hH.1
        have hfloor := LocalBParameterRealFloorTransfer H' (by decide : 0 < 3)
          hu hrone hmax e
        refine hfloor.trans ((hb ⌊r⌋₊ hn H' ?_ e).trans ?_)
        · exact ⟨hu, hinherit.2.1 2 hH.2.1, RealDegreeFloorBound H' hmax⟩
        · exact le_of_eq (by dsimp [theta, eps, c]))
    rcases hout with ⟨q, hq, hcol⟩
    refine ⟨q, hq.trans ?_, hcol⟩
    have hcoef : theta + eps ≤ c + iota := by dsimp [theta, eps]; linarith
    simpa [c] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by norm_num : (0 : ℝ) ≤ 3))
      (Nat.cast_nonneg D)
  first | exact main | (
  obtain ⟨D0, hD0⟩ := main (1 / 100000 : ℝ) (by norm_num)
  refine ⟨D0, ?_⟩
  intro D hD V E _ _ _ H hH
  rcases hD0 D hD H hH with ⟨q, hq, hcol⟩
  refine ⟨q, hq.trans ?_, hcol⟩
  have hc : (1 - (2 : ℝ) / 9 + 2 / (3 : ℝ) ^ 5 + 1 / 100000) * 3 ≤
      2.3581 := by norm_num
  exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg D)))
