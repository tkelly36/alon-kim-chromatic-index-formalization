import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph
import Tablet.OrderThreeAffineIndependentPairs
import Tablet.OrderThreeAffineIndependentTriples

-- [TABLET NODE: ThreeUniformThreeSimpleExtremalExample]
theorem ThreeUniformThreeSimpleExtremalExample :
    ∀ eta : ℝ, 0 < eta →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∃ V E : Type, ∃ _instE : Fintype E, ∃ _instDE : DecidableEq E,
          ∃ _instDV : DecidableEq V,
            ∃ H : MultiHypergraph V E,
              H ∈ HypergraphClass (V := V) (E := E) 3 3 D ∧
              ∃ e : E,
                @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                    (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e
                  ≥ 1 - (1 : ℝ) / 9 + 1 / (3 : ℝ) ^ 5 - eta := by
-- BODY
  classical
  intro eta heta
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / eta)
  refine ⟨max 4 N, ?_⟩
  intro D hD
  have hD4 : 4 ≤ D := (le_max_left 4 N).trans hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hND : (N : ℝ) ≤ D := by exact_mod_cast ((le_max_right 4 N).trans hD)
  have herr : 4 / (D : ℝ) ≤ eta := by
    apply (div_le_iff₀ hDpos).2
    have := (div_lt_iff₀ heta).1 hN
    nlinarith
  let q := (D - 1) / 3
  have hq : 3 * q + 1 ≤ D := by
    dsimp [q]
    omega
  have hq' : D ≤ 3 * q + 3 := by
    dsimp [q]
    omega
  obtain ⟨hclass, _, hdeg, _⟩ := OrderThreeAffineGeometry q
  refine ⟨ZMod 3 × ZMod 3, Option (ZMod 3 × ZMod 3 × Fin q),
    inferInstance, inferInstance, inferInstance, OrderThreeAffineMultihypergraph q,
    ?_, none, ?_⟩
  · exact ⟨hclass.1, hclass.2.1, fun v => (hclass.2.2 v).trans hq⟩
  · rw [LocalBParameter, hdeg, OrderThreeAffineIndependentPairs,
      OrderThreeAffineIndependentTriples]
    push_cast
    let x : ℝ := q / (D : ℝ)
    have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hDpos.le
    have hx : x ≤ 1 / 3 := by
      dsimp [x]
      apply (div_le_iff₀ hDpos).2
      have : (3 : ℝ) * q + 1 ≤ D := by exact_mod_cast hq
      linarith
    have hgap : 1 / 3 - x ≤ 1 / (D : ℝ) := by
      have hcast : (D : ℝ) ≤ 3 * q + 3 := by exact_mod_cast hq'
      apply (mul_le_mul_iff_left₀ hDpos).mp
      dsimp [x]
      field_simp
      nlinarith
    have hpoly :
        1 - (1 : ℝ) / 9 + 1 / (3 : ℝ) ^ 5 -
          (3 * x - x ^ 2 + x ^ 3 / 9) ≤ 4 / (D : ℝ) := by
      have hfactor : 3 - (1 / 3 + x) + ((1 / 3 : ℝ)^2 + x / 3 + x^2) / 9 ≤ 4 := by
        have : x ^ 2 ≤ (1 / 3 : ℝ)^2 := sq_le_sq₀ hx0 (by norm_num) |>.2 hx
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hx)
      simp only [div_eq_mul_inv] at hgap ⊢
      nlinarith
    have hid : (9 * (q : ℝ)) / (3 * D) - (9 * (q : ℝ)^2) / (3 * D)^2 +
        (3 * (q : ℝ)^3) / (3 * D)^3 = 3*x - x^2 + x^3/9 := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    linarith
