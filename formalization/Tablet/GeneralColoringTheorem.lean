import Tablet.ChromaticIndexAtMost
import Tablet.ChromaticIndexAtMostReal
import Tablet.GeneralColoringIterationGreedyFinish
import Tablet.HypergraphClass
import Tablet.IndependentSetSamplingBound
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.OneNibblePartialColoring
import Tablet.ProperEdgeColoring
import Tablet.SubhypergraphOf
import Tablet.LocalBParameterRealNatCast
import Tablet.RealDegreeFloorBound
import Tablet.UniformHypergraphGreedyColoring

-- [TABLET NODE: GeneralColoringTheorem]
theorem GeneralColoringTheorem (eps : ℝ) (k : ℕ) (heps : 0 < eps) (hk : 0 < k) :
    ∃ D0 : ℕ, ∀ D : ℝ, (D0 : ℝ) ≤ D → ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          UniformHypergraph H k → (∀ v, (HypergraphDegree H v : ℝ) ≤ D) →
          (∀ {F : Type*} [Fintype F] [DecidableEq F], ∀ D' : ℝ,
            eps * D / 3 ≤ D' →
            ∀ H' : MultiHypergraph V F,
              SubhypergraphOf H' H → (∀ v, (HypergraphDegree H' v : ℝ) ≤ D') →
              ∀ e : F,
                @LocalBParameterReal F _ _ (LineGraphOfHypergraph H')
                  (Classical.decRel (LineGraphOfHypergraph H').Adj) ((k : ℝ) * D') e ≤ theta) →
          ChromaticIndexAtMostReal H ((theta + eps) * (k : ℝ) * (D : ℝ)) := by
-- BODY
  classical
  by_cases heps1 : eps ≤ 1
  · obtain ⟨D0, hD0⟩ := GeneralColoringIterationGreedyFinish eps k heps heps1 hk
    refine ⟨D0, ?_⟩
    intro D hD theta ht ht1 V E _ _ _ H hu hd hb
    apply hD0 D hD theta ht ht1 H hu hd
    intro F _ _ n hn H' hs hd' e
    have hh := hb (n : ℝ) hn H' hs (fun v => by exact_mod_cast hd' v) e
    simpa only [← Nat.cast_mul, LocalBParameterRealNatCast] using hh
  · refine ⟨1, ?_⟩
    intro D hD theta ht ht1 V E _ _ _ H hu hd hb
    have hD1 : 1 ≤ D := by simpa using hD
    have hn : 0 < ⌊D⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor (by simpa using hD1))
    refine ⟨k * ⌊D⌋₊, ?_, UniformHypergraphGreedyColoring H hk hn hu
      (RealDegreeFloorBound H hd)⟩
    calc
      ((k * ⌊D⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) * D := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by positivity)
      _ ≤ (theta + eps) * (k : ℝ) * D := by
        have hc : 1 ≤ theta + eps := by linarith
        nlinarith [mul_nonneg (Nat.cast_nonneg k) (show 0 ≤ D by linarith)]
