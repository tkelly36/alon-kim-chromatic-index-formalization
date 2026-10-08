import Tablet.ChromaticIndexAtMostReal
import Tablet.HypergraphClass
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.OneNibblePartialColoring
import Tablet.SubhypergraphOf
import Tablet.SubhypergraphInheritance
import Tablet.CanonicalResidualEmbedding
import Tablet.FiniteGraphGreedyColoring
import Tablet.UniformHypergraphLineDegreeBound
import Tablet.GeneralColoringRoundedSchedule
import Tablet.GeneralColoringScheduledNibbleIteration
import Tablet.PartialEdgeColoringGreedyFinish

-- [TABLET NODE: GeneralColoringIterationGreedyFinish]
theorem GeneralColoringIterationGreedyFinish (eps : ℝ) (k : ℕ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hk : 0 < k) :
    ∃ D0 : ℕ, ∀ D : ℝ, (D0 : ℝ) ≤ D → ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          UniformHypergraph H k → (∀ v, (HypergraphDegree H v : ℝ) ≤ D) →
          (∀ {F : Type*} [Fintype F] [DecidableEq F], ∀ D' : ℕ,
            eps * (D : ℝ) / 3 ≤ (D' : ℝ) →
            ∀ H' : MultiHypergraph V F,
              SubhypergraphOf H' H → MaxDegreeAtMost H' D' →
              ∀ e : F,
                @LocalBParameter F _ _ (LineGraphOfHypergraph H')
                  (Classical.decRel (LineGraphOfHypergraph H').Adj) (k * D') e ≤ theta) →
          ChromaticIndexAtMostReal H ((theta + eps) * (k : ℝ) * (D : ℝ)) := by
-- BODY
  obtain ⟨A, hA⟩ := GeneralColoringRoundedSchedule eps k heps heps1 hk
  obtain ⟨gamma0, hgamma0⟩ := GeneralColoringScheduledNibbleIteration eps A k heps
  obtain ⟨gamma, hgamma, hgammaPos, hsched⟩ := hA gamma0
  obtain ⟨Dn, hiter⟩ := hgamma0 gamma hgamma hgammaPos
  obtain ⟨D0, hD0⟩ := hsched Dn
  refine ⟨D0, ?_⟩
  intro D hD theta htheta htheta1 V E instE instDE instDV H hu hd hb
  obtain ⟨s, N, K, hN0, hK0, hsteps, hbudget⟩ := hD0 D hD theta htheta htheta1
  have hd0 : MaxDegreeAtMost H (N 0) := by
    intro v
    exact_mod_cast (hd v).trans hN0
  obtain ⟨C, c, hc, hr⟩ := hiter D theta s N K hK0 hsteps H hu hd0 hb
  exact ⟨K s + (k * N s + 1), hbudget,
    PartialEdgeColoringGreedyFinish H k (K s) (N s) hu C c hc hr⟩
