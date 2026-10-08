import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph
import Tablet.KUniformKSimpleExtremalSaturation
import Tablet.FiniteHypergraphClassRelabeling

-- [TABLET NODE: ExtremalBParameterSaturationThreeSimple]
theorem ExtremalBParameterSaturationThreeSimple :
    ∀ᶠ D : ℕ in Filter.atTop, ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E,
        H ∈ HypergraphClass (V := V) (E := E) 3 3 D →
        ∀ e : E,
          (∀ {V' E' : Type*} [Fintype E'] [DecidableEq E'] [DecidableEq V'],
            ∀ H' : MultiHypergraph V' E',
              H' ∈ HypergraphClass (V := V') (E := E') 3 3 D →
              ∀ e' : E',
                @LocalBParameter E' _ _ (LineGraphOfHypergraph H')
                    (Classical.decRel (LineGraphOfHypergraph H').Adj) (3 * D) e'
                  ≤ @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                    (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e) →
          (∀ v : V, v ∈ H.edge e → HypergraphDegree H v = D) ∧
          ((Finset.univ : Finset E).filter
            (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)).card = 3 * (D - 1) := by
-- BODY
  classical
  obtain ⟨D0, hD0⟩ := KUniformKSimpleExtremalSaturation 3 (by norm_num)
  apply Filter.eventually_atTop.mpr
  refine ⟨max D0 2, ?_⟩
  intro D hD V E _ _ _ H hH e hmax
  have hDtwo : 2 ≤ D := (le_max_right D0 2).trans hD
  have hMpos : 0 < 3 * D := by omega
  have hsat := hD0 D ((le_max_left D0 2).trans hD) H hH e
  have hresult := hsat (by
    intro V' E' _ _ _ H' hH' e'
    obtain ⟨W, F, _, _, _, _, K, f, hK, hparam⟩ :=
      FiniteHypergraphClassRelabeling 3 3 D (3 * D) H' hH' e' hMpos le_rfl
    rw [hparam]
    exact hmax K hK f)
  refine ⟨hresult.1, ?_⟩
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using hresult.2
