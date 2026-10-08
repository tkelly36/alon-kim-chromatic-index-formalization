import Tablet.FiniteRealFunctionAttainsMaximum
import Tablet.HypergraphClass
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.KUniformKSimpleBoundedLocalPatternLift
import Tablet.KUniformKSimpleBoundedLocalPatternAttainsMaximum
import Tablet.KUniformKSimpleLocalPatternTransportToBounded
import Tablet.KUniformKSimpleLocalTruncationPreservesBParameter
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

universe u v

-- [TABLET NODE: KUniformKSimpleLocalPatternExtremalReduction]
theorem KUniformKSimpleLocalPatternExtremalReduction :
    ∀ k : ℕ, 0 < k → ∀ D : ℕ, 0 < D →
      ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) k k D →
          ∀ e : E,
            ∃ (Vloc : Type u) (Eloc : Type v),
              ∃ (_instFintype : Fintype Eloc) (_instDecidableEqE : DecidableEq Eloc)
                (_instDecidableEqV : DecidableEq Vloc),
                ∃ (F : MultiHypergraph Vloc Eloc) (f : Eloc),
                  F ∈ HypergraphClass (V := Vloc) (E := Eloc) k k D ∧
                    @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                        (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e
                      ≤ @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                        (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f ∧
                    (∀ {V' : Type u} {E' : Type v}
                      [Fintype E'] [DecidableEq E'] [DecidableEq V'],
                      ∀ H' : MultiHypergraph V' E',
                        H' ∈ HypergraphClass (V := V') (E := E') k k D →
                        ∀ e' : E',
                          @LocalBParameter E' _ _ (LineGraphOfHypergraph H')
                              (Classical.decRel (LineGraphOfHypergraph H').Adj) (k * D) e'
                            ≤ @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                              (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f) := by
-- BODY
  classical
  intro k hk D hD V E instFintypeE instDecidableEqE instDecidableEqV H hH e
  obtain ⟨P₀, hP₀⟩ :=
    KUniformKSimpleLocalPatternTransportToBounded
      k hk D hD H hH e
  obtain ⟨Pmax, hmax⟩ :=
    KUniformKSimpleBoundedLocalPatternAttainsMaximum k D ⟨P₀⟩
  obtain ⟨Vloc, Eloc, instFintypeEloc, instDecidableEqEloc, instDecidableEqVloc,
    F, f, hF, hscore⟩ :=
    KUniformKSimpleBoundedLocalPatternLift.{u, v} k D Pmax
  refine ⟨Vloc, Eloc, instFintypeEloc, instDecidableEqEloc, instDecidableEqVloc,
    F, f, hF, ?_, ?_⟩
  · exact le_trans hP₀ ((hmax P₀).trans_eq hscore)
  · intro V' E' instFintypeE' instDecidableEqE' instDecidableEqV' H' hH' e'
    obtain ⟨P', hP'⟩ :=
      KUniformKSimpleLocalPatternTransportToBounded
        k hk D hD H' hH' e'
    exact le_trans hP' ((hmax P').trans_eq hscore)
