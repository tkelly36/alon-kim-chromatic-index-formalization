import Tablet.BoundedSquaresInterval
import Tablet.ExtremalBParameterSaturationThreeSimple
import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.SaturatedLineGraphEdgeCount
import Tablet.ThreeUniformSaturatedEdgeStructure
import Tablet.ThreeUniformThreeSimpleBalancedBigDegree
import Tablet.ThreeUniformThreeSimpleBigPartSize
import Tablet.ThreeUniformThreeSimplePairLowerBound
import Tablet.ThreeUniformThreeSimplePairUpperCutoff
import Tablet.ThreeUniformThreeSimpleSmallXs
import Tablet.ThreeUniformThreeSimpleT2TriangleBound
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformTwoSimpleBParameterEstimate
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph
import Tablet.KUniformKSimpleLocalPatternExtremalReduction
import Tablet.FiniteHypergraphClassRelabeling
import Tablet.ThreeUniformThreeSimpleSetupConstruction
import Tablet.ThreeUniformThreeSimpleT1IncidenceBound
import Tablet.ThreeUniformThreeSimpleT2UniformEstimate
import Tablet.ThreeUniformThreeSimpleNeighborhoodComplementBounds

-- [TABLET NODE: ThreeUniformThreeSimpleBParameterEstimate]
theorem ThreeUniformThreeSimpleBParameterEstimate :
    ∀ eta : ℝ, 0 < eta →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) 3 3 D →
            ∀ e : E,
              @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                  (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e
                ≤ 1 - (1 : ℝ) / 9 + 1 / (3 : ℝ) ^ 5 + eta := by
-- BODY
  classical
  intro eta heta
  obtain ⟨Dsat, hsat⟩ := Filter.eventually_atTop.mp
    ExtremalBParameterSaturationThreeSimple.{0, 0, 0, 0}
  obtain ⟨Dcut, hcut⟩ := Filter.eventually_atTop.mp
    ThreeUniformThreeSimplePairUpperCutoff.{0, 0, 0, 0}
  obtain ⟨Dt, ht⟩ := Filter.eventually_atTop.mp
    (ThreeUniformThreeSimpleT2UniformEstimate.{0, 0, 0, 0} eta heta)
  refine ⟨max 100 (max Dsat (max Dcut Dt)), ?_⟩
  intro D hD V E _ _ _ H hH e
  have h100 : 100 ≤ D := (le_max_left _ _).trans hD
  have hsatD : Dsat ≤ D := by omega
  have hcutD : Dcut ≤ D := by omega
  have htD : Dt ≤ D := by omega
  have hpos : 0 < D := by omega
  have hMpos : 0 < 3 * D := by omega
  obtain ⟨V0, E0, iV0, iE0, iDE0, iDV0, H0, e0, hH0, heq0⟩ :=
    FiniteHypergraphClassRelabeling.{_, _, 0, 0}
      3 3 D (3 * D) H hH e hMpos le_rfl
  letI := iV0
  letI := iE0
  letI := iDE0
  letI := iDV0
  obtain ⟨Vm, Em, iEm, iDEm, iDVm, Fm, fm, hFm, hle, hmax⟩ :=
    KUniformKSimpleLocalPatternExtremalReduction 3 (by norm_num) D hpos H0 hH0 e0
  letI := iEm
  letI := iDEm
  letI := iDVm
  obtain ⟨W, J, iW, iJ, iDJ, iDW, F, f, hF, heq⟩ :=
    FiniteHypergraphClassRelabeling.{0, 0, 0, 0}
      3 3 D (3 * D) Fm hFm fm hMpos le_rfl
  letI := iW
  letI := iJ
  letI := iDJ
  letI := iDW
  rw [heq] at hle hmax
  obtain ⟨hv, hn⟩ := hsat D hsatD F hF f hmax
  obtain ⟨S⟩ := ThreeUniformThreeSimpleSetupConstruction D h100 F f hF hmax hv hn
  have hpupper := hcut D hcutD F f S
  have hplower := ThreeUniformThreeSimplePairLowerBound D F f S
  have hd : (0 : ℝ) < D := by exact_mod_cast hpos
  have hd2 : 0 < (D : ℝ) ^ 2 := sq_pos_of_pos hd
  let delta : ℝ := (S.P + 9 * D) / (D : ℝ) ^ 2 - 1
  have hP : S.P = (1 + delta) * (D : ℝ) ^ 2 - 9 * D := by
    dsimp [delta]
    field_simp
    <;> ring
  have hdelta : 0 ≤ delta := by
    have hmul : 0 ≤ delta * (D : ℝ) ^ 2 := by
      nlinarith [S.Y_nonnegative]
    exact nonneg_of_mul_nonneg_left hmul hd2
  have hdelta31 : delta ≤ 0.031 := by
    have hmul : delta * (D : ℝ) ^ 2 ≤ 0.031 * (D : ℝ) ^ 2 := by
      nlinarith [hpupper]
    exact (mul_le_mul_iff_left₀ hd2).mp hmul
  obtain ⟨hsmall, _⟩ :=
    ThreeUniformThreeSimpleSmallXs D F f S hpupper delta hdelta hP.le
  obtain ⟨hT1, hV1⟩ := ThreeUniformThreeSimpleT1IncidenceBound F f S
  have hT1' : S.T1 ≤ (8 / 5 : ℝ) * delta * (D : ℝ) ^ 3 := by
    have hinc := mul_le_mul_of_nonneg_right (hV1.trans hsmall) hd2.le
    nlinarith only [hT1, hinc]
  have hT2 := ht D htD F f S delta hdelta hdelta31 hP
  have hT : S.T ≤ ((1 / 9 : ℝ) + 3 * delta + eta) * (D : ℝ) ^ 3 := by
    have hnonneg := mul_nonneg hdelta (pow_nonneg hd.le 3)
    nlinarith only [S.T_split, hT1', hT2, hnonneg]
  have hb := (ThreeUniformThreeSimpleNeighborhoodComplementBounds F f S).2.2.2.2
  have hdiv := div_le_div_of_nonneg_right hT
    (show 0 ≤ (3 * (D : ℝ)) ^ 3 by positivity)
  have hcancel :
      3 * ((D : ℝ) - 1) / (3 * (D : ℝ)) -
        ((1 + delta) * (D : ℝ) ^ 2 - 9 * D) / (3 * (D : ℝ)) ^ 2 +
        (((1 / 9 : ℝ) + 3 * delta + eta) * (D : ℝ) ^ 3) /
          (3 * (D : ℝ)) ^ 3 = 1 - (1 : ℝ) / 9 + 1 / (3 : ℝ) ^ 5 + eta / 27 := by
    field_simp
    <;> ring
  rw [heq0]
  apply hle.trans
  rw [← S.b_eq]
  rw [hP] at hb
  linarith
