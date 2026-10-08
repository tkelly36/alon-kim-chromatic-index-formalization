import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.ExtremalBParameterSaturation
import Tablet.SaturatedEdgeStructure
import Tablet.SaturatedLineGraphPairBound
import Tablet.TSimpleHypergraph
import Tablet.ThreeByNMatrixBound
import Tablet.ThreeUniformTwoSimpleDegreeToBigBound
import Tablet.ThreeUniformTwoSimpleSmallPairsBound
import Tablet.ThreeUniformTwoSimpleTripleBound
import Tablet.UniformHypergraph
import Tablet.ThreeUniformTwoSimpleFiniteExtremalAttainment
import Tablet.ThreeUniformTwoSimpleSaturatedMatrixCertificate
import Tablet.ThreeUniformTwoSimpleMatrixRescaling
import Tablet.ThreeUniformTwoSimpleEventualNumericalError

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleBParameterEstimate]
theorem ThreeUniformTwoSimpleBParameterEstimate :
    ∀ eta : ℝ, 0 < eta →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
            ∀ e : E,
              @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                  (Classical.decRel (LineGraphOfHypergraph H).Adj) (3 * D) e
                ≤ 1 - (2 : ℝ) / 9 + 2 / (3 : ℝ) ^ 5 + eta := by
-- BODY
  classical
  intro eta heta
  obtain ⟨Derr, herr⟩ := ThreeUniformTwoSimpleEventualNumericalError eta heta
  obtain ⟨Dsat, hsat⟩ := Filter.eventually_atTop.mp ExtremalBParameterSaturation
  refine ⟨max 1 (max Derr Dsat), ?_⟩
  intro D hD V E _ _ _ H hH e
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 1)
    ((le_max_left _ _).trans hD)
  have hDe : Derr ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDs : Dsat ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  obtain ⟨V₀, E₀, iV, iE, dE, dV, F, f, hF, hmax⟩ :=
    ThreeUniformTwoSimpleFiniteExtremalAttainment D hDpos
  letI := iV
  letI := iE
  letI := dE
  letI := dV
  have hcompare := hmax H hH e
  obtain ⟨hdegree, hneighbors⟩ := hsat D hDs F hF f hmax
  obtain ⟨n, hn, A, horigin, hA, hcolumn, horder, htotal, hb⟩ :=
    ThreeUniformTwoSimpleSaturatedMatrixCertificate D hDpos F hF f hdegree hneighbors
  let Q : ℝ := ∑ j : Fin n, ∑ i : Fin 3, ∑ i' : Fin 3,
    if i < i' then A i j * A i' j else 0
  let P : ℝ := Matrix.permanent (fun i j : Fin 3 => A i (Fin.castLE hn j))
  let L : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, A i (Fin.castLE hn j)
  let r : ℝ := 1 + 18 * (D : ℝ) ^ (-(1 : ℝ) / 3)
  have hQ : 0 ≤ Q := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro i' _
    split_ifs
    · exact mul_nonneg (hA i j).1 (hA i' j).1
    · exact le_refl 0
  have hL : L ≤ 3 := by
    dsimp [L]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hcolumn (Fin.castLE hn j))
      _ = 3 := by norm_num
  have hr : 1 ≤ r := by
    dsimp [r]
    have := Real.rpow_nonneg (Nat.cast_nonneg D) (-(1 : ℝ) / 3)
    linarith
  have hm := ThreeByNMatrixBound hn A hA hcolumn horder htotal
  have hscale := ThreeUniformTwoSimpleMatrixRescaling r Q P L hr hQ hL hm
  have he := herr D hDe
  dsimp only at hb he
  change _ ≤ 1 - (2 : ℝ) / 9 + (2 : ℝ) / 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) +
    8 / (9 * (D : ℝ)) + r ^ 2 / 9 * Q + r ^ 3 / 27 * P - r / 27 * L at hb
  change (2 : ℝ) / 9 * (D : ℝ) ^ (-(1 : ℝ) / 3) + 8 / (9 * (D : ℝ)) +
    r ^ 3 * (2 / (3 : ℝ) ^ 5) + (r ^ 2 - 1) * r / 9 ≤
    2 / (3 : ℝ) ^ 5 + eta at he
  linarith
