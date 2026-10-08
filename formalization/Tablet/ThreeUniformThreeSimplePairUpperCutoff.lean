import Tablet.ExtremalBParameterSaturationThreeSimple
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.TriangleCountPartite
import Tablet.ThreeUniformThreeSimpleExtremalExample
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformThreeSimpleNeighborhoodComplementBounds
import Tablet.ThreeUniformThreeSimpleCutoffScalarEstimate
import Tablet.FiniteHypergraphClassRelabeling

-- [TABLET NODE: ThreeUniformThreeSimplePairUpperCutoff]
theorem ThreeUniformThreeSimplePairUpperCutoff :
    ∀ᶠ D : ℕ in Filter.atTop,
      ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
        ∀ F : MultiHypergraph V E, ∀ f : E,
          ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
            S.P ≤ 1.031 * (D : ℝ) ^ (2 : ℕ) - 9 * (D : ℝ) := by
-- BODY
  classical
  obtain ⟨D0, hD0⟩ := ThreeUniformThreeSimpleExtremalExample
    ((1 : ℝ) / 300000) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (max D0 900000)] with D hD
  intro V E _ _ _ _ F f S
  have hDlarge : 900000 ≤ D := (le_max_right _ _).trans hD
  have hd : (900000 : ℝ) ≤ D := by exact_mod_cast hDlarge
  have hdpos : (0 : ℝ) < D := by linarith
  have hdne : (D : ℝ) ≠ 0 := ne_of_gt hdpos
  obtain ⟨hP0, hPupper, hT0, hTupper, hb⟩ :=
    ThreeUniformThreeSimpleNeighborhoodComplementBounds F f S
  by_contra hcut
  have hcut' : 1.031 * (D : ℝ) ^ 2 - 9 * (D : ℝ) < S.P :=
    lt_of_not_ge hcut
  let p := S.P / (D : ℝ) ^ 2
  let t := S.T / (D : ℝ) ^ 3
  have hp : 1.031 - 9 / (D : ℝ) < p := by
    dsimp [p]
    apply (lt_div_iff₀ (sq_pos_of_pos hdpos)).2
    field_simp at *
    nlinarith
  have hpu : p ≤ 9 / 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hdpos)).2 hPupper
  have htu : t ^ 2 ≤ p ^ 3 / 27 := by
    dsimp [p, t]
    field_simp
    nlinarith
  have hbnormal : S.b = -1 / (D : ℝ) + 1 - p / 9 + t / 27 := by
    rw [hb]
    dsimp [p, t]
    field_simp
    <;> ring
  have hupper : S.b < 0.89291 := by
    rw [hbnormal]
    exact ThreeUniformThreeSimpleCutoffScalarEstimate (D : ℝ) p t hd hp hpu htu
  obtain ⟨V', E', instE, instDE, instDV, H, hH, e, he⟩ :=
    hD0 D ((le_max_left _ _).trans hD)
  letI := instE
  letI := instDE
  letI := instDV
  obtain ⟨V'', E'', instV'', instE'', instDE'', instDV'', H', e', hH', heq⟩ :=
    FiniteHypergraphClassRelabeling 3 3 D (3 * D) H hH e
      (by omega) (le_refl _)
  letI := instV''
  letI := instE''
  letI := instDE''
  letI := instDV''
  have hmax := S.maximizes_b H' hH' e'
  rw [heq] at he
  norm_num at he
  linarith
