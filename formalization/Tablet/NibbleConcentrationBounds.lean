import Tablet.NibbleResidualDegree
import Tablet.NibbleDeletedColors
import Tablet.NibbleResidualDegreeBoundedDifference
import Tablet.NibbleSelectedSetProductLaw
import Tablet.FiniteIndependentBoundedDifferences
import Tablet.FiniteIndependentBernoulliCountTail

open MeasureTheory

-- [TABLET NODE: NibbleConcentrationBounds]
theorem NibbleConcentrationBounds {V E K : Type*} [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq E] [DecidableEq K]
    {H : MultiHypergraph V E} {M : E → Finset K} {Delta : ℕ}
    (Q : NibbleCompletionData H M Delta) (gamma iota t d b : ℝ)
    (hg : 0 < gamma) (hgD : gamma ≤ Delta) (hi : 0 < iota) (ht : 0 < t)
    (hK : 0 < Fintype.card K) (ell : ℕ) (hell : 0 < ell)
    (hM : ∀ e, (M e).card = ell) :
    let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a)) (gamma / Delta)
    (∀ x, (∫ ω, (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) ∂ν) ≤ d - t →
      ν {ω | d < (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-2 * t^2 / Fintype.card K))) ∧
    (∀ e, (∫ ω, ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) ∂ν) ≤
        (b + iota / 2) * ell →
      ν {ω | (b + iota) * ell ≤
        ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(iota^2 / (8 + 2 * iota)) * ell))) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset E) := ⊤
  let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a)) (gamma / Delta)
  have hlaw := NibbleProductSamplingLaw Q gamma hg hgD
  letI : IsProbabilityMeasure ν := hlaw.1
  obtain ⟨hmeas, hind, _⟩ := NibbleSelectedSetProductLaw Q gamma hg hgD
  let X : K → ((Sigma fun a => Fin (Q.size a)) → ℝ × ℝ) → Finset E :=
    fun a ω => NibbleSelectedEdges Q ω a
  change (∀ x, _ → ν _ ≤ _) ∧ (∀ e, _ → ν _ ≤ _)
  constructor
  · intro x hmean
    have htail := FiniteIndependentBoundedDifferences ν X hmeas hind
      (fun S => (LineGraphOfHypergraph H).IsIndepSet (S : Set E)) hlaw.2.2.2.2.1
      (fun I => (NibbleResidualDegree H I x : ℝ))
      (fun I J hI hJ a hagree => by
        convert NibbleResidualDegreeBoundedDifference H I J a (hI a) (hJ a) hagree x
          using 1
        simp only [NibbleResidualDegree]
        congr 4 <;> ext e <;> simp)
      hK t ht
    refine le_trans (measure_mono ?_) htail
    intro ω hω
    change d < (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) at hω
    change (∫ ω, (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) ∂ν) + t ≤ _
    linarith
  · intro e hmean
    let R : K → Finset E → Prop := fun _ S =>
      ∃ f ∈ S, (LineGraphOfHypergraph H).Adj e f
    have hℓ : (0 : ℝ) < ell := Nat.cast_pos.mpr hell
    have hs : 0 < iota * ell / 2 := by positivity
    have htail := FiniteIndependentBernoulliCountTail ν X hmeas hind
      (M e) R (iota * ell / 2) hs
    have heq : ∀ ω, (( (M e).filter fun a => R a (X a ω)).card : ℝ) =
        ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) := fun _ => rfl
    dsimp only at htail
    simp_rw [heq, hM e] at htail
    obtain ⟨hμ0, hμℓ, htail⟩ := htail
    have hden : 0 < 2 * (∫ ω,
        ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) ∂ν) +
        iota * ell / 2 :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hμ0) hs
    have htail' := htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg (iota * (ell : ℝ) / 2))
        hden (by linarith : 2 * (∫ ω,
          ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) ∂ν) +
          iota * ell / 2 ≤ 2 * ell + iota * ell / 2)))))
    have halg : -((iota * (ell : ℝ) / 2)^2 / (2 * ell + iota * ell / 2)) =
        -(iota^2 / (8 + 2 * iota)) * ell := by
      have hd : (0 : ℝ) < 8 + 2 * iota := by positivity
      have hd' : (0 : ℝ) < 2 * ell + iota * ell / 2 := by positivity
      field_simp
      <;> ring
    rw [halg] at htail'
    refine le_trans (measure_mono ?_) htail'
    intro ω hω
    change (b + iota) * ell ≤
      ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) at hω
    change (∫ ω, ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) ∂ν) +
      iota * ell / 2 ≤ _
    linarith
