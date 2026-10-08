import Tablet.LocalBParameterReal
import Tablet.IndependentPairCountLeChooseNeighborCard
import Mathlib.Data.Nat.Choose.Cast

-- [TABLET NODE: LocalBParameterRealAntitone]
theorem LocalBParameterRealAntitone {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {M N : ℝ} (hM : 0 < M) (hMN : M ≤ N) (hdM : (G.degree v : ℝ) ≤ M) :
    LocalBParameterReal G N v ≤ LocalBParameterReal G M v := by
-- BODY
  let d : ℝ := G.degree v
  let P : ℝ := IndependentPairCount G v
  let T : ℝ := IndependentTripleCount G v
  have hd : 0 ≤ d := by positivity
  have hP : 0 ≤ P := by positivity
  have hT : 0 ≤ T := by positivity
  have hpairs : 2 * P ≤ d * (d - 1) := by
    have h := IndependentPairCountLeChooseNeighborCard G v
    have hr : P ≤ ((G.neighborFinset v).card.choose 2 : ℝ) := by
      dsimp [P]
      exact_mod_cast h
    rw [Nat.cast_choose_two, G.card_neighborFinset_eq_degree] at hr
    dsimp [d]
    linarith
  have hPM : 2 * P ≤ d * M := by
    have hh := mul_le_mul_of_nonneg_left hdM hd
    change d * d ≤ d * M at hh
    nlinarith
  have hN : 0 < N := lt_of_lt_of_le hM hMN
  let x := M⁻¹
  let y := N⁻¹
  have hx : 0 ≤ x := le_of_lt (inv_pos.mpr hM)
  have hy : 0 ≤ y := le_of_lt (inv_pos.mpr hN)
  have hyx : y ≤ x := (inv_le_inv₀ hN hM).mpr hMN
  have hPx : 2 * P * x ≤ d := by
    dsimp [x]
    exact (mul_inv_le_iff₀ hM).mpr hPM
  have hPxy : P * (x + y) ≤ d := by
    have hh := mul_le_mul_of_nonneg_left hyx hP
    nlinarith
  have hbr : 0 ≤ d - P * (x + y) + T * (x^2 + x*y + y^2) := by
    exact add_nonneg (sub_nonneg.mpr hPxy) (mul_nonneg hT (by positivity))
  have hfac : LocalBParameterReal G M v - LocalBParameterReal G N v =
      (x-y) * (d-P*(x+y)+T*(x^2+x*y+y^2)) := by
    simp only [LocalBParameterReal, d, P, T, x, y, div_eq_mul_inv, inv_pow]
    ring
  have hh := mul_nonneg (sub_nonneg.mpr hyx) hbr
  rw [← hfac] at hh
  linarith
