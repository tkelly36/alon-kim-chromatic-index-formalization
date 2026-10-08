import Tablet.LocalBParameter

-- [TABLET NODE: LocalBParameterStrictIncrease]
theorem LocalBParameterStrictIncrease
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (v : V) (w : W) (M r : ℕ) (hM : 0 < M)
    (hd : H.degree w = G.degree v + 1)
    (hp : IndependentPairCount H w ≤ IndependentPairCount G v + r)
    (ht : IndependentTripleCount G v ≤ IndependentTripleCount H w)
    (hr : r < M) : LocalBParameter G M v < LocalBParameter H M w := by
-- BODY
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hrlt : (r : ℝ) < M := by exact_mod_cast hr
  have hcore : (0 : ℝ) < 1 / (M : ℝ) - (r : ℝ) / (M : ℝ) ^ 2 := by
    rw [show (1 : ℝ) / (M : ℝ) - (r : ℝ) / (M : ℝ) ^ 2 =
        ((M : ℝ) - r) / (M : ℝ) ^ 2 by field_simp [hMpos.ne']]
    exact div_pos (sub_pos.mpr hrlt) (pow_pos hMpos 2)
  have hpR : (IndependentPairCount H w : ℝ) ≤ (IndependentPairCount G v : ℝ) + r := by
    exact_mod_cast hp
  have htR : (IndependentTripleCount G v : ℝ) ≤ (IndependentTripleCount H w : ℝ) := by
    exact_mod_cast ht
  have hdR : (H.degree w : ℝ) = (G.degree v : ℝ) + 1 := by exact_mod_cast hd
  have hpdiv := div_le_div_of_nonneg_right hpR (le_of_lt (pow_pos hMpos 2))
  have htdiv := div_le_div_of_nonneg_right htR (le_of_lt (pow_pos hMpos 3))
  have hddiv : (H.degree w : ℝ) / (M : ℝ) =
      (G.degree v : ℝ) / (M : ℝ) + 1 / (M : ℝ) := by rw [hdR, add_div]
  simp only [add_div] at hpdiv
  unfold LocalBParameter
  linarith
