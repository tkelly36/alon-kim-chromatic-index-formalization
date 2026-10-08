import Tablet.RandomIndependentSetSampling

open BigOperators
open MeasureTheory

-- [TABLET NODE: RandomIndependentSetSamplingGammaLeDelta]
theorem RandomIndependentSetSamplingGammaLeDelta {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Delta : ℕ} {gamma : ℝ}
    {μ : Finset V → ℝ} (hV : Nonempty V) (hDelta : 0 < Delta)
    (hsamp : RandomIndependentSetSampling G Delta gamma μ) : gamma ≤ (Delta : ℝ) := by
-- BODY
  rcases hsamp with
    ⟨hgamma_pos, _hμ, ν, hν_univ, hν_A, _hν_prio_mem, _hν_prio,
      _hν_compare, _hpush, _hind⟩
  let A : Finset V := Finset.univ
  have hset_sub : {ω : Finset V × (V → ℝ) | ω.1 = A} ⊆ Set.univ := by
    intro ω _hω
    trivial
  have hmeasure_le : ν {ω : Finset V × (V → ℝ) | ω.1 = A} ≤ (1 : ENNReal) := by
    simpa [hν_univ] using MeasureTheory.measure_mono (μ := ν) hset_sub
  have hcard_pos : 0 < A.card := by
    simpa [A] using Fintype.card_pos_iff.mpr hV
  have hpow_le_enn : ENNReal.ofReal ((gamma / (Delta : ℝ)) ^ A.card) ≤ (1 : ENNReal) := by
    rw [hν_A A] at hmeasure_le
    simpa [A] using hmeasure_le
  have hpow_le_real : (gamma / (Delta : ℝ)) ^ A.card ≤ 1 := by
    exact ENNReal.ofReal_le_one.mp hpow_le_enn
  have hratio_le : gamma / (Delta : ℝ) ≤ 1 := by
    by_contra hnot
    have hlt : 1 < gamma / (Delta : ℝ) := lt_of_not_ge hnot
    have hpow_gt : 1 < (gamma / (Delta : ℝ)) ^ A.card := one_lt_pow₀ hlt hcard_pos.ne'
    linarith
  exact (div_le_one (by positivity : (0 : ℝ) < (Delta : ℝ))).mp hratio_le
