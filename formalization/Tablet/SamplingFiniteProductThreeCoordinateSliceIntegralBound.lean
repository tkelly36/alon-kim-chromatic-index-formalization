import Tablet.RandomIndependentSetSampling
import Tablet.SamplingMeasurePreservingTripleSliceIntegralBound
import Tablet.SamplingThreeCoordinateComplementMeasurePreserving
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingFiniteProductThreeCoordinateSliceIntegralBound]
theorem SamplingFiniteProductThreeCoordinateSliceIntegralBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b c : V)
    (E : Set (V → ℝ))
    (g : ℝ → ℝ → ℝ → ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE_meas : MeasurableSet E)
    (hg_cont : Continuous fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (hg_nonneg :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 → 0 ≤ g x y z)
    (hE :
      E ⊆
        {q : V → ℝ |
          q a ∈ Set.Icc (0 : ℝ) 1 ∧ q a ≤ q b ∧ q b ≤ q c ∧
            q c ∈ Set.Icc (0 : ℝ) 1})
    (hslice :
      ∀ x y z : ℝ,
        0 ≤ x → x ≤ y → y ≤ z → z ≤ 1 →
          MeasureTheory.volume
              {r : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} → ℝ |
                ∃ q : V → ℝ,
                  q ∈ E ∧ q a = x ∧ q b = y ∧ q c = z ∧
                    ∀ v : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}, q v.1 = r v} ≤
            ENNReal.ofReal (g x y z)) :
    MeasureTheory.volume E ≤
      ENNReal.ofReal
        (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y, g x y z) := by
-- BODY
  classical
  let W := {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} → ℝ
  let Φ : (V → ℝ) → ℝ × ℝ × ℝ × W :=
    fun q => (q a, q b, q c, fun v : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} => q v.1)
  let Ψ : ℝ × ℝ × ℝ × W → V → ℝ :=
    fun p v =>
      if hva : v = a then p.1
      else if hvb : v = b then p.2.1
      else if hvc : v = c then p.2.2.1
      else p.2.2.2 ⟨v, hva, hvb, hvc⟩
  let A : Set (ℝ × ℝ × ℝ × W) := Ψ ⁻¹' E
  have hΨ_meas : Measurable Ψ := by
    apply measurable_pi_lambda
    intro v
    by_cases hva : v = a
    · simp [Ψ, hva]
      measurability
    · by_cases hvb : v = b
      · simp [Ψ, hvb]
        measurability
      · by_cases hvc : v = c
        · simp [Ψ, hvc]
          measurability
        · simp [Ψ, hva, hvb, hvc]
          measurability
  have hA_meas : MeasurableSet A := by
    exact hE_meas.preimage hΨ_meas
  refine
    SamplingMeasurePreservingTripleSliceIntegralBound
      (X := V → ℝ) (W := W) Φ E A g
      ?_ hA_meas hg_cont hg_nonneg ?_ ?_ ?_
  · simpa [Φ, W] using
      SamplingThreeCoordinateComplementMeasurePreserving a b c hab hac hbc
  · intro q hq
    change Ψ (Φ q) ∈ E
    have hΨΦ : Ψ (Φ q) = q := by
      funext v
      by_cases hva : v = a
      · simp [Ψ, Φ, hva]
      · by_cases hvb : v = b
        · simp [Ψ, Φ, W, hvb, Ne.symm hab]
        · by_cases hvc : v = c
          · simp [Ψ, Φ, W, hvc, Ne.symm hac, Ne.symm hbc]
          · simp [Ψ, Φ, W, hva, hvb, hvc]
    simpa [hΨΦ] using hq
  · intro p hp
    have h := hE hp
    simpa [A, Ψ, W, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] using h
  · intro x y z hx0 hxy hyz hz1
    refine (MeasureTheory.measure_mono ?_).trans (hslice x y z hx0 hxy hyz hz1)
    intro w hw
    refine ⟨Ψ (x, y, z, w), hw, ?_, ?_, ?_, ?_⟩
    · simp [Ψ]
    · simp [Ψ, Ne.symm hab]
    · simp [Ψ, Ne.symm hac, Ne.symm hbc]
    · intro v
      simp [Ψ, W, v.2.1, v.2.2.1, v.2.2.2]
