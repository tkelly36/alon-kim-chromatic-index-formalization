import Tablet.SamplingOneCoordinateComplementMeasurePreserving
import Tablet.SamplingOneCoordinateChamberFiberVolume
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingOneCoordinateChamberVolume]
theorem SamplingOneCoordinateChamberVolume
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (B : Finset V) (hvB : v ∉ B) :
    MeasureTheory.volume
      {q : V → ℝ |
        (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ z : V, z ∈ B → q z < q v)} =
      ENNReal.ofReal (∫ a in (0 : ℝ)..1, a ^ B.card) := by
-- BODY
  classical
  let W := {w : V // w ≠ v}
  let Φ : (V → ℝ) → ℝ × (W → ℝ) :=
    fun q => (q v, fun w : W => q w.1)
  let E : Set (V → ℝ) :=
    {q : V → ℝ |
      (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ z : V, z ∈ B → q z < q v)}
  let A : Set (ℝ × (W → ℝ)) :=
    {p : ℝ × (W → ℝ) |
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ w : W, p.2 w ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ z : V, z ∈ B → ∀ hz : z ≠ v, p.2 ⟨z, hz⟩ < p.1)}
  have hA_meas : MeasurableSet A := by
    dsimp [A, W]
    measurability
  have hpre : Φ ⁻¹' A = E := by
    ext q
    constructor
    · intro hq
      dsimp [Φ, A, E, W] at hq ⊢
      constructor
      · intro x
        by_cases hxv : x = v
        · simpa [hxv] using hq.1
        · exact hq.2.1 ⟨x, hxv⟩
      · intro z hz
        have hzv : z ≠ v := by
          intro hzv
          exact hvB (by simpa [hzv] using hz)
        exact hq.2.2 z hz hzv
    · intro hq
      dsimp [Φ, A, E, W] at hq ⊢
      constructor
      · exact hq.1 v
      constructor
      · intro w
        exact hq.1 w.1
      · intro z hzB _hz
        exact hq.2 z hzB
  have hmeasure_EA : MeasureTheory.volume E = MeasureTheory.volume A := by
    have hmp := SamplingOneCoordinateComplementMeasurePreserving (V := V) v
    have hmp' : MeasureTheory.MeasurePreserving Φ MeasureTheory.volume
        MeasureTheory.volume := by
      simpa [Φ, W] using hmp
    calc
      MeasureTheory.volume E = MeasureTheory.volume (Φ ⁻¹' A) := by
        rw [hpre]
      _ = MeasureTheory.volume A := hmp'.measure_preimage hA_meas.nullMeasurableSet
  have hsections : MeasureTheory.volume A =
      ∫⁻ a : ℝ,
        (Set.Icc (0 : ℝ) 1).indicator
          (fun a => ENNReal.ofReal (a ^ B.card)) a := by
    have h1 : MeasureTheory.volume A =
        ∫⁻ a : ℝ, MeasureTheory.volume {r : W → ℝ | (a, r) ∈ A} := by
      exact MeasureTheory.Measure.prod_apply hA_meas
    rw [h1]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with a
    by_cases ha : a ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ha]
      have hfiber := SamplingOneCoordinateChamberFiberVolume (V := V)
        v B hvB a ha.1 ha.2
      change MeasureTheory.volume {r : W → ℝ | (a, r) ∈ A} =
        ENNReal.ofReal (a ^ B.card)
      rw [show {r : W → ℝ | (a, r) ∈ A} =
          {r : W → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ B → ∀ hz : z ≠ v, r ⟨z, hz⟩ < a)} by
        ext r
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨ha, h⟩]
      exact hfiber
    · rw [Set.indicator_of_notMem ha]
      have hempty : {r : W → ℝ | (a, r) ∈ A} = ∅ := by
        ext r
        constructor
        · intro hr
          exact False.elim (ha hr.1)
        · intro hr
          cases hr
      change MeasureTheory.volume {r : W → ℝ | (a, r) ∈ A} = 0
      rw [hempty, MeasureTheory.measure_empty]
  have hconvert :
      (∫⁻ a : ℝ,
        (Set.Icc (0 : ℝ) 1).indicator
          (fun a => ENNReal.ofReal (a ^ B.card)) a) =
        ENNReal.ofReal (∫ a in (0 : ℝ)..1, a ^ B.card) := by
    rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (by
        have hcont : Continuous fun a : ℝ => a ^ B.card := by
          continuity
        rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
        exact hcont.integrableOn_Icc)
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioc |>.2
        (Filter.Eventually.of_forall (fun a ha => pow_nonneg (le_of_lt ha.1) _)))).symm
  calc
    MeasureTheory.volume
        {q : V → ℝ |
          (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ z : V, z ∈ B → q z < q v)}
        = MeasureTheory.volume E := rfl
    _ = MeasureTheory.volume A := hmeasure_EA
    _ = ∫⁻ a : ℝ,
        (Set.Icc (0 : ℝ) 1).indicator
          (fun a => ENNReal.ofReal (a ^ B.card)) a := hsections
    _ = ENNReal.ofReal (∫ a in (0 : ℝ)..1, a ^ B.card) := hconvert
