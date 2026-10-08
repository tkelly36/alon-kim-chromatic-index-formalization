import Tablet.SamplingTwoCoordinateComplementMeasurePreserving
import Tablet.SamplingTwoCoordinateChamberFiberVolume
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option maxHeartbeats 800000

open BigOperators

-- [TABLET NODE: SamplingTwoCoordinateChamberVolume]
theorem SamplingTwoCoordinateChamberVolume
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (BU BT : Finset V)
    (huv : u ≠ v)
    (hBUQ : Disjoint BU ({u, v} : Finset V))
    (hBTQ : Disjoint BT ({u, v} : Finset V))
    (hBT : Disjoint BU BT) :
    MeasureTheory.volume
      {q : V → ℝ |
        (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
        q v ≤ q u ∧
        (∀ z : V, z ∈ BU → q z < q u) ∧
        (∀ z : V, z ∈ BT → q z < q v)} =
      ENNReal.ofReal
        (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
          a ^ BU.card * b ^ BT.card) := by
-- BODY
  classical
  have hconvert : ∀ m n : ℕ,
      (∫⁻ a : ℝ, ∫⁻ b : ℝ,
        ({p : ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1}).indicator
          (fun p => ENNReal.ofReal (p.1 ^ m * p.2 ^ n)) (a, b)) =
        ENNReal.ofReal
          (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, a ^ m * b ^ n) := by
    intro m n
    let S : Set (ℝ × ℝ) :=
      {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1}
    let F : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.1 ^ m * p.2 ^ n)
    have hmeasS : MeasurableSet S := by
      dsimp [S]
      measurability
    have hinner : ∀ a : ℝ,
        (∫⁻ b : ℝ, S.indicator F (a, b)) =
          (Set.Icc (0 : ℝ) 1).indicator
            (fun a => ∫⁻ b in Set.Icc (0 : ℝ) a,
              ENNReal.ofReal (a ^ m * b ^ n)) a := by
      intro a
      by_cases ha : a ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ha]
        rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
        apply MeasureTheory.lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun b => by
          by_cases hb : b ∈ Set.Icc (0 : ℝ) a
          · rw [Set.indicator_of_mem hb]
            have hs : (a, b) ∈ S := ⟨ha, hb⟩
            change S.indicator F (a, b) = ENNReal.ofReal (a ^ m * b ^ n)
            rw [Set.indicator_of_mem hs]
          · rw [Set.indicator_of_notMem hb]
            have hs : (a, b) ∉ S := by
              intro h
              exact hb h.2
            change S.indicator F (a, b) = 0
            rw [Set.indicator_of_notMem hs])
      · rw [Set.indicator_of_notMem ha]
        simpa using (MeasureTheory.lintegral_congr_ae
          (Filter.Eventually.of_forall (fun b => by
            have hs : (a, b) ∉ S := by
              intro h
              exact ha h.1
            change S.indicator F (a, b) = 0
            rw [Set.indicator_of_notMem hs]) :
            (fun b : ℝ => S.indicator F (a, b)) =ᵐ[MeasureTheory.volume]
              fun _ => (0 : ENNReal)))
    have hIccIoc_inner :
        (∫⁻ a in Set.Icc (0 : ℝ) 1, ∫⁻ b in Set.Icc (0 : ℝ) a,
            ENNReal.ofReal (a ^ m * b ^ n)) =
          ∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ b in Set.Ioc (0 : ℝ) a,
            ENNReal.ofReal (a ^ m * b ^ n) := by
      rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
      apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
      intro a _ha
      change (∫⁻ b in Set.Icc (0 : ℝ) a, ENNReal.ofReal (a ^ m * b ^ n)) =
        ∫⁻ b in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (a ^ m * b ^ n)
      rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    calc
      (∫⁻ a : ℝ, ∫⁻ b : ℝ,
        ({p : ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1}).indicator
          (fun p => ENNReal.ofReal (p.1 ^ m * p.2 ^ n)) (a, b))
          = ∫⁻ a : ℝ, ∫⁻ b : ℝ, S.indicator F (a, b) := rfl
      _ = ∫⁻ a in Set.Icc (0 : ℝ) 1, ∫⁻ b in Set.Icc (0 : ℝ) a,
            ENNReal.ofReal (a ^ m * b ^ n) := by
          simp_rw [hinner]
          rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
      _ = ∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ b in Set.Ioc (0 : ℝ) a,
            ENNReal.ofReal (a ^ m * b ^ n) := hIccIoc_inner
      _ = ENNReal.ofReal
            (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a, a ^ m * b ^ n) := by
          have hinner_conv : ∀ a ∈ Set.Ioc (0 : ℝ) 1,
              (∫⁻ b in Set.Ioc (0 : ℝ) a,
                  ENNReal.ofReal (a ^ m * b ^ n)) =
                ENNReal.ofReal (∫ b in (0 : ℝ)..a, a ^ m * b ^ n) := by
            intro a ha
            rw [intervalIntegral.integral_of_le (le_of_lt ha.1)]
            exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (by
                have hcont : Continuous fun b : ℝ => a ^ m * b ^ n := by
                  continuity
                rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
                exact hcont.integrableOn_Icc)
              (MeasureTheory.ae_restrict_iff' measurableSet_Ioc |>.2
                (Filter.Eventually.of_forall (fun b hb => by
                  exact mul_nonneg (pow_nonneg (le_of_lt ha.1) _)
                    (pow_nonneg (le_of_lt hb.1) _))))).symm
          calc
            (∫⁻ a in Set.Ioc (0 : ℝ) 1, ∫⁻ b in Set.Ioc (0 : ℝ) a,
                ENNReal.ofReal (a ^ m * b ^ n))
                = ∫⁻ a in Set.Ioc (0 : ℝ) 1,
                    ENNReal.ofReal (∫ b in (0 : ℝ)..a, a ^ m * b ^ n) := by
                  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
                  intro a ha
                  exact hinner_conv a ha
            _ = ENNReal.ofReal
                  (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
                    a ^ m * b ^ n) := by
                rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
                exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  (by
                    have hcont_uncurry :
                        Continuous (Function.uncurry
                          (fun a b : ℝ => a ^ m * b ^ n)) := by
                      change Continuous (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ n)
                      continuity
                    have hGcont :
                        Continuous fun a : ℝ =>
                          ∫ b in (0 : ℝ)..a, a ^ m * b ^ n := by
                      simpa [Function.uncurry] using
                        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
                          (f := fun a b : ℝ => a ^ m * b ^ n)
                          (a₀ := (0 : ℝ)) hcont_uncurry continuous_id)
                    rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
                    exact hGcont.integrableOn_Icc)
                  (MeasureTheory.ae_restrict_iff' measurableSet_Ioc |>.2
                    (Filter.Eventually.of_forall (fun a ha => by
                      refine intervalIntegral.integral_nonneg (le_of_lt ha.1) ?_
                      intro b hb
                      exact mul_nonneg (pow_nonneg (le_of_lt ha.1) _)
                        (pow_nonneg hb.1 _))))).symm
  let W := {w : V // w ≠ u ∧ w ≠ v}
  let Φ : (V → ℝ) → ℝ × ℝ × (W → ℝ) :=
    fun q => (q u, q v, fun w : W => q w.1)
  let E : Set (V → ℝ) :=
    {q : V → ℝ |
      (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
      q v ≤ q u ∧
      (∀ z : V, z ∈ BU → q z < q u) ∧
      (∀ z : V, z ∈ BT → q z < q v)}
  let A : Set (ℝ × ℝ × (W → ℝ)) :=
    {p : ℝ × ℝ × (W → ℝ) |
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      p.2.1 ∈ Set.Icc (0 : ℝ) p.1 ∧
      (∀ w : W, p.2.2 w ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v,
        p.2.2 ⟨z, hz⟩ < p.1) ∧
      (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v,
        p.2.2 ⟨z, hz⟩ < p.2.1)}
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
        by_cases hxu : x = u
        · simpa [hxu] using hq.1
        · by_cases hxv : x = v
          · simpa [hxv] using
              (⟨hq.2.1.1, le_trans hq.2.1.2 hq.1.2⟩ :
                q v ∈ Set.Icc (0 : ℝ) 1)
          · exact hq.2.2.1 ⟨x, hxu, hxv⟩
      constructor
      · exact hq.2.1.2
      constructor
      · intro z hz
        by_cases hzu : z = u
        · have : z ∉ BU := by
            intro hzBU
            have hmem : z ∈ ({u, v} : Finset V) := by
              simp [hzu]
            exact Finset.disjoint_left.mp hBUQ hzBU hmem
          exact False.elim (this hz)
        · by_cases hzv : z = v
          · have : z ∉ BU := by
              intro hzBU
              have hmem : z ∈ ({u, v} : Finset V) := by
                simp [hzv]
              exact Finset.disjoint_left.mp hBUQ hzBU hmem
            exact False.elim (this hz)
          · exact hq.2.2.2.1 z hz ⟨hzu, hzv⟩
      · intro z hz
        by_cases hzu : z = u
        · have : z ∉ BT := by
            intro hzBT
            have hmem : z ∈ ({u, v} : Finset V) := by
              simp [hzu]
            exact Finset.disjoint_left.mp hBTQ hzBT hmem
          exact False.elim (this hz)
        · by_cases hzv : z = v
          · have : z ∉ BT := by
              intro hzBT
              have hmem : z ∈ ({u, v} : Finset V) := by
                simp [hzv]
              exact Finset.disjoint_left.mp hBTQ hzBT hmem
            exact False.elim (this hz)
          · exact hq.2.2.2.2 z hz ⟨hzu, hzv⟩
    · intro hq
      dsimp [Φ, A, E, W] at hq ⊢
      constructor
      · exact hq.1 u
      constructor
      · exact ⟨(hq.1 v).1, hq.2.1⟩
      constructor
      · intro w
        exact hq.1 w.1
      constructor
      · intro z hzBU _hz
        exact hq.2.2.1 z hzBU
      · intro z hzBT _hz
        exact hq.2.2.2 z hzBT
  have hmeasure_EA : MeasureTheory.volume E = MeasureTheory.volume A := by
    have hmp := SamplingTwoCoordinateComplementMeasurePreserving (V := V) u v huv
    have hmp' : MeasureTheory.MeasurePreserving Φ MeasureTheory.volume
        MeasureTheory.volume := by
      simpa [Φ, W] using hmp
    calc
      MeasureTheory.volume E = MeasureTheory.volume (Φ ⁻¹' A) := by
        rw [hpre]
      _ = MeasureTheory.volume A := hmp'.measure_preimage hA_meas.nullMeasurableSet
  have hsections : MeasureTheory.volume A =
      ∫⁻ a : ℝ, ∫⁻ b : ℝ,
        ({p : ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1}).indicator
          (fun p => ENNReal.ofReal (p.1 ^ BU.card * p.2 ^ BT.card)) (a, b) := by
    have h1 : MeasureTheory.volume A =
        ∫⁻ a : ℝ, MeasureTheory.volume {br : ℝ × (W → ℝ) | (a, br) ∈ A} := by
      exact MeasureTheory.Measure.prod_apply hA_meas
    rw [h1]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with a
    let B : Set (ℝ × (W → ℝ)) := {br | (a, br) ∈ A}
    have hB_meas : MeasurableSet B := measurable_prodMk_left hA_meas
    have h2 : MeasureTheory.volume B =
        ∫⁻ b : ℝ, MeasureTheory.volume {r : W → ℝ | (b, r) ∈ B} := by
      exact MeasureTheory.Measure.prod_apply hB_meas
    rw [show MeasureTheory.volume {br : ℝ × (W → ℝ) | (a, br) ∈ A} =
        MeasureTheory.volume B by rfl]
    rw [h2]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with b
    by_cases hs : a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) a
    · have ha0 : 0 ≤ a := hs.1.1
      have ha1 : a ≤ 1 := hs.1.2
      have hb0 : 0 ≤ b := hs.2.1
      have hba : b ≤ a := hs.2.2
      have hfiber := SamplingTwoCoordinateChamberFiberVolume (V := V)
        u v BU BT huv hBUQ hBTQ hBT a b ha0 hb0 hba ha1
      have hmem : (a, b) ∈
          {p : ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1} := hs
      rw [Set.indicator_of_mem hmem]
      change MeasureTheory.volume {r : W → ℝ | (a, b, r) ∈ A} =
        ENNReal.ofReal (a ^ BU.card * b ^ BT.card)
      rw [show {r : W → ℝ | (a, b, r) ∈ A} =
          {r : W → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v,
              r ⟨z, hz⟩ < a) ∧
            (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v,
              r ⟨z, hz⟩ < b)} by
        ext r
        constructor
        · intro h
          exact h.2.2
        · intro h
          exact ⟨hs.1, hs.2, h⟩]
      exact hfiber
    · have hnotmem : (a, b) ∉
          {p : ℝ × ℝ |
            p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) p.1} := hs
      rw [Set.indicator_of_notMem hnotmem]
      have hempty : {r : W → ℝ | (a, b, r) ∈ A} = ∅ := by
        ext r
        constructor
        · intro hr
          exact False.elim (hs ⟨hr.1, hr.2.1⟩)
        · intro hr
          cases hr
      change MeasureTheory.volume {r : W → ℝ | (a, b, r) ∈ A} = 0
      rw [hempty, MeasureTheory.measure_empty]
  calc
    MeasureTheory.volume
        {q : V → ℝ |
          (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
          q v ≤ q u ∧
          (∀ z : V, z ∈ BU → q z < q u) ∧
          (∀ z : V, z ∈ BT → q z < q v)}
        = MeasureTheory.volume E := rfl
    _ = MeasureTheory.volume A := hmeasure_EA
    _ = _ := hsections
    _ = ENNReal.ofReal
        (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..a,
          a ^ BU.card * b ^ BT.card) := hconvert BU.card BT.card
