import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open BigOperators
open MeasureTheory Set

-- [TABLET NODE: SamplingFiniteProductLowerOrthantEqualityMeasurable]
theorem SamplingFiniteProductLowerOrthantEqualityMeasurable
    {Ω V : Type*} [MeasurableSpace Ω] [Fintype V] [DecidableEq V]
    (ν : MeasureTheory.Measure Ω)
    (F : Ω → Prop) (p : Ω → V → ℝ)
    (hp_meas : Measurable p)
    (M : ENNReal)
    (C : Set (V → ℝ))
    (hC_meas : MeasurableSet C)
    (hC_cube : C ⊆ {q : V → ℝ | ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1})
    (hfinite_atom : ν {ω | F ω} ≠ ⊤)
    (hM : M = ν {ω | F ω})
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            F ω ∧
              ∀ v : V, 0 ≤ p ω v ∧ p ω v ≤ t v} =
            M * ENNReal.ofReal (∏ v : V, t v)) :
    ν ({ω | F ω ∧ p ω ∈ C} ∩
        {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}) =
    M * MeasureTheory.volume C := by
-- BODY
  classical
  let cube : Set (V → ℝ) := {q | ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1}
  let cubeΩ : Set Ω := {ω | ∀ v : V, p ω v ∈ Set.Icc (0 : ℝ) 1}
  let μ : Measure (V → ℝ) := (ν.restrict ({ω | F ω} ∩ cubeΩ)).map p
  let ρ : Measure (V → ℝ) := M • (volume.restrict cube)
  have hC_cube' : C ⊆ cube := by
    simpa [cube] using hC_cube
  have hM_ne_top : M ≠ ⊤ := by
    rw [hM]
    exact hfinite_atom
  have hμ_finite : μ Set.univ < ⊤ := by
    calc
      μ Set.univ = ν ({ω | F ω} ∩ cubeΩ) := by
        simp [μ, hp_meas, cubeΩ]
      _ ≤ ν {ω | F ω} := measure_mono (inter_subset_left)
      _ = M := hM.symm
      _ < ⊤ := lt_top_iff_ne_top.mpr hM_ne_top
  haveI : IsFiniteMeasure μ := ⟨hμ_finite⟩
  have hρ_univ : ρ Set.univ = M := by
    have hvol_cube : volume cube = 1 := by
      have hIcc :
          cube = Set.Icc (fun _ : V => (0 : ℝ)) (fun _ : V => (1 : ℝ)) := by
        ext q
        simp [cube, Set.mem_Icc, Pi.le_def, forall_and]
      rw [hIcc, Real.volume_Icc_pi]
      simp
    simp [ρ, hvol_cube]
  have hμ_univ : μ Set.univ = M := by
    have hone : ∀ v : V, (fun _ : V => (1 : ℝ)) v ∈ Set.Icc (0 : ℝ) 1 := by
      intro v
      simp
    have hrect := hlower_rect (fun _ : V => (1 : ℝ)) hone
    have hset :
        {ω | F ω ∧ ∀ v : V, 0 ≤ p ω v ∧ p ω v ≤ (fun _ : V => (1 : ℝ)) v} =
          {ω | F ω} ∩ cubeΩ := by
      ext ω
      simp [cubeΩ, Set.mem_Icc]
    calc
      μ Set.univ = ν ({ω | F ω} ∩ cubeΩ) := by
        simp [μ, hp_meas, cubeΩ]
      _ = ν {ω | F ω ∧ ∀ v : V, 0 ≤ p ω v ∧ p ω v ≤ (fun _ : V => (1 : ℝ)) v} := by
        rw [hset]
      _ = M := by
        rw [hrect]
        simp
  have hμρ_univ : μ Set.univ = ρ Set.univ := by
    rw [hμ_univ, hρ_univ]
  have h_eq_on_generators :
      ∀ s ∈ (Set.pi Set.univ '' Set.pi Set.univ fun _ : V => (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ))),
        μ s = ρ s := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    have hr' : ∀ v : V, ∃ a : ℝ, r v = Set.Iic a := by
      intro v
      rcases hr v (Set.mem_univ v) with ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    choose a ha using hr'
    have hbox :
        Set.pi Set.univ r = Set.Iic a := by
      ext q
      simp [Set.mem_pi, ha, Set.mem_Iic, Pi.le_def]
    rw [hbox]
    by_cases hneg : ∃ v : V, a v < 0
    · rcases hneg with ⟨v0, hv0⟩
      have hpre_empty :
          p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ) = (∅ : Set Ω) := by
        rw [eq_empty_iff_forall_notMem]
        intro ω hω
        have hp_le : p ω v0 ≤ a v0 := hω.1 v0
        have hnonneg : 0 ≤ p ω v0 := (hω.2.2 v0).1
        exact (not_le_of_gt hv0) (hnonneg.trans hp_le)
      have hcube_box_empty : Set.Iic a ∩ cube = (∅ : Set (V → ℝ)) := by
        rw [eq_empty_iff_forall_notMem]
        intro q hq
        have hq_le : q v0 ≤ a v0 := hq.1 v0
        have hnonneg : 0 ≤ q v0 := (hq.2 v0).1
        exact (not_le_of_gt hv0) (hnonneg.trans hq_le)
      calc
        μ (Set.Iic a) = ν (p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ)) := by
          change Measure.map p (ν.restrict ({ω | F ω} ∩ cubeΩ)) (Set.Iic a) =
            ν (p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ))
          rw [Measure.map_apply hp_meas measurableSet_Iic, Measure.restrict_apply]
          exact measurableSet_Iic.preimage hp_meas
        _ = 0 := by rw [hpre_empty, measure_empty]
        _ = ρ (Set.Iic a) := by
          change 0 = (M • volume.restrict cube) (Set.Iic a)
          rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hcube_box_empty,
            measure_empty]
          simp [smul_eq_mul]
    · have hnonneg : ∀ v : V, 0 ≤ a v := by
        intro v
        exact le_of_not_gt (by intro hv; exact hneg ⟨v, hv⟩)
      let t : V → ℝ := fun v => min (a v) 1
      have ht_mem : ∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1 := by
        intro v
        dsimp [t]
        exact ⟨le_min (hnonneg v) zero_le_one, min_le_right _ _⟩
      have hpre_rect :
          p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ) =
            {ω | F ω ∧ ∀ v : V, 0 ≤ p ω v ∧ p ω v ≤ t v} := by
        ext ω
        constructor
        · intro hω
          refine ⟨hω.2.1, fun v => ?_⟩
          exact ⟨(hω.2.2 v).1, le_min (hω.1 v) (hω.2.2 v).2⟩
        · intro hω
          refine ⟨?_, ?_⟩
          · intro v
            exact (hω.2 v).2.trans (min_le_left _ _)
          · exact ⟨hω.1, fun v => ⟨(hω.2 v).1, (hω.2 v).2.trans (min_le_right _ _)⟩⟩
      have hcube_box :
          Set.Iic a ∩ cube =
            Set.Icc (fun _ : V => (0 : ℝ)) t := by
        ext q
        constructor
        · intro hq
          exact ⟨fun v => (hq.2 v).1, fun v => le_min (hq.1 v) (hq.2 v).2⟩
        · intro hq
          exact ⟨fun v => (hq.2 v).trans (min_le_left _ _),
            fun v => ⟨hq.1 v, (hq.2 v).trans (min_le_right _ _)⟩⟩
      calc
        μ (Set.Iic a) = ν (p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ)) := by
          change Measure.map p (ν.restrict ({ω | F ω} ∩ cubeΩ)) (Set.Iic a) =
            ν (p ⁻¹' Set.Iic a ∩ ({ω | F ω} ∩ cubeΩ))
          rw [Measure.map_apply hp_meas measurableSet_Iic, Measure.restrict_apply]
          exact measurableSet_Iic.preimage hp_meas
        _ = M * ENNReal.ofReal (∏ v : V, t v) := by
          rw [hpre_rect, hlower_rect t ht_mem]
        _ = ρ (Set.Iic a) := by
          change M * ENNReal.ofReal (∏ v : V, t v) =
            (M • volume.restrict cube) (Set.Iic a)
          rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hcube_box,
            Real.volume_Icc_pi]
          simp [smul_eq_mul, t, ENNReal.ofReal_prod_of_nonneg,
            fun v : V => le_min (hnonneg v) zero_le_one]
  have h_gen :
      (inferInstance : MeasurableSpace (V → ℝ)) =
        MeasurableSpace.generateFrom
          (Set.pi Set.univ '' Set.pi Set.univ fun _ : V =>
            (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ))) := by
    have hspanIic :
        IsCountablySpanning (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ)) := by
      refine ⟨fun n : ℕ => Set.Iic (n : ℝ), ?_, ?_⟩
      · intro n
        exact ⟨(n : ℝ), rfl⟩
      · rw [Set.eq_univ_iff_forall]
        intro x
        rcases exists_nat_ge x with ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa using hn⟩
    symm
    refine generateFrom_eq_pi (α := fun _ : V => ℝ)
      (C := fun _ : V => (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ)))
      (fun _ => ?_) (fun _ => ?_)
    · exact (borel_eq_generateFrom_Iic (α := ℝ)).symm
    · exact hspanIic
  have h_pi :
      IsPiSystem
        (Set.pi Set.univ '' Set.pi Set.univ fun _ : V =>
          (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ))) := by
    exact IsPiSystem.pi (fun _ => isPiSystem_Iic)
  have hμρ : μ = ρ := by
    exact ext_of_generate_finite
      (Set.pi Set.univ '' Set.pi Set.univ fun _ : V =>
        (Set.range (fun a : ℝ => Set.Iic a) : Set (Set ℝ)))
      h_gen h_pi h_eq_on_generators hμρ_univ
  calc
    ν ({ω | F ω ∧ p ω ∈ C} ∩ cubeΩ) = μ C := by
      rw [show μ C = ν (p ⁻¹' C ∩ ({ω | F ω} ∩ cubeΩ)) by
        change Measure.map p (ν.restrict ({ω | F ω} ∩ cubeΩ)) C =
          ν (p ⁻¹' C ∩ ({ω | F ω} ∩ cubeΩ))
        rw [Measure.map_apply hp_meas hC_meas, Measure.restrict_apply]
        exact hC_meas.preimage hp_meas]
      congr 1
      ext ω
      simp [cubeΩ, and_assoc, and_left_comm]
    _ = ρ C := by rw [hμρ]
    _ = M * volume C := by
      change (M • volume.restrict cube) C = M * volume C
      rw [Measure.smul_apply, Measure.restrict_apply hC_meas]
      rw [Set.inter_eq_left.mpr hC_cube']
      simp [smul_eq_mul]
