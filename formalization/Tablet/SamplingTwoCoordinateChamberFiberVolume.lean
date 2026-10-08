import Tablet.SamplingTwoCoordinateFiberBoxVolume
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open BigOperators

-- [TABLET NODE: SamplingTwoCoordinateChamberFiberVolume]
theorem SamplingTwoCoordinateChamberFiberVolume
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (BU BT : Finset V)
    (huv : u ≠ v)
    (hBUQ : Disjoint BU ({u, v} : Finset V))
    (hBTQ : Disjoint BT ({u, v} : Finset V))
    (hBT : Disjoint BU BT)
    (a b : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    MeasureTheory.volume
        {r : {w : V // w ≠ u ∧ w ≠ v} → ℝ |
          (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < a) ∧
          (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < b)} =
      ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
-- BODY
  classical
  let β := {w : V // w ≠ u ∧ w ≠ v}
  let upper : β → ℝ :=
    fun w => if w.1 ∈ BU then a else if w.1 ∈ BT then b else 1
  let S : Set (β → ℝ) :=
        {r : β → ℝ |
          (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < a) ∧
          (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < b)}
  have hIco := SamplingTwoCoordinateFiberBoxVolume (V := V)
    u v BU BT huv hBUQ hBTQ hBT a b ha0 hb0 hba ha1
  have hprod : (∏ i : β, ENNReal.ofReal (upper i - 0)) =
      ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
    rw [Real.volume_pi_Ico] at hIco
    simpa [β, upper] using hIco
  have hIcc :
      MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) =
        ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
    rw [Real.volume_Icc_pi]
    simpa [upper] using hprod
  have hlow : (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) ⊆ S := by
    intro r hr
    constructor
    · intro w
      have hw := hr w (by simp)
      by_cases hBU : w.1 ∈ BU
      · have : r w ∈ Set.Ico (0 : ℝ) a := by
          simpa [upper, hBU] using hw
        exact ⟨this.1, le_trans (le_of_lt this.2) ha1⟩
      · by_cases hBTm : w.1 ∈ BT
        · have : r w ∈ Set.Ico (0 : ℝ) b := by
            simpa [upper, hBU, hBTm] using hw
          exact ⟨this.1, le_trans (le_of_lt this.2) (le_trans hba ha1)⟩
        · have : r w ∈ Set.Ico (0 : ℝ) 1 := by
            simpa [upper, hBU, hBTm] using hw
          exact ⟨this.1, le_of_lt this.2⟩
    constructor
    · intro z hzBU hz
      have hw := hr ⟨z, hz⟩ (by simp)
      simpa [upper, hzBU] using hw.2
    · intro z hzBT hz
      have hzBU : z ∉ BU := by
        intro hzBU
        exact Finset.disjoint_left.mp hBT hzBU hzBT
      have hw := hr ⟨z, hz⟩ (by simp)
      simpa [upper, hzBU, hzBT] using hw.2
  have hhigh : S ⊆ Set.Icc (fun _ : β => (0 : ℝ)) upper := by
    intro r hr
    constructor
    · intro w
      exact (hr.1 w).1
    · intro w
      by_cases hBU : w.1 ∈ BU
      · have hlt := hr.2.1 w.1 hBU w.2
        simpa [upper, hBU] using le_of_lt hlt
      · by_cases hBTm : w.1 ∈ BT
        · have hlt := hr.2.2 w.1 hBTm w.2
          simpa [upper, hBU, hBTm] using le_of_lt hlt
        · exact (by simpa [upper, hBU, hBTm] using (hr.1 w).2)
  apply le_antisymm
  · calc
      MeasureTheory.volume
          {r : β → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < a) ∧
            (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < b)}
          = MeasureTheory.volume S := rfl
      _ ≤ MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) :=
        MeasureTheory.measure_mono hhigh
      _ = ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := hIcc
  · calc
      ENNReal.ofReal (a ^ BU.card * b ^ BT.card)
          = MeasureTheory.volume (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) :=
        hIco.symm
      _ ≤ MeasureTheory.volume S := MeasureTheory.measure_mono hlow
      _ = MeasureTheory.volume
          {r : β → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ BU → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < a) ∧
            (∀ z : V, z ∈ BT → ∀ hz : z ≠ u ∧ z ≠ v, r ⟨z, hz⟩ < b)} := rfl
