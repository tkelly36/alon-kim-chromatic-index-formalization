import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open BigOperators

-- [TABLET NODE: SamplingOneCoordinateChamberFiberVolume]
theorem SamplingOneCoordinateChamberFiberVolume
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (B : Finset V) (hvB : v ∉ B)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    MeasureTheory.volume
        {r : {w : V // w ≠ v} → ℝ |
          (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ z : V, z ∈ B → ∀ hz : z ≠ v, r ⟨z, hz⟩ < a)} =
      ENNReal.ofReal (a ^ B.card) := by
-- BODY
  classical
  let β := {w : V // w ≠ v}
  let upper : β → ℝ := fun w => if w.1 ∈ B then a else 1
  let S : Set (β → ℝ) :=
    {r : β → ℝ |
      (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ z : V, z ∈ B → ∀ hz : z ≠ v, r ⟨z, hz⟩ < a)}
  have hprod :
      (∏ i : β, ENNReal.ofReal (upper i - 0)) =
        ENNReal.ofReal (a ^ B.card) := by
    let C : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ B)
    have hCcard : C.card = B.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ C) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro w hw
        have hwv : w ≠ v := by
          intro hwv
          exact hvB (by simpa [hwv] using hw)
        refine ⟨⟨w, hwv⟩, ?_, rfl⟩
        simp [C, hw]
    let f : β → ENNReal := fun i => ENNReal.ofReal (upper i - 0)
    have hfC : ∀ i ∈ C, f i = ENNReal.ofReal a := by
      intro i hi
      have hiB : i.1 ∈ B := (Finset.mem_filter.mp hi).2
      simp [f, upper, hiB]
    have hfR : ∀ i ∈ ((Finset.univ : Finset β) \ C), f i = 1 := by
      intro i hi
      have hnot : i ∉ C := (Finset.mem_sdiff.mp hi).2
      have hiB : i.1 ∉ B := by
        intro h
        exact hnot (by simp [C, h])
      simp [f, upper, hiB]
    have hCsub : C ⊆ (Finset.univ : Finset β) := by
      intro i _hi
      simp
    have hprod_univ : (∏ i : β, f i) = ∏ i ∈ C, f i := by
      have hs := Finset.prod_sdiff (s₁ := C)
        (s₂ := (Finset.univ : Finset β)) (f := f) hCsub
      have hres : (∏ i ∈ ((Finset.univ : Finset β) \ C), f i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact hfR i hi
      rw [hres, one_mul] at hs
      exact hs.symm
    calc
      (∏ i : β, ENNReal.ofReal (upper i - 0)) = ∏ i : β, f i := by simp [f]
      _ = ∏ i ∈ C, f i := hprod_univ
      _ = (ENNReal.ofReal a) ^ C.card := by
        trans ∏ i ∈ C, ENNReal.ofReal a
        · exact Finset.prod_congr rfl (by intro i hi; exact hfC i hi)
        · simp
      _ = ENNReal.ofReal (a ^ B.card) := by
        rw [hCcard, ENNReal.ofReal_pow ha0]
  have hIco :
      MeasureTheory.volume (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) =
        ENNReal.ofReal (a ^ B.card) := by
    rw [Real.volume_pi_Ico]
    exact hprod
  have hIcc :
      MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) =
        ENNReal.ofReal (a ^ B.card) := by
    rw [Real.volume_Icc_pi]
    exact hprod
  have hlow : (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) ⊆ S := by
    intro r hr
    constructor
    · intro w
      have hw := hr w (by simp)
      by_cases hB : w.1 ∈ B
      · have : r w ∈ Set.Ico (0 : ℝ) a := by
          simpa [upper, hB] using hw
        exact ⟨this.1, le_trans (le_of_lt this.2) ha1⟩
      · have : r w ∈ Set.Ico (0 : ℝ) 1 := by
          simpa [upper, hB] using hw
        exact ⟨this.1, le_of_lt this.2⟩
    · intro z hzB hz
      have hw := hr ⟨z, hz⟩ (by simp)
      simpa [upper, hzB] using hw.2
  have hhigh : S ⊆ Set.Icc (fun _ : β => (0 : ℝ)) upper := by
    intro r hr
    constructor
    · intro w
      exact (hr.1 w).1
    · intro w
      by_cases hB : w.1 ∈ B
      · have hlt := hr.2 w.1 hB w.2
        simpa [upper, hB] using le_of_lt hlt
      · exact (by simpa [upper, hB] using (hr.1 w).2)
  apply le_antisymm
  · calc
      MeasureTheory.volume
          {r : β → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ B → ∀ hz : z ≠ v, r ⟨z, hz⟩ < a)}
          = MeasureTheory.volume S := rfl
      _ ≤ MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) :=
        MeasureTheory.measure_mono hhigh
      _ = ENNReal.ofReal (a ^ B.card) := hIcc
  · calc
      ENNReal.ofReal (a ^ B.card)
          = MeasureTheory.volume (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) :=
        hIco.symm
      _ ≤ MeasureTheory.volume S := MeasureTheory.measure_mono hlow
      _ = MeasureTheory.volume
          {r : β → ℝ |
            (∀ w, r w ∈ Set.Icc (0 : ℝ) 1) ∧
            (∀ z : V, z ∈ B → ∀ hz : z ≠ v, r ⟨z, hz⟩ < a)} := rfl
