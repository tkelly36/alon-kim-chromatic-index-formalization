import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi

open BigOperators

-- [TABLET NODE: SamplingOneCoordinateComplementMeasurePreserving]
theorem SamplingOneCoordinateComplementMeasurePreserving
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) :
    MeasureTheory.MeasurePreserving
      (fun q : V → ℝ => (q v, fun w : {w : V // w ≠ v} => q w.1))
      MeasureTheory.volume
      MeasureTheory.volume := by
-- BODY
  let W := {w : V // w ≠ v}
  let eIdx : (Unit ⊕ W) ≃ V :=
    { toFun := fun i =>
        match i with
        | Sum.inl _ => v
        | Sum.inr w => w.1
      invFun := fun x =>
        if hv : x = v then Sum.inl ()
        else Sum.inr ⟨x, hv⟩
      left_inv := by
        intro i
        cases i with
        | inl j =>
            cases j
            simp
        | inr w =>
            rcases w with ⟨w, hwv⟩
            simp [hwv]
      right_inv := by
        intro x
        by_cases hv : x = v
        · simp [hv]
        · simp [hv] }
  let eSplit : ((Unit ⊕ W) → ℝ) ≃ᵐ ((Unit → ℝ) × (W → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ W => ℝ)
  let eHead : (Unit → ℝ) ≃ᵐ ℝ :=
    MeasurableEquiv.funUnique Unit ℝ
  let eTuple : ((Unit → ℝ) × (W → ℝ)) ≃ᵐ (ℝ × (W → ℝ)) :=
    MeasurableEquiv.prodCongr eHead (MeasurableEquiv.refl (W → ℝ))
  have hIdx :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm
        MeasureTheory.volume MeasureTheory.volume := by
    exact (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : V => ℝ) eIdx).symm
  have hSplit : MeasureTheory.MeasurePreserving eSplit
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Unit ⊕ W => ℝ)
  have hHead : MeasureTheory.MeasurePreserving eHead
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_preserving_funUnique Unit ℝ
  have hIdW : MeasureTheory.MeasurePreserving (id : (W → ℝ) → (W → ℝ))
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.id MeasureTheory.volume
  have hTuple : MeasureTheory.MeasurePreserving eTuple
      MeasureTheory.volume MeasureTheory.volume := by
    exact hHead.prod hIdW
  have hAll : MeasureTheory.MeasurePreserving
      (eTuple ∘ eSplit ∘
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm)
      MeasureTheory.volume MeasureTheory.volume := by
    exact hTuple.comp (hSplit.comp hIdx)
  convert hAll using 1
