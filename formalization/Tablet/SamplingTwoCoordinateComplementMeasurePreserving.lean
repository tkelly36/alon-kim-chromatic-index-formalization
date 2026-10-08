import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi

open BigOperators

-- [TABLET NODE: SamplingTwoCoordinateComplementMeasurePreserving]
theorem SamplingTwoCoordinateComplementMeasurePreserving
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (huv : u ≠ v) :
    MeasureTheory.MeasurePreserving
      (fun q : V → ℝ =>
        (q u, q v, fun w : {w : V // w ≠ u ∧ w ≠ v} => q w.1))
      MeasureTheory.volume
      MeasureTheory.volume := by
-- BODY
  let W := {w : V // w ≠ u ∧ w ≠ v}
  let eIdx : (Fin 2 ⊕ W) ≃ V :=
    { toFun := fun i =>
        match i with
        | Sum.inl j => ![u, v] j
        | Sum.inr w => w.1
      invFun := fun x =>
        if hu : x = u then Sum.inl 0
        else if hv : x = v then Sum.inl 1
        else Sum.inr ⟨x, hu, hv⟩
      left_inv := by
        intro i
        cases i with
        | inl j =>
            fin_cases j <;> simp [Ne.symm huv]
        | inr w =>
            rcases w with ⟨w, hwu, hwv⟩
            simp [hwu, hwv]
      right_inv := by
        intro x
        by_cases hu : x = u
        · simp [hu]
        · by_cases hv : x = v
          · simp [hv, Ne.symm huv]
          · simp [hu, hv] }
  let eSplit : ((Fin 2 ⊕ W) → ℝ) ≃ᵐ ((Fin 2 → ℝ) × (W → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ W => ℝ)
  let eHead : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  let eTuple : ((Fin 2 → ℝ) × (W → ℝ)) ≃ᵐ (ℝ × ℝ × (W → ℝ)) :=
    (MeasurableEquiv.prodCongr eHead (MeasurableEquiv.refl (W → ℝ))).trans
      MeasurableEquiv.prodAssoc
  have hIdx :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm
        MeasureTheory.volume MeasureTheory.volume := by
    exact (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : V => ℝ) eIdx).symm
  have hSplit : MeasureTheory.MeasurePreserving eSplit
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin 2 ⊕ W => ℝ)
  have hHead : MeasureTheory.MeasurePreserving eHead
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  have hIdW : MeasureTheory.MeasurePreserving (id : (W → ℝ) → (W → ℝ))
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.id MeasureTheory.volume
  have hA : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodCongr eHead (MeasurableEquiv.refl (W → ℝ)))
      MeasureTheory.volume MeasureTheory.volume := by
    exact hHead.prod hIdW
  have hB : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × (W → ℝ)) ≃ᵐ ℝ × ℝ × (W → ℝ))
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.measurePreserving_prodAssoc
      MeasureTheory.volume MeasureTheory.volume MeasureTheory.volume
  have hTuple : MeasureTheory.MeasurePreserving eTuple
      MeasureTheory.volume MeasureTheory.volume := by
    exact hB.comp hA
  have hAll : MeasureTheory.MeasurePreserving
      (eTuple ∘ eSplit ∘
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm)
      MeasureTheory.volume MeasureTheory.volume := by
    exact hTuple.comp (hSplit.comp hIdx)
  convert hAll using 1

