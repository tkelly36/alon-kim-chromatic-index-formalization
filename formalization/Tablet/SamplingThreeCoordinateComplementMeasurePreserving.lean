import Tablet.RandomIndependentSetSampling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi

open BigOperators

-- [TABLET NODE: SamplingThreeCoordinateComplementMeasurePreserving]
theorem SamplingThreeCoordinateComplementMeasurePreserving
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    MeasureTheory.MeasurePreserving
      (fun q : V → ℝ =>
        (q a, q b, q c,
          fun v : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} => q v.1))
      MeasureTheory.volume
      MeasureTheory.volume := by
-- BODY
  let W := {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}
  let eIdx : (Fin 3 ⊕ W) ≃ V :=
    { toFun := fun i =>
        match i with
        | Sum.inl j => ![a, b, c] j
        | Sum.inr v => v.1
      invFun := fun v =>
        if ha : v = a then Sum.inl 0
        else if hb : v = b then Sum.inl 1
        else if hc : v = c then Sum.inl 2
        else Sum.inr ⟨v, ha, hb, hc⟩
      left_inv := by
        intro i
        cases i with
        | inl j =>
            fin_cases j <;> simp [Ne.symm hab, Ne.symm hac, Ne.symm hbc]
        | inr v =>
            rcases v with ⟨v, hva, hvb, hvc⟩
            simp [hva, hvb, hvc]
      right_inv := by
        intro v
        by_cases ha : v = a
        · simp [ha]
        · by_cases hb : v = b
          · simp [hb, Ne.symm hab]
          · by_cases hc : v = c
            · simp [hc, Ne.symm hac, Ne.symm hbc]
            · simp [ha, hb, hc] }
  let eSplit : ((Fin 3 ⊕ W) → ℝ) ≃ᵐ ((Fin 3 → ℝ) × (W → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ W => ℝ)
  let eHead : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let eTail : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) :=
    MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  let eTuple : ((Fin 3 → ℝ) × (W → ℝ)) ≃ᵐ (ℝ × ℝ × ℝ × (W → ℝ)) :=
    (MeasurableEquiv.prodCongr eHead
      (MeasurableEquiv.refl (W → ℝ))).trans
      (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.prodCongr eTail
            (MeasurableEquiv.refl (W → ℝ)))).trans
          (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
            MeasurableEquiv.prodAssoc)))
  have hIdx :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm
        MeasureTheory.volume MeasureTheory.volume := by
    exact (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : V => ℝ) eIdx).symm
  have hSplit : MeasureTheory.MeasurePreserving eSplit
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin 3 ⊕ W => ℝ)
  have hHead : MeasureTheory.MeasurePreserving eHead
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hTail : MeasureTheory.MeasurePreserving eTail
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  have hIdW : MeasureTheory.MeasurePreserving (id : (W → ℝ) → (W → ℝ))
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.id MeasureTheory.volume
  have hIdR : MeasureTheory.MeasurePreserving (id : ℝ → ℝ)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.id MeasureTheory.volume
  have hA : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodCongr eHead
        (MeasurableEquiv.refl (W → ℝ)))
      MeasureTheory.volume MeasureTheory.volume := by
    exact hHead.prod hIdW
  have hB : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((ℝ × (Fin 2 → ℝ)) × (W → ℝ)) ≃ᵐ ℝ × (Fin 2 → ℝ) × (W → ℝ))
      MeasureTheory.volume MeasureTheory.volume := by
    exact MeasureTheory.measurePreserving_prodAssoc
      MeasureTheory.volume MeasureTheory.volume MeasureTheory.volume
  have hC : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.prodCongr eTail
          (MeasurableEquiv.refl (W → ℝ))))
      MeasureTheory.volume MeasureTheory.volume := by
    exact hIdR.prod (hTail.prod hIdW)
  have hD : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.prodAssoc :
          ((ℝ × ℝ) × (W → ℝ)) ≃ᵐ ℝ × ℝ × (W → ℝ)))
      MeasureTheory.volume MeasureTheory.volume := by
    exact hIdR.prod (MeasureTheory.measurePreserving_prodAssoc
      MeasureTheory.volume MeasureTheory.volume MeasureTheory.volume)
  have hTuple : MeasureTheory.MeasurePreserving eTuple
      MeasureTheory.volume MeasureTheory.volume := by
    exact hD.comp (hC.comp (hB.comp hA))
  have hAll : MeasureTheory.MeasurePreserving
      (eTuple ∘ eSplit ∘
        (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) eIdx).symm)
      MeasureTheory.volume MeasureTheory.volume := by
    exact hTuple.comp (hSplit.comp hIdx)
  convert hAll using 1
