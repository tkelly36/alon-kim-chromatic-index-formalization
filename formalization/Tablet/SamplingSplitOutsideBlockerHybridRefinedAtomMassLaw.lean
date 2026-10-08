import Tablet.SamplingSplitOutsideBlockerBooleanAtomMassSupplier
import Tablet.SamplingSplitOutsideBlockerStageCellCommonRefinement

open BigOperators MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerHybridRefinedAtomMassLaw]
theorem SamplingSplitOutsideBlockerHybridRefinedAtomMassLaw :
    ∀ {V V' Ω₀ Λ : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Λ] [DecidableEq Λ]
      [MeasurableSpace (Finset V × (V → ℝ))]
      [MeasurableSpace (Finset V' × (V' → ℝ))],
      ∀ (ν : MeasureTheory.Measure (Finset V × (V → ℝ)))
        (ν' : MeasureTheory.Measure (Finset V' × (V' → ℝ)))
        (baseCell : Ω₀ → Set (Finset V × (V → ℝ)))
        (targetBaseCell : Ω₀ → Set (Finset V' × (V' → ℝ)))
        (sourceLabel : Λ → Set (Finset V × (V → ℝ)))
        (targetLabel : Λ → Set (Finset V' × (V' → ℝ)))
        (transport : Ω₀ → (Finset V × (V → ℝ)) →
          (Finset V' × (V' → ℝ)) → Prop),
        (∀ ω₀ : Ω₀, MeasurableSet (baseCell ω₀)) →
        (∀ ω₀ : Ω₀, MeasurableSet (targetBaseCell ω₀)) →
        (∀ ℓ : Λ, MeasurableSet (sourceLabel ℓ)) →
        (∀ ℓ : Λ, MeasurableSet (targetLabel ℓ)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            (η ∈ baseCell ω₀ ↔ η' ∈ targetBaseCell ω₀)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ η' ∈ targetLabel ℓ)) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          -- This is the exact mass certificate obtained by applying the
          -- paired-cell and Boolean-to-product subcell refinements to the
          -- displayed source and target subcells for this truth vector.
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          MeasurableSet (baseCell ω₀ ∩
            {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          MeasurableSet (targetBaseCell ω₀ ∩
            {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀,
          baseCell ω₀ =
            ⋃ truth : Finset Λ,
              baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
        (∀ ω₀ : Ω₀,
          targetBaseCell ω₀ =
            ⋃ truth : Finset Λ,
              targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)}) ∧
        (∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
          Disjoint
            (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₁)})
            (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₂)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
          Disjoint
            (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth₁)})
            (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth₂)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ, ∀ η η',
          transport ω₀ η η' →
            (η ∈ baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)} ↔
              η' ∈ targetBaseCell ω₀ ∩
                {η' | ∀ ℓ : Λ, (η' ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀,
          ν (baseCell ω₀) =
            ∑ truth : Finset Λ,
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀,
          ν' (targetBaseCell ω₀) =
            ∑ truth : Finset Λ,
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ν (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) =
            ν' (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) ∧
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) := by
-- BODY
  classical
  intro V V' Ω₀ Λ _ _ _ _ _ _ _ _ ν ν' baseCell targetBaseCell
    sourceLabel targetLabel transport hbaseMeas htargetBaseMeas hsourceLabelMeas
    htargetLabelMeas hbaseTransport hlabelTransport hatomMass
  let sourceAtom : Ω₀ → Finset Λ → Set (Finset V × (V → ℝ)) := fun ω₀ truth =>
    baseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}
  let targetAtom : Ω₀ → Finset Λ → Set (Finset V' × (V' → ℝ)) := fun ω₀ truth =>
    targetBaseCell ω₀ ∩ {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)}
  have hsourceTruthMeas :
      ∀ truth : Finset Λ,
        MeasurableSet
          ({η : Finset V × (V → ℝ) |
            ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) := by
    intro truth
    have hset :
        ({η : Finset V × (V → ℝ) |
          ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) =
          ⋂ ℓ : Λ, (if ℓ ∈ truth then sourceLabel ℓ else (sourceLabel ℓ)ᶜ) := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h ℓ
        by_cases hℓ : ℓ ∈ truth
        · simpa [hℓ] using (h ℓ).2 hℓ
        · simpa [hℓ] using fun hmem => hℓ ((h ℓ).1 hmem)
      · intro h ℓ
        constructor
        · intro hmem
          by_contra hnot
          have hcompl := h ℓ
          simpa [hnot, hmem] using hcompl
        · intro hmem
          have hset := h ℓ
          simpa [hmem] using hset
    rw [hset]
    exact MeasurableSet.iInter fun ℓ =>
      by by_cases hℓ : ℓ ∈ truth <;> simp [hℓ, hsourceLabelMeas ℓ]
  have htargetTruthMeas :
      ∀ truth : Finset Λ,
        MeasurableSet
          ({η : Finset V' × (V' → ℝ) |
            ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)}) := by
    intro truth
    have hset :
        ({η : Finset V' × (V' → ℝ) |
          ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)}) =
          ⋂ ℓ : Λ, (if ℓ ∈ truth then targetLabel ℓ else (targetLabel ℓ)ᶜ) := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h ℓ
        by_cases hℓ : ℓ ∈ truth
        · simpa [hℓ] using (h ℓ).2 hℓ
        · simpa [hℓ] using fun hmem => hℓ ((h ℓ).1 hmem)
      · intro h ℓ
        constructor
        · intro hmem
          by_contra hnot
          have hcompl := h ℓ
          simpa [hnot, hmem] using hcompl
        · intro hmem
          have hset := h ℓ
          simpa [hmem] using hset
    rw [hset]
    exact MeasurableSet.iInter fun ℓ =>
      by by_cases hℓ : ℓ ∈ truth <;> simp [hℓ, htargetLabelMeas ℓ]
  have hsourceAtomMeas : ∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
      MeasurableSet (sourceAtom ω₀ truth) := by
    intro ω₀ truth
    exact (hbaseMeas ω₀).inter (hsourceTruthMeas truth)
  have htargetAtomMeas : ∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
      MeasurableSet (targetAtom ω₀ truth) := by
    intro ω₀ truth
    exact (htargetBaseMeas ω₀).inter (htargetTruthMeas truth)
  have hsourceCoverMem : ∀ ω₀ : Ω₀, ∀ η : Finset V × (V → ℝ),
      η ∈ baseCell ω₀ ↔ ∃ truth : Finset Λ, η ∈ sourceAtom ω₀ truth := by
    intro ω₀ η
    constructor
    · intro hη
      let truth : Finset Λ := (Finset.univ : Finset Λ).filter fun ℓ => η ∈ sourceLabel ℓ
      refine ⟨truth, ⟨hη, ?_⟩⟩
      intro ℓ
      simp [truth]
    · rintro ⟨truth, hη⟩
      exact hη.1
  have htargetCoverMem : ∀ ω₀ : Ω₀, ∀ η' : Finset V' × (V' → ℝ),
      η' ∈ targetBaseCell ω₀ ↔ ∃ truth : Finset Λ, η' ∈ targetAtom ω₀ truth := by
    intro ω₀ η'
    constructor
    · intro hη
      let truth : Finset Λ := (Finset.univ : Finset Λ).filter fun ℓ => η' ∈ targetLabel ℓ
      refine ⟨truth, ⟨hη, ?_⟩⟩
      intro ℓ
      simp [truth]
    · rintro ⟨truth, hη⟩
      exact hη.1
  have hsourceCoverSet : ∀ ω₀ : Ω₀,
      baseCell ω₀ = ⋃ truth : Finset Λ, sourceAtom ω₀ truth := by
    intro ω₀
    ext η
    simpa [Set.mem_iUnion] using hsourceCoverMem ω₀ η
  have htargetCoverSet : ∀ ω₀ : Ω₀,
      targetBaseCell ω₀ = ⋃ truth : Finset Λ, targetAtom ω₀ truth := by
    intro ω₀
    ext η'
    simpa [Set.mem_iUnion] using htargetCoverMem ω₀ η'
  have hsourceDisjoint : ∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
      Disjoint (sourceAtom ω₀ truth₁) (sourceAtom ω₀ truth₂) := by
    intro ω₀ truth₁ truth₂ hneq
    rw [Set.disjoint_left]
    intro η hη₁ hη₂
    have hnot : ¬ ∀ ℓ : Λ, (ℓ ∈ truth₁ ↔ ℓ ∈ truth₂) := by
      intro h
      exact hneq (Finset.ext h)
    push_neg at hnot
    rcases hnot with ⟨ℓ, hℓ⟩
    have h₁ : η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₁ := hη₁.2 ℓ
    have h₂ : η ∈ sourceLabel ℓ ↔ ℓ ∈ truth₂ := hη₂.2 ℓ
    have hequiv : ℓ ∈ truth₁ ↔ ℓ ∈ truth₂ := h₁.symm.trans h₂
    rcases hℓ with ⟨hmem, hnotmem⟩ | ⟨hnotmem, hmem⟩
    · exact hnotmem (hequiv.1 hmem)
    · exact hnotmem (hequiv.2 hmem)
  have htargetDisjoint : ∀ ω₀ : Ω₀, ∀ truth₁ truth₂ : Finset Λ, truth₁ ≠ truth₂ →
      Disjoint (targetAtom ω₀ truth₁) (targetAtom ω₀ truth₂) := by
    intro ω₀ truth₁ truth₂ hneq
    rw [Set.disjoint_left]
    intro η hη₁ hη₂
    have hnot : ¬ ∀ ℓ : Λ, (ℓ ∈ truth₁ ↔ ℓ ∈ truth₂) := by
      intro h
      exact hneq (Finset.ext h)
    push_neg at hnot
    rcases hnot with ⟨ℓ, hℓ⟩
    have h₁ : η ∈ targetLabel ℓ ↔ ℓ ∈ truth₁ := hη₁.2 ℓ
    have h₂ : η ∈ targetLabel ℓ ↔ ℓ ∈ truth₂ := hη₂.2 ℓ
    have hequiv : ℓ ∈ truth₁ ↔ ℓ ∈ truth₂ := h₁.symm.trans h₂
    rcases hℓ with ⟨hmem, hnotmem⟩ | ⟨hnotmem, hmem⟩
    · exact hnotmem (hequiv.1 hmem)
    · exact hnotmem (hequiv.2 hmem)
  have hatomTransport : ∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
      ∀ η η', transport ω₀ η η' →
        (η ∈ sourceAtom ω₀ truth ↔ η' ∈ targetAtom ω₀ truth) := by
    intro ω₀ truth η η' htransport
    constructor
    · intro hη
      exact ⟨(hbaseTransport ω₀ η η' htransport).1 hη.1,
        by intro ℓ; exact ((hlabelTransport ω₀ η η' htransport ℓ).symm.trans (hη.2 ℓ))⟩
    · intro hη'
      exact ⟨(hbaseTransport ω₀ η η' htransport).2 hη'.1,
        by intro ℓ; exact ((hlabelTransport ω₀ η η' htransport ℓ).trans (hη'.2 ℓ))⟩
  have hmassPack :=
    SamplingSplitOutsideBlockerBooleanAtomMassSupplier
      (ν := ν) (ν' := ν') (baseCell := baseCell) (targetBaseCell := targetBaseCell)
      (sourceLabel := sourceLabel) (targetLabel := targetLabel)
      (by simpa [sourceAtom] using hsourceAtomMeas)
      (by simpa [targetAtom] using htargetAtomMeas)
      (by simpa [sourceAtom] using hsourceCoverMem)
      (by simpa [targetAtom] using htargetCoverMem)
      (by simpa [sourceAtom] using hsourceDisjoint)
      (by simpa [targetAtom] using htargetDisjoint)
      (by
        intro ω₀ truth
        obtain ⟨w, hw_nonneg, hw_source, hw_target⟩ := hatomMass ω₀ truth
        exact hw_source.symm.trans hw_target)
      hatomMass
  refine ⟨?_, ?_, hsourceCoverSet, htargetCoverSet, ?_, ?_, hatomTransport,
    hmassPack.1, hmassPack.2.1, hmassPack.2.2.1, hmassPack.2.2.2⟩
  · simpa [sourceAtom] using hsourceAtomMeas
  · simpa [targetAtom] using htargetAtomMeas
  · simpa [sourceAtom] using hsourceDisjoint
  · simpa [targetAtom] using htargetDisjoint
