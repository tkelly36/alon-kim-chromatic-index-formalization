import Tablet.Preamble

open BigOperators

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerStageCellCommonRefinement]
theorem SamplingSplitOutsideBlockerStageCellCommonRefinement :
    ∀ {V V' Ω₀ Λ : Type u} [Fintype Ω₀] [DecidableEq Ω₀]
      [Fintype Λ] [DecidableEq Λ],
      ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
        (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
        (baseCell : Ω₀ → Set (Finset V × (V → ℝ)))
        (targetBaseCell : Ω₀ → Set (Finset V' × (V' → ℝ)))
        (sourceLabel : Λ → Set (Finset V × (V → ℝ)))
        (targetLabel : Λ → Set (Finset V' × (V' → ℝ)))
        (transport : Ω₀ → (Finset V × (V → ℝ)) →
          (Finset V' × (V' → ℝ)) → Prop),
        (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ → Disjoint (baseCell ω₁) (baseCell ω₂)) →
        (∀ ω₁ ω₂ : Ω₀, ω₁ ≠ ω₂ →
          Disjoint (targetBaseCell ω₁) (targetBaseCell ω₂)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            (η ∈ baseCell ω₀ ↔ η' ∈ targetBaseCell ω₀)) →
        (∀ ω₀ : Ω₀, ∀ η η',
          transport ω₀ η η' →
            ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ η' ∈ targetLabel ℓ)) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ν (baseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) =
            ν' (targetBaseCell ω₀ ∩
              {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀, ∀ truth : Finset Λ,
          ∃ w : ℝ, 0 ≤ w ∧
            ENNReal.ofReal w =
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)}) ∧
            ENNReal.ofReal w =
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀,
          ν (baseCell ω₀) =
            ∑ truth : Finset Λ,
              ν (baseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth)})) →
        (∀ ω₀ : Ω₀,
          ν' (targetBaseCell ω₀) =
            ∑ truth : Finset Λ,
              ν' (targetBaseCell ω₀ ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth)})) →
        ∃ (Ω : Type u) (_ : Fintype Ω) (baseOf : Ω → Ω₀)
          (truth : Ω → Finset Λ)
          (cell : Ω → Set (Finset V × (V → ℝ)))
          (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
          (w : Ω → ℝ),
          (∀ ω : Ω,
            cell ω =
              baseCell (baseOf ω) ∩
                {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth ω)}) ∧
          (∀ ω : Ω,
            targetCell ω =
              targetBaseCell (baseOf ω) ∩
                {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth ω)}) ∧
          (∀ ω₀ : Ω₀, ∀ η : Finset V × (V → ℝ),
            η ∈ baseCell ω₀ → ∃ ω : Ω, baseOf ω = ω₀ ∧ η ∈ cell ω) ∧
          (∀ ω₀ : Ω₀, ∀ η' : Finset V' × (V' → ℝ),
            η' ∈ targetBaseCell ω₀ →
              ∃ ω : Ω, baseOf ω = ω₀ ∧ η' ∈ targetCell ω) ∧
          (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ → Disjoint (cell ω₁) (cell ω₂)) ∧
          (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ →
            Disjoint (targetCell ω₁) (targetCell ω₂)) ∧
          (∀ ω : Ω, ∀ ℓ : Λ, ∀ η : Finset V × (V → ℝ),
            η ∈ cell ω → (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth ω)) ∧
          (∀ ω : Ω, ∀ ℓ : Λ, ∀ η' : Finset V' × (V' → ℝ),
            η' ∈ targetCell ω → (η' ∈ targetLabel ℓ ↔ ℓ ∈ truth ω)) ∧
          (∀ ω : Ω, ∀ η η',
            transport (baseOf ω) η η' →
              (η ∈ cell ω ↔ η' ∈ targetCell ω)) ∧
          (∀ ω : Ω, 0 ≤ w ω) ∧
          (∀ ω : Ω, ENNReal.ofReal (w ω) = ν (cell ω)) ∧
          (∀ ω : Ω, ENNReal.ofReal (w ω) = ν' (targetCell ω)) ∧
          (∀ ω₀ : Ω₀,
            ν (baseCell ω₀) =
              ∑ ω : Ω, if baseOf ω = ω₀ then ν (cell ω) else 0) ∧
          (∀ ω₀ : Ω₀,
            ν' (targetBaseCell ω₀) =
              ∑ ω : Ω, if baseOf ω = ω₀ then ν' (targetCell ω) else 0) := by
-- BODY
  classical
  intro V V' Ω₀ Λ _ _ _ _ ν ν' baseCell targetBaseCell sourceLabel targetLabel
    transport hbaseDisjoint htargetDisjoint hbaseTransport hlabelTransport _hequalAtoms
    hatomMass hsourceSplit htargetSplit
  let Ω : Type u := Ω₀ × Finset Λ
  let baseOf : Ω → Ω₀ := fun ω => ω.1
  let truth : Ω → Finset Λ := fun ω => ω.2
  let cell : Ω → Set (Finset V × (V → ℝ)) := fun ω =>
    baseCell (baseOf ω) ∩
      {η | ∀ ℓ : Λ, (η ∈ sourceLabel ℓ ↔ ℓ ∈ truth ω)}
  let targetCell : Ω → Set (Finset V' × (V' → ℝ)) := fun ω =>
    targetBaseCell (baseOf ω) ∩
      {η | ∀ ℓ : Λ, (η ∈ targetLabel ℓ ↔ ℓ ∈ truth ω)}
  choose w hw_nonneg hw_source hw_target using hatomMass
  refine ⟨Ω, inferInstance, baseOf, truth, cell, targetCell,
    (fun ω : Ω => w (baseOf ω) (truth ω)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    rfl
  · intro ω
    rfl
  · intro ω₀ η hη
    let τ : Finset Λ := (Finset.univ : Finset Λ).filter fun ℓ => η ∈ sourceLabel ℓ
    refine ⟨(ω₀, τ), rfl, ?_⟩
    exact ⟨hη, by intro ℓ; change η ∈ sourceLabel ℓ ↔ ℓ ∈ τ; simp [τ]⟩
  · intro ω₀ η' hη'
    let τ : Finset Λ := (Finset.univ : Finset Λ).filter fun ℓ => η' ∈ targetLabel ℓ
    refine ⟨(ω₀, τ), rfl, ?_⟩
    exact ⟨hη', by intro ℓ; change η' ∈ targetLabel ℓ ↔ ℓ ∈ τ; simp [τ]⟩
  · rintro ⟨ω₁, τ₁⟩ ⟨ω₂, τ₂⟩ hpair
    by_cases hω : ω₁ = ω₂
    · subst ω₂
      have hτ : τ₁ ≠ τ₂ := by
        intro h
        exact hpair (Prod.ext rfl h)
      have hnot : ¬ ∀ ℓ : Λ, (ℓ ∈ τ₁ ↔ ℓ ∈ τ₂) := by
        intro h
        exact hτ (Finset.ext h)
      push Not at hnot
      obtain ⟨ℓ, hℓ⟩ := hnot
      rw [Set.disjoint_left]
      intro η hη₁ hη₂
      have h₁ : η ∈ sourceLabel ℓ ↔ ℓ ∈ τ₁ := hη₁.2 ℓ
      have h₂ : η ∈ sourceLabel ℓ ↔ ℓ ∈ τ₂ := hη₂.2 ℓ
      have hequiv : ℓ ∈ τ₁ ↔ ℓ ∈ τ₂ := h₁.symm.trans h₂
      rcases hℓ with ⟨hmem, hnot⟩ | ⟨hnot, hmem⟩
      · exact hnot (hequiv.1 hmem)
      · exact hnot (hequiv.2 hmem)
    · exact (hbaseDisjoint ω₁ ω₂ hω).mono
        (by intro η hη; exact hη.1) (by intro η hη; exact hη.1)
  · rintro ⟨ω₁, τ₁⟩ ⟨ω₂, τ₂⟩ hpair
    by_cases hω : ω₁ = ω₂
    · subst ω₂
      have hτ : τ₁ ≠ τ₂ := by
        intro h
        exact hpair (Prod.ext rfl h)
      have hnot : ¬ ∀ ℓ : Λ, (ℓ ∈ τ₁ ↔ ℓ ∈ τ₂) := by
        intro h
        exact hτ (Finset.ext h)
      push Not at hnot
      obtain ⟨ℓ, hℓ⟩ := hnot
      rw [Set.disjoint_left]
      intro η' hη₁ hη₂
      have h₁ : η' ∈ targetLabel ℓ ↔ ℓ ∈ τ₁ := hη₁.2 ℓ
      have h₂ : η' ∈ targetLabel ℓ ↔ ℓ ∈ τ₂ := hη₂.2 ℓ
      have hequiv : ℓ ∈ τ₁ ↔ ℓ ∈ τ₂ := h₁.symm.trans h₂
      rcases hℓ with ⟨hmem, hnot⟩ | ⟨hnot, hmem⟩
      · exact hnot (hequiv.1 hmem)
      · exact hnot (hequiv.2 hmem)
    · exact (htargetDisjoint ω₁ ω₂ hω).mono
        (by intro η' hη'; exact hη'.1) (by intro η' hη'; exact hη'.1)
  · intro ω ℓ η hη
    exact hη.2 ℓ
  · intro ω ℓ η' hη'
    exact hη'.2 ℓ
  · rintro ⟨ω₀, τ⟩ η η' htransport
    constructor
    · intro hη
      exact ⟨(hbaseTransport ω₀ η η' htransport).1 hη.1,
        by intro ℓ; exact ((hlabelTransport ω₀ η η' htransport ℓ).symm.trans (hη.2 ℓ))⟩
    · intro hη'
      exact ⟨(hbaseTransport ω₀ η η' htransport).2 hη'.1,
        by intro ℓ; exact ((hlabelTransport ω₀ η η' htransport ℓ).trans (hη'.2 ℓ))⟩
  · rintro ⟨ω₀, τ⟩
    exact hw_nonneg ω₀ τ
  · rintro ⟨ω₀, τ⟩
    exact hw_source ω₀ τ
  · rintro ⟨ω₀, τ⟩
    exact hw_target ω₀ τ
  · intro ω₀
    rw [hsourceSplit ω₀]
    rw [Fintype.sum_prod_type]
    simp [Ω, baseOf, truth, cell]
  · intro ω₀
    rw [htargetSplit ω₀]
    rw [Fintype.sum_prod_type]
    simp [Ω, baseOf, truth, targetCell]
