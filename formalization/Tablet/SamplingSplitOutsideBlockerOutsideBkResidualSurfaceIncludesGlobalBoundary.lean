import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerOutsideBkResidualSurfaceIncludesGlobalBoundary]
theorem SamplingSplitOutsideBlockerOutsideBkResidualSurfaceIncludesGlobalBoundary :
    ∀ {α : Type u} {S T : Type u} [LT α]
      (sourceComplete : α → Set S) (targetComplete : α → Set T)
      (sourceBoundary : Set S) (targetBoundary : Set T) (x : α),
      let sourceResidual : α → Set S := fun y => sourceComplete y \ sourceBoundary
      let targetResidual : α → Set T := fun y => targetComplete y \ targetBoundary
      let sourcePiece : α → Set S :=
        fun y => {s | s ∈ sourceResidual y ∧ ∀ z : α, z < y → s ∉ sourceResidual z}
      let targetPiece : α → Set T :=
        fun y => {t | t ∈ targetResidual y ∧ ∀ z : α, z < y → t ∉ targetResidual z}
      sourcePiece x =
          {s | s ∈ sourceComplete x ∧ s ∉ sourceBoundary ∧
            ∀ z : α, z < x → ¬ (s ∈ sourceComplete z ∧ s ∉ sourceBoundary)} ∧
        targetPiece x =
          {t | t ∈ targetComplete x ∧ t ∉ targetBoundary ∧
            ∀ z : α, z < x → ¬ (t ∈ targetComplete z ∧ t ∉ targetBoundary)} := by
-- BODY
  intro α S T _ sourceComplete targetComplete sourceBoundary targetBoundary x
  constructor
  · ext s
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, fun z hzx hz => h.2 z hzx hz⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, fun z hzx hz => h.2.2 z hzx hz⟩
  · ext t
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, fun z hzx hz => h.2 z hzx hz⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, fun z hzx hz => h.2.2 z hzx hz⟩
