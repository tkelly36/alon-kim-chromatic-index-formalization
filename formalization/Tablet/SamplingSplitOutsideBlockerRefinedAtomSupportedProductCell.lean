import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerRefinedAtomSupportedProductCell]
theorem SamplingSplitOutsideBlockerRefinedAtomSupportedProductCell :
    ∀ {σ : Type u}
      (displayedCell baseCell cell atom support : Set σ),
        baseCell = displayedCell ∩ support →
        cell = baseCell ∩ atom →
          ∃ refinedDisplayedCell : Set σ,
            refinedDisplayedCell = displayedCell ∩ atom ∧
              cell = refinedDisplayedCell ∩ support := by
-- BODY
  intro σ displayedCell baseCell cell atom support hbase hcell
  refine ⟨displayedCell ∩ atom, rfl, ?_⟩
  ext x
  simp [hcell, hbase, and_assoc, and_left_comm, and_comm]
