import Tablet.Preamble

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerMixedStageCompleteDecomposition]
theorem SamplingSplitOutsideBlockerMixedStageCompleteDecomposition :
    ∀ {Ω Source : Type u} [Fintype Ω] [MeasurableSpace Source],
      ∀ (n : ℕ) (w : Ω → ℝ) (ν : MeasureTheory.Measure Source)
        (cell : Ω → Set Source)
        (complete unchanged boundary : ℕ → Ω → Set Source)
        (stageMass unchangedMass boundaryMass : ℕ → Ω → ℝ),
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ w ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ stageMass k ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ unchangedMass k ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ boundaryMass k ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          w ω = 0 → stageMass k ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          w ω = 0 → unchangedMass k ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          w ω = 0 → boundaryMass k ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          complete k ω ∩ cell ω =
            (unchanged k ω ∩ cell ω) ∪ (boundary k ω ∩ cell ω)) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          Disjoint (unchanged k ω ∩ cell ω) (boundary k ω ∩ cell ω)) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          ν (complete k ω ∩ cell ω) =
            ν (unchanged k ω ∩ cell ω) + ν (boundary k ω ∩ cell ω)) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          ENNReal.ofReal (w ω * stageMass k ω) =
            ν (complete k ω ∩ cell ω)) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          ENNReal.ofReal (w ω * unchangedMass k ω) =
            ν (unchanged k ω ∩ cell ω)) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          ENNReal.ofReal (w ω * boundaryMass k ω) =
            ν (boundary k ω ∩ cell ω)) →
        ∀ k : ℕ, k < n → ∀ ω : Ω,
          stageMass k ω = unchangedMass k ω + boundaryMass k ω := by
-- BODY
  intro Ω Source _ _ n w ν cell complete unchanged boundary stageMass
    unchangedMass boundaryMass hw_nonneg hstage_nonneg hunchanged_nonneg
    hboundary_nonneg hstage_zero hunchanged_zero hboundary_zero _hcover
    _hdisjoint hfinite_add hcomplete hunchanged hboundary k hk ω
  by_cases hwz : w ω = 0
  · rw [hstage_zero k hk ω hwz, hunchanged_zero k hk ω hwz,
      hboundary_zero k hk ω hwz]
    ring
  · have hwpos : 0 < w ω := lt_of_le_of_ne (hw_nonneg k hk ω) (Ne.symm hwz)
    have hstage_prod_nonneg : 0 ≤ w ω * stageMass k ω :=
      mul_nonneg (hw_nonneg k hk ω) (hstage_nonneg k hk ω)
    have hunchanged_prod_nonneg : 0 ≤ w ω * unchangedMass k ω :=
      mul_nonneg (hw_nonneg k hk ω) (hunchanged_nonneg k hk ω)
    have hboundary_prod_nonneg : 0 ≤ w ω * boundaryMass k ω :=
      mul_nonneg (hw_nonneg k hk ω) (hboundary_nonneg k hk ω)
    have hmass :
        ENNReal.ofReal (w ω * stageMass k ω) =
          ENNReal.ofReal (w ω * unchangedMass k ω) +
            ENNReal.ofReal (w ω * boundaryMass k ω) := by
      rw [hcomplete k hk ω, hfinite_add k hk ω, ← hunchanged k hk ω,
        ← hboundary k hk ω]
    have hreal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_ofReal hstage_prod_nonneg,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hunchanged_prod_nonneg,
      ENNReal.toReal_ofReal hboundary_prod_nonneg] at hreal
    have hmul :
        w ω * stageMass k ω =
          w ω * (unchangedMass k ω + boundaryMass k ω) := by
      linarith
    exact mul_left_cancel₀ (ne_of_gt hwpos) hmul
