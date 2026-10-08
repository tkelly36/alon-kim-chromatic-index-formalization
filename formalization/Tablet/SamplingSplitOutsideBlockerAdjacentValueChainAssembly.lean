import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerAdjacentValueChainAssembly]
theorem SamplingSplitOutsideBlockerAdjacentValueChainAssembly :
    ∀ {Ω : Type u} [Fintype Ω],
      ∀ (n : ℕ) (w : Ω → ℝ) (sourceEndpoint targetEndpoint : Ω → ℝ)
        (sourceAdjacent targetAdjacent : ℕ → Ω → ℝ),
        (∀ ω : Ω, 0 ≤ sourceEndpoint ω) →
        (∀ ω : Ω, 0 ≤ targetEndpoint ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ sourceAdjacent k ω) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, 0 ≤ targetAdjacent k ω) →
        (∀ ω : Ω, w ω = 0 → sourceEndpoint ω = 0) →
        (∀ ω : Ω, w ω = 0 → targetEndpoint ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, w ω = 0 → sourceAdjacent k ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω, w ω = 0 → targetAdjacent k ω = 0) →
        (∀ k : ℕ, k < n → ∀ ω : Ω,
          sourceAdjacent k ω ≤ targetAdjacent k ω) →
        (∀ ω : Ω, n = 0 → sourceEndpoint ω = targetEndpoint ω) →
        (∀ ω : Ω, 0 < n → sourceEndpoint ω ≤ targetAdjacent 0 ω) →
        (∀ k : ℕ, k + 1 < n → ∀ ω : Ω,
          targetAdjacent k ω ≤ sourceAdjacent (k + 1) ω) →
        (∀ ω : Ω, 0 < n → targetAdjacent (n - 1) ω ≤ targetEndpoint ω) →
        ∃ P : ℕ → Ω → ℝ,
          (∀ j : ℕ, ∀ ω : Ω, 0 ≤ P j ω) ∧
          (∀ j : ℕ, ∀ ω : Ω, w ω = 0 → P j ω = 0) ∧
          (∀ ω : Ω, P 0 ω = sourceEndpoint ω) ∧
          (∀ ω : Ω, P n ω = targetEndpoint ω) ∧
          (∀ k : ℕ, k < n → ∀ ω : Ω, P k ω ≤ P (k + 1) ω) := by
-- BODY
  intro Ω _ n w sourceEndpoint targetEndpoint sourceAdjacent targetAdjacent
    hsourceEndpoint_nonneg htargetEndpoint_nonneg hsourceAdjacent_nonneg
    htargetAdjacent_nonneg hsourceEndpoint_zero htargetEndpoint_zero
    hsourceAdjacent_zero htargetAdjacent_zero hadj hzero hfirst hinterior hlast
  let P : ℕ → Ω → ℝ :=
    fun j ω =>
      if j = 0 then sourceEndpoint ω
      else if j < n then targetAdjacent (j - 1) ω
      else targetEndpoint ω
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro j ω
    dsimp [P]
    split
    · exact hsourceEndpoint_nonneg ω
    · rename_i hj0
      split
      · rename_i hjn
        exact htargetAdjacent_nonneg (j - 1) (by omega) ω
      · exact htargetEndpoint_nonneg ω
  · intro j ω hw
    dsimp [P]
    split
    · exact hsourceEndpoint_zero ω hw
    · rename_i hj0
      split
      · rename_i hjn
        exact htargetAdjacent_zero (j - 1) (by omega) ω hw
      · exact htargetEndpoint_zero ω hw
  · intro ω
    rfl
  · intro ω
    dsimp [P]
    by_cases hn0 : n = 0
    · simp [hn0, hzero ω hn0]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      simp [hn0, Nat.lt_irrefl n]
  · intro k hk ω
    dsimp [P]
    by_cases hk0 : k = 0
    · subst k
      by_cases hn1 : n = 1
      · have hnpos : 0 < n := by omega
        have hlast0 : targetAdjacent 0 ω ≤ targetEndpoint ω := by
          simpa [hn1] using hlast ω hnpos
        simp [P, hk, hn1, le_trans (hfirst ω hnpos) hlast0]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.ne_of_gt hk)
        have h0lt : 0 + 1 < n := by
          omega
        simp [hk, Nat.ne_of_gt hk, h0lt, hfirst ω hnpos]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      by_cases hksucc : k + 1 < n
      · have hksucc_ne0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
        have hk_pred : (k + 1) - 1 = k := Nat.succ_sub_one k
        have hk_lt : k < n := hk
        simp [hk0, hk_lt, hksucc_ne0, hksucc, hk_pred]
        have hhandoff : targetAdjacent (k - 1) ω ≤ sourceAdjacent k ω := by
          simpa [Nat.sub_add_cancel hkpos] using
            hinterior (k - 1) (by simpa [Nat.sub_add_cancel hkpos] using hk) ω
        exact le_trans hhandoff (hadj k hk ω)
      · have hksucc_eq : k + 1 = n := Nat.le_antisymm (Nat.succ_le_of_lt hk)
          (Nat.le_of_not_gt hksucc)
        have hk_pred : k = n - 1 := by omega
        simp [hk0, hk, hksucc, hksucc_eq]
        calc
          targetAdjacent (k - 1) ω ≤ sourceAdjacent k ω := by
            simpa [Nat.sub_add_cancel hkpos] using
              hinterior (k - 1) (by simpa [Nat.sub_add_cancel hkpos] using hk) ω
          _ ≤ targetAdjacent k ω := hadj k hk ω
          _ ≤ targetEndpoint ω := by
            simpa [hk_pred] using hlast ω (by omega)
