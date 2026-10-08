import Tablet.SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces

open BigOperators MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualCurrentAdjacentPieceMass]
theorem SamplingSplitOutsideBlockerActualCurrentAdjacentPieceMass :
    ∀ {V V' Ω : Type u} [Fintype V] [DecidableEq V]
      [Fintype V'] [DecidableEq V'] [Fintype Ω],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (ν' : @MeasureTheory.Measure (Finset V' × (V' → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
          (φ : V → V') (r : V) (X : Finset V)
          [LinearOrder {x : V // x ∈ X}]
          (β :
            (Σ x : {x : V // x ∈ X},
              {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
          (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
          (k : ℕ) (hk : k < n) (ω : Ω)
          (cell : Ω → Set (Finset V × (V → ℝ)))
          (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
          (p w : ℝ)
          (sourceCoord sourceExtensionCoord : Finset V)
          (targetCommonCoord targetExtensionCoord : Finset V')
          (baseOf : Ω → {A : Finset V // A ⊆ sourceCoord})
          (truth : Ω → Finset (Bool × {v : V // v ∈ sourceCoord})),
          Function.Injective zAt →
          Function.Injective φ →
          0 ≤ p →
          p ≤ 1 →
          (∀ i : Fin n, zAt i ∉ insert r X) →
          (∀ i : Fin n, ∀ x : V,
            x ∈ B i ↔ x ∈ X ∧ G.Adj x (zAt i)) →
          (∀ i : Fin n, zAt i ∈ sourceExtensionCoord) →
          Disjoint sourceCoord sourceExtensionCoord →
          (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) →
          targetCommonCoord = sourceCoord.image φ →
          Disjoint targetCommonCoord targetExtensionCoord →
          (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) →
          (∀ i : Fin n, ∀ x : V, ∀ hx : x ∈ X,
            ∀ hz : zAt i ∉ insert r X ∧ G.Adj x (zAt i),
              β ⟨⟨x, hx⟩, ⟨zAt i, hz⟩⟩ ∈ targetExtensionCoord) →
          (∀ η : Finset V × (V → ℝ), η ∈ cell ω →
            ∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1) →
          (∀ η' : Finset V' × (V' → ℝ), η' ∈ targetCell ω →
            ∀ v' : V', 0 ≤ η'.2 v' ∧ η'.2 v' ≤ 1) →
          (∀ ω : Ω,
            cell ω =
              ({η : Finset V × (V → ℝ) |
                η.1 ∩ sourceCoord = (baseOf ω).1 ∧
                  ∀ ℓ : Bool × {v : V // v ∈ sourceCoord},
                    ((if ℓ.1 then (0 : ℝ) < η.2 ℓ.2.1
                      else η.2 ℓ.2.1 ≤ 1) ↔ ℓ ∈ truth ω)} ∩
                {η | ∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ 1})) →
          (∀ ω : Ω,
            targetCell ω =
              ({η : Finset V' × (V' → ℝ) |
                η.1 ∩ targetCommonCoord = (baseOf ω).1.image φ ∧
                  ∀ ℓ : Bool × {v : V // v ∈ sourceCoord},
                    ((if ℓ.1 then (0 : ℝ) < η.2 (φ ℓ.2.1)
                      else η.2 (φ ℓ.2.1) ≤ 1) ↔ ℓ ∈ truth ω)} ∩
                {η | ∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ 1})) →
          (∀ A : Finset V,
            ν {η | η.1 = A} =
              ENNReal.ofReal
                (p ^ A.card *
                  (1 - p) ^ ((Finset.univ : Finset V).card - A.card))) →
          (∀ A : Finset V, ∀ t : V → ℝ,
            (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
              ν {η | η.1 = A ∧ ∀ v : V, 0 ≤ η.2 v ∧ η.2 v ≤ t v} =
                ν {η | η.1 = A} * ENNReal.ofReal (∏ v : V, t v)) →
          (∀ A : Finset V',
            ν' {η | η.1 = A} =
              ENNReal.ofReal
                (p ^ A.card *
                  (1 - p) ^ ((Finset.univ : Finset V').card - A.card))) →
          (∀ A : Finset V', ∀ t : V' → ℝ,
            (∀ v' : V', t v' ∈ Set.Icc (0 : ℝ) 1) →
              ν' {η | η.1 = A ∧ ∀ v' : V', 0 ≤ η.2 v' ∧ η.2 v' ≤ t v'} =
                ν' {η | η.1 = A} * ENNReal.ofReal (∏ v' : V', t v')) →
          (∀ candCut : {x : V // x ∈ B ⟨k, hk⟩} → ℝ,
            (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
              candCut x ∈ Set.Icc (0 : ℝ) 1) →
              ν'
                ({ξ : Finset V' × (V' → ℝ) |
                  ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                    0 ≤ ξ.2 (φ x.1) ∧ ξ.2 (φ x.1) ≤ candCut x} ∩
                  targetCell ω) =
                ν
                  ({ξ : Finset V × (V → ℝ) |
                    ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                      0 ≤ ξ.2 x.1 ∧ ξ.2 x.1 ≤ candCut x} ∩
                    cell ω)) →
          (∃ candidateLaw :
              @MeasureTheory.Measure ({x : V // x ∈ B ⟨k, hk⟩} → ℝ) ⊤,
            (∀ candCut : {x : V // x ∈ B ⟨k, hk⟩} → ℝ,
              ∀ currentCut : ℝ,
              (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                candCut x ∈ Set.Icc (0 : ℝ) 1) →
              currentCut ∈ Set.Icc (0 : ℝ) 1 →
                ν ({ξ : Finset V × (V → ℝ) |
                  (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                    0 ≤ ξ.2 x.1 ∧ ξ.2 x.1 ≤ candCut x) ∧
                  zAt ⟨k, hk⟩ ∈ ξ.1 ∧
                  0 ≤ ξ.2 (zAt ⟨k, hk⟩) ∧
                    ξ.2 (zAt ⟨k, hk⟩) ≤ currentCut} ∩ cell ω) =
                  ENNReal.ofReal w *
                    candidateLaw {π |
                      ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                        0 ≤ π x ∧ π x ≤ candCut x} *
                      ENNReal.ofReal (p * currentCut)) ∧
            (∀ candCut : {x : V // x ∈ B ⟨k, hk⟩} → ℝ,
              (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                candCut x ∈ Set.Icc (0 : ℝ) 1) →
                ν ({ξ : Finset V × (V → ℝ) |
                  (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                    0 ≤ ξ.2 x.1 ∧ ξ.2 x.1 ≤ candCut x) ∧
                  zAt ⟨k, hk⟩ ∉ ξ.1} ∩ cell ω) =
                  ENNReal.ofReal w *
                    candidateLaw {π |
                      ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                        0 ≤ π x ∧ π x ≤ candCut x} *
                      ENNReal.ofReal (1 - p)) ∧
            ∃ privateOf : {x : V // x ∈ B ⟨k, hk⟩} → V',
              (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                ∃ hxX : x.1 ∈ X,
                ∃ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                    G.Adj x.1 (zAt ⟨k, hk⟩),
                  privateOf x =
                    β ⟨⟨x.1, hxX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∧
              (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                privateOf x ∈ targetExtensionCoord) ∧
              (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                privateOf x ∉ targetCommonCoord) ∧
              (∀ x y : {x : V // x ∈ B ⟨k, hk⟩},
                privateOf x = privateOf y → x = y) ∧
              (∀ x y : {x : V // x ∈ B ⟨k, hk⟩},
                φ x.1 ≠ privateOf y) ∧
              ∀ candCut : {x : V // x ∈ B ⟨k, hk⟩} → ℝ,
                ∀ privateActive : Finset {x : V // x ∈ B ⟨k, hk⟩},
                ∀ privateCut : {x : V // x ∈ B ⟨k, hk⟩} → ℝ,
                (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                  candCut x ∈ Set.Icc (0 : ℝ) 1) →
                (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                  x ∈ privateActive → privateCut x ∈ Set.Icc (0 : ℝ) 1) →
                  ν' ({ξ : Finset V' × (V' → ℝ) |
                    (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                      0 ≤ ξ.2 (φ x.1) ∧ ξ.2 (φ x.1) ≤ candCut x) ∧
                    (∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                      privateOf x ∈ ξ.1 ↔ x ∈ privateActive) ∧
                    ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                      x ∈ privateActive →
                        0 ≤ ξ.2 (privateOf x) ∧
                          ξ.2 (privateOf x) ≤ privateCut x} ∩ targetCell ω) =
                    ENNReal.ofReal w *
                      candidateLaw {π |
                        ∀ x : {x : V // x ∈ B ⟨k, hk⟩},
                          0 ≤ π x ∧ π x ≤ candCut x} *
                      ENNReal.ofReal
                        (p ^ privateActive.card *
                          (1 - p) ^
                            ((Finset.univ :
                              Finset {x : V // x ∈ B ⟨k, hk⟩}).card -
                                privateActive.card) *
                            ∏ x ∈ privateActive, privateCut x)) →
          ∀ x : {x : V // x ∈ X}, x.1 ∈ B ⟨k, hk⟩ →
            let pieces :=
              SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
                G φ r X β n zAt B k hk
            ν (pieces.1 x ∩ cell ω) = ν' (pieces.2 x ∩ targetCell ω) := by
-- BODY
  classical
  intro V V' Ω _ _ _ _ _ G _ ν ν' φ r X _ β n zAt B k hk ω
    cell targetCell p w sourceCoord sourceExtensionCoord targetCommonCoord
    targetExtensionCoord baseOf truth hzAt_inj hφ_inj hp_nonneg hp_le_one
    hOutside hB hzAt_extension hsource_disjoint hsource_common htarget_common_eq
    htarget_disjoint htarget_common hβ_target hcell_unit htargetCell_unit
    hcell_def htargetCell_def hν_atom hν_priority hν'_atom hν'_priority
    hcandidate_transport hfactorizations x hxBk
  let pieces :=
    SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
      G φ r X β n zAt B k hk
  change ν (pieces.1 x ∩ cell ω) = ν' (pieces.2 x ∩ targetCell ω)
  have hsource_empty : pieces.1 x = (∅ : Set (Finset V × (V → ℝ))) := by
    subst pieces
    ext η
    constructor
    · intro hη
      dsimp [SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces] at hη
      rcases hη.1 with ⟨hcomplete, hnot_boundary⟩
      rcases hcomplete with ⟨hx_active, hx_priority, hx_retained⟩
      exfalso
      exact hnot_boundary
        ⟨x.1, x.2, hx_active, hx_priority,
          (by
            intro i hki hne hxiB
            exact hx_retained i hki hxiB),
          hxBk, hx_retained ⟨k, hk⟩ le_rfl hxBk⟩
    · intro hη
      cases hη
  have htarget_empty : pieces.2 x = (∅ : Set (Finset V' × (V' → ℝ))) := by
    subst pieces
    ext η'
    constructor
    · intro hη'
      dsimp [SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces] at hη'
      rcases hη'.1 with ⟨hcomplete, hnot_boundary⟩
      rcases hcomplete with ⟨hφx_active, hφx_priority, hprivate⟩
      exfalso
      exact hnot_boundary
        ⟨x.1, x.2, hφx_active, hφx_priority,
          (by
            intro i hik hne hxiB hz
            exact hprivate i hik hxiB hz),
          hxBk,
          (by
            intro hz
            exact hprivate ⟨k, hk⟩ (Nat.lt_succ_self k) hxBk hz)⟩
    · intro hη'
      cases hη'
  rw [hsource_empty, htarget_empty]
  simp
