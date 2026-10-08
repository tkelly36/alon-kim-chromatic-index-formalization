import Tablet.SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces

open BigOperators MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerOutsideBkResidualLabelStructure]
structure SamplingSplitOutsideBlockerOutsideBkResidualLabelStructure
    {V V' Ω ι label : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    [LinearOrder {x : V // x ∈ X}]
    (β :
      (Σ x : {x : V // x ∈ X},
        {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (k : ℕ) (hk : k < n) (ω : Ω)
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ)))
    (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
    (x : {x : V // x ∈ X})
    (sourceAtom : ι → Set (Finset V × (V → ℝ)))
    (targetAtom : ι → Set (Finset V' × (V' → ℝ)))
    (sourceLabelEvent : label → Set (Finset V × (V → ℝ)))
    (targetLabelEvent : label → Set (Finset V' × (V' → ℝ)))
    (labelTruth : ι → label → Bool)
    (selectedWitnessLabels : Finset label)
    (earlierFirstWitnessLabels : Finset label)
    (cellPredicateLabels : Finset label)
    (retainedCommonSourceTestLabels : Finset label)
    (alreadyPrivateTargetTestLabels : Finset label)
    (globalBoundaryComplementLabels : Finset label) : Prop where
-- BODY
  label_finite : Nonempty (Fintype label)
  source_atom_normal_form :
    ∀ a : ι,
      sourceAtom a =
        {η | ∀ ℓ : label,
          (η ∈ sourceLabelEvent ℓ ↔ labelTruth a ℓ = true)}
  target_atom_normal_form :
    ∀ a : ι,
      targetAtom a =
        {η' | ∀ ℓ : label,
          (η' ∈ targetLabelEvent ℓ ↔ labelTruth a ℓ = true)}
  label_exhausts_residual_surface :
    ∀ ℓ : label,
      ℓ ∈ selectedWitnessLabels ∨
        ℓ ∈ earlierFirstWitnessLabels ∨
        ℓ ∈ cellPredicateLabels ∨
        ℓ ∈ retainedCommonSourceTestLabels ∨
        ℓ ∈ alreadyPrivateTargetTestLabels ∨
        ℓ ∈ globalBoundaryComplementLabels
  selected_activation_label_exists :
    ∃ ℓ ∈ selectedWitnessLabels,
      sourceLabelEvent ℓ =
        {η : Finset V × (V → ℝ) | x.1 ∈ η.1} ∧
      targetLabelEvent ℓ =
        {η' : Finset V' × (V' → ℝ) | φ x.1 ∈ η'.1}
  selected_embedded_priority_labels_exist :
    ∀ y : V, ∀ hy : y ∈ insert r X, ∀ hxy : G.Adj x.1 y,
      ∃ ℓ ∈ selectedWitnessLabels,
        sourceLabelEvent ℓ =
          {η : Finset V × (V → ℝ) |
            y ∈ η.1 → η.2 y < η.2 x.1} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) |
            φ y ∈ η'.1 → η'.2 (φ y) < η'.2 (φ x.1)}
  selected_retained_source_blocker_labels_exist :
    ∀ i : Fin n, ∀ hki : (k : ℕ) ≤ i, ∀ hxi : x.1 ∈ B i,
      ∃ ℓ ∈ selectedWitnessLabels,
        sourceLabelEvent ℓ =
          {η : Finset V × (V → ℝ) |
            ¬ (zAt i ∈ η.1 ∧
              η.2 x.1 < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) |
            ∀ hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i),
              ¬ (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                η'.2 (φ x.1) <
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∧
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∈
                    Set.Icc (0 : ℝ) 1)}
  selected_labels_are_selected_witness_clauses :
    ∀ ℓ : label, ℓ ∈ selectedWitnessLabels →
      (sourceLabelEvent ℓ =
          {η : Finset V × (V → ℝ) |
            x.1 ∈ η.1 ∧
              (∀ y : V, y ∈ insert r X → y ∈ η.1 →
                G.Adj x.1 y → η.2 y < η.2 x.1) ∧
              ∀ i : Fin n, (k : ℕ) ≤ i → x.1 ∈ B i →
                ¬ (zAt i ∈ η.1 ∧
                  η.2 x.1 < η.2 (zAt i) ∧
                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) |
            φ x.1 ∈ η'.1 ∧
              (∀ y : V, y ∈ insert r X → φ y ∈ η'.1 →
                G.Adj x.1 y → η'.2 (φ y) < η'.2 (φ x.1)) ∧
              ∀ i : Fin n, (i : ℕ) < k + 1 → x.1 ∈ B i →
                ∀ hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i),
                  ¬ (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                    η'.2 (φ x.1) <
                      η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∧
                      η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∈
                        Set.Icc (0 : ℝ) 1)}) ∨
      sourceLabelEvent ℓ =
        {η : Finset V × (V → ℝ) | x.1 ∈ η.1} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) | φ x.1 ∈ η'.1} ∨
      (∃ y : V, ∃ _hy : y ∈ insert r X, ∃ _hxy : G.Adj x.1 y,
        sourceLabelEvent ℓ =
          {η : Finset V × (V → ℝ) |
            y ∈ η.1 → η.2 y < η.2 x.1} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) |
            φ y ∈ η'.1 → η'.2 (φ y) < η'.2 (φ x.1)}) ∨
      (∃ i : Fin n, ∃ _hki : (k : ℕ) ≤ i, ∃ _hxi : x.1 ∈ B i,
        sourceLabelEvent ℓ =
          {η : Finset V × (V → ℝ) |
            ¬ (zAt i ∈ η.1 ∧
              η.2 x.1 < η.2 (zAt i) ∧
                η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
        targetLabelEvent ℓ =
          {η' : Finset V' × (V' → ℝ) |
            ∀ hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i),
              ¬ (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                η'.2 (φ x.1) <
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∧
                  η'.2 (β ⟨⟨x.1, x.2⟩, ⟨zAt i, hz⟩⟩) ∈
                    Set.Icc (0 : ℝ) 1)})
  earlier_labels_are_first_witness_exclusions :
    let pieces :=
      SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
        G φ r X β n zAt B k hk
    ∀ ℓ : label, ℓ ∈ earlierFirstWitnessLabels →
      ∃ y : {x : V // x ∈ X}, y < x ∧
        sourceLabelEvent ℓ = (pieces.1 y)ᶜ ∧
        targetLabelEvent ℓ = (pieces.2 y)ᶜ
  earlier_first_witness_labels_exist :
    let pieces :=
      SamplingSplitOutsideBlockerActualFirstWitnessResidualPieces
        G φ r X β n zAt B k hk
    ∀ y : {x : V // x ∈ X}, ∀ hyx : y < x,
      ∃ ℓ ∈ earlierFirstWitnessLabels,
        sourceLabelEvent ℓ = (pieces.1 y)ᶜ ∧
        targetLabelEvent ℓ = (pieces.2 y)ᶜ
  cell_predicate_label_exists :
    ∃ ℓ ∈ cellPredicateLabels,
      sourceLabelEvent ℓ = cell ω ∧
      targetLabelEvent ℓ = targetCell ω
  cell_labels_are_current_cells :
    ∀ ℓ : label, ℓ ∈ cellPredicateLabels →
      sourceLabelEvent ℓ = cell ω ∧ targetLabelEvent ℓ = targetCell ω
  retained_common_source_test_labels_exist :
    ∀ y : {x : V // x ∈ X}, ∀ i : Fin n,
      ∀ hki : k < (i : ℕ), ∀ hyi : y.1 ∈ B i,
        ∃ ℓ ∈ retainedCommonSourceTestLabels,
          sourceLabelEvent ℓ =
            {η : Finset V × (V → ℝ) |
              ¬ (zAt i ∈ η.1 ∧
                η.2 y.1 < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
          targetLabelEvent ℓ =
            {η' : Finset V' × (V' → ℝ) |
              ∀ hz : zAt i ∉ insert r X ∧ G.Adj y.1 (zAt i),
                ¬ (β ⟨y, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ y.1) < η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∧
                    η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
  retained_common_labels_are_noncurrent_source_tests :
    ∀ ℓ : label, ℓ ∈ retainedCommonSourceTestLabels →
      ∃ y : {x : V // x ∈ X}, ∃ i : Fin n,
        k < (i : ℕ) ∧ G.Adj y.1 (zAt i) ∧
          sourceLabelEvent ℓ =
            {η : Finset V × (V → ℝ) |
              ¬ (zAt i ∈ η.1 ∧
                η.2 y.1 < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
          targetLabelEvent ℓ =
            {η' : Finset V' × (V' → ℝ) |
              ∀ hz : zAt i ∉ insert r X ∧ G.Adj y.1 (zAt i),
                ¬ (β ⟨y, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ y.1) < η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∧
                    η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
  already_private_target_test_labels_exist :
    ∀ y : {x : V // x ∈ X}, ∀ i : Fin n, ∀ hik : (i : ℕ) < k,
      ∀ hz : zAt i ∉ insert r X ∧ G.Adj y.1 (zAt i),
        ∃ ℓ ∈ alreadyPrivateTargetTestLabels,
          sourceLabelEvent ℓ =
            {η : Finset V × (V → ℝ) |
              ¬ (zAt i ∈ η.1 ∧
                η.2 y.1 < η.2 (zAt i) ∧
                  η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
          targetLabelEvent ℓ =
            {η' : Finset V' × (V' → ℝ) |
              ¬ (β ⟨y, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                η'.2 (φ y.1) < η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∧
                  η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
  already_private_labels_are_target_tests :
    ∀ ℓ : label, ℓ ∈ alreadyPrivateTargetTestLabels →
      ∃ y : {x : V // x ∈ X}, ∃ i : Fin n,
        (i : ℕ) < k ∧
          ∃ hz : zAt i ∉ insert r X ∧ G.Adj y.1 (zAt i),
            sourceLabelEvent ℓ =
              {η : Finset V × (V → ℝ) |
                ¬ (zAt i ∈ η.1 ∧
                  η.2 y.1 < η.2 (zAt i) ∧
                    η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)} ∧
            targetLabelEvent ℓ =
              {η' : Finset V' × (V' → ℝ) |
                ¬ (β ⟨y, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ y.1) < η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∧
                    η'.2 (β ⟨y, ⟨zAt i, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1)}
  global_boundary_complement_label_exists :
    ∃ ℓ ∈ globalBoundaryComplementLabels,
      sourceLabelEvent ℓ =
        {η : Finset V × (V → ℝ) |
          ¬ ∃ y : V, ∃ _hyX : y ∈ X,
            y ∈ η.1 ∧
              (∀ w : V, w ∈ insert r X → w ∈ η.1 →
                G.Adj y w → η.2 w < η.2 y) ∧
              (∀ i : Fin n, (k : ℕ) ≤ i → i ≠ ⟨k, hk⟩ →
                y ∈ B i →
                  ¬ (zAt i ∈ η.1 ∧
                    η.2 y < η.2 (zAt i) ∧
                      η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
              y ∈ B ⟨k, hk⟩ ∧
              ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                η.2 y < η.2 (zAt ⟨k, hk⟩) ∧
                  η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)} ∧
      targetLabelEvent ℓ =
        {η' : Finset V' × (V' → ℝ) |
          ¬ ∃ y : V, ∃ hyX : y ∈ X,
            φ y ∈ η'.1 ∧
              (∀ w : V, w ∈ insert r X → φ w ∈ η'.1 →
                G.Adj y w → η'.2 (φ w) < η'.2 (φ y)) ∧
              (∀ i : Fin n, (i : ℕ) < k + 1 →
                i ≠ ⟨k, hk⟩ → y ∈ B i →
                  ∀ hz : zAt i ∉ insert r X ∧ G.Adj y (zAt i),
                    ¬ (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                      η'.2 (φ y) <
                        η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩) ∧
                        η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩) ∈
                          Set.Icc (0 : ℝ) 1)) ∧
              y ∈ B ⟨k, hk⟩ ∧
              ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                  G.Adj y (zAt ⟨k, hk⟩),
                ¬ (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ y) <
                    η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∧
                    η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1)}
  global_boundary_labels_are_boundary_complements :
    ∀ ℓ : label, ℓ ∈ globalBoundaryComplementLabels →
      sourceLabelEvent ℓ =
        {η : Finset V × (V → ℝ) |
          ¬ ∃ y : V, ∃ _hyX : y ∈ X,
            y ∈ η.1 ∧
              (∀ w : V, w ∈ insert r X → w ∈ η.1 →
                G.Adj y w → η.2 w < η.2 y) ∧
              (∀ i : Fin n, (k : ℕ) ≤ i → i ≠ ⟨k, hk⟩ →
                y ∈ B i →
                  ¬ (zAt i ∈ η.1 ∧
                    η.2 y < η.2 (zAt i) ∧
                      η.2 (zAt i) ∈ Set.Icc (0 : ℝ) 1)) ∧
              y ∈ B ⟨k, hk⟩ ∧
              ¬ (zAt ⟨k, hk⟩ ∈ η.1 ∧
                η.2 y < η.2 (zAt ⟨k, hk⟩) ∧
                  η.2 (zAt ⟨k, hk⟩) ∈ Set.Icc (0 : ℝ) 1)} ∧
      targetLabelEvent ℓ =
        {η' : Finset V' × (V' → ℝ) |
          ¬ ∃ y : V, ∃ hyX : y ∈ X,
            φ y ∈ η'.1 ∧
              (∀ w : V, w ∈ insert r X → φ w ∈ η'.1 →
                G.Adj y w → η'.2 (φ w) < η'.2 (φ y)) ∧
              (∀ i : Fin n, (i : ℕ) < k + 1 →
                i ≠ ⟨k, hk⟩ → y ∈ B i →
                  ∀ hz : zAt i ∉ insert r X ∧ G.Adj y (zAt i),
                    ¬ (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩ ∈ η'.1 ∧
                      η'.2 (φ y) <
                        η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩) ∧
                        η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt i, hz⟩⟩) ∈
                          Set.Icc (0 : ℝ) 1)) ∧
              y ∈ B ⟨k, hk⟩ ∧
              ∀ hz : zAt ⟨k, hk⟩ ∉ insert r X ∧
                  G.Adj y (zAt ⟨k, hk⟩),
                ¬ (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩ ∈ η'.1 ∧
                  η'.2 (φ y) <
                    η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∧
                    η'.2 (β ⟨⟨y, hyX⟩, ⟨zAt ⟨k, hk⟩, hz⟩⟩) ∈
                      Set.Icc (0 : ℝ) 1)}
