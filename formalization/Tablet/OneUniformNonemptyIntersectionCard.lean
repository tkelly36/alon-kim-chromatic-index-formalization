import Tablet.UniformHypergraph

-- [TABLET NODE: OneUniformNonemptyIntersectionCard]
theorem OneUniformNonemptyIntersectionCard :
    ∀ {V E : Type*} [DecidableEq V], ∀ H : MultiHypergraph V E,
      UniformHypergraph H 1 →
      ∀ f g : E, (H.edge g ∩ H.edge f).Nonempty →
        (H.edge g ∩ H.edge f).card = 1 := by
-- BODY
  intro V E _ H hunif f g hnon
  have hpos : 0 < (H.edge g ∩ H.edge f).card := Finset.card_pos.mpr hnon
  have hle : (H.edge g ∩ H.edge f).card ≤ 1 := by
    calc
      (H.edge g ∩ H.edge f).card ≤ (H.edge f).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 1 := hunif f
  omega
