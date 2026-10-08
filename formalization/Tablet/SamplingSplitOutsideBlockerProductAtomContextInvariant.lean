import Tablet.SamplingSplitOutsideBlockerProductDecode

-- [TABLET NODE: SamplingSplitOutsideBlockerProductAtomContextInvariant]
theorem SamplingSplitOutsideBlockerProductAtomContextInvariant
    {V V' T : Type*} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] (φ : V → V')
    (S : Finset V) (S' : Finset V') (hS' : S' = S.image φ)
    (s : V → T) (t : V' → T)
    (hoverlap : ∀ v v', s v = t v' ↔ v ∈ S ∧ φ v = v')
    (C : Set (Finset V × (V → ℝ)))
    (C' : Set (Finset V' × (V' → ℝ)))
    (htransport : ∀ η η',
      η'.1 ∩ S' = (η.1 ∩ S).image φ →
      (∀ v ∈ S, η'.2 (φ v) = η.2 v) → (η ∈ C ↔ η' ∈ C')) :
    let D := SamplingSplitOutsideBlockerProductDecode s t
    let pairedCell := {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
      ζ.1 ∈ C ∧ ζ.2 ∈ C' ∧ ζ.2.1 ∩ S' = (ζ.1.1 ∩ S).image φ ∧
      ∀ v ∈ S, ζ.2.2 (φ v) = ζ.1.2 v}
    (∀ q, D q ∈ pairedCell ↔ (D q).1 ∈ C) ∧
    (∀ q q', (∀ v ∈ S, q (s v) = q' (s v)) →
      (D q ∈ pairedCell ↔ D q' ∈ pairedCell)) := by
-- BODY
  classical
  dsimp only
  let D := SamplingSplitOutsideBlockerProductDecode s t
  have hsync (q q' : T → ℝ × ℝ)
      (h : ∀ v ∈ S, q (s v) = q' (s v)) :
      (D q').2.1 ∩ S' = ((D q).1.1 ∩ S).image φ ∧
      ∀ v ∈ S, (D q').2.2 (φ v) = (D q).1.2 v := by
    have ht (v : V) (hv : v ∈ S) : s v = t (φ v) :=
      (hoverlap v (φ v)).mpr ⟨hv, rfl⟩
    constructor
    · ext v'
      simp only [Finset.mem_inter, Finset.mem_image]
      constructor
      · rintro ⟨ha, hb⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hS' ▸ hb)
        refine ⟨v, ⟨?_, hv⟩, rfl⟩
        change v ∈ Finset.univ.filter (fun v => (q (s v)).1 = 1)
        have ha' : (q' (t (φ v))).1 = 1 := (Finset.mem_filter.mp ha).2
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by rw [h v hv, ht v hv]; exact ha'⟩
      · rintro ⟨v, ⟨ha, hv⟩, rfl⟩
        constructor
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have ha' : (q (s v)).1 = 1 := (Finset.mem_filter.mp ha).2
          rw [← ht v hv, ← h v hv]
          exact ha'
        · rw [hS']
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · intro v hv
      change (q' (t (φ v))).2 = (q (s v)).2
      rw [← ht v hv, h v hv]
  have heq (q : T → ℝ × ℝ) := hsync q q (fun _ _ => rfl)
  have hcell (q : T → ℝ × ℝ) :
      ((D q).1 ∈ C ∧ (D q).2 ∈ C' ∧
        (D q).2.1 ∩ S' = ((D q).1.1 ∩ S).image φ ∧
        ∀ v ∈ S, (D q).2.2 (φ v) = (D q).1.2 v) ↔ (D q).1 ∈ C := by
    exact ⟨fun h => h.1, fun h =>
      ⟨h, (htransport _ _ (heq q).1 (heq q).2).mp h, heq q⟩⟩
  refine ⟨hcell, ?_⟩
  intro q q' h
  exact (hcell q).trans
    (((htransport _ _ (hsync q q' h).1 (hsync q q' h).2).trans
      (htransport _ _ (heq q').1 (heq q').2).symm).trans (hcell q').symm)
