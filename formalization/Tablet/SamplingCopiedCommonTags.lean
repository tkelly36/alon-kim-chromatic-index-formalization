import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingCopiedCommonTags]
theorem SamplingCopiedCommonTags
    {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (φ : V → W) (S : Finset V) (hφ : Function.Injective φ) :
    ∃ (T : Type u) (_ : Fintype T) (s : V → T) (t : W → T),
      Function.Injective s ∧ Function.Injective t ∧
      (∀ v w, s v = t w ↔ v ∈ S ∧ φ v = w) ∧
      (∀ a, (∃ v, s v = a) ∨ (∃ w, t w = a)) := by
-- BODY
  classical
  let T := V ⊕ {w : W // w ∉ S.image φ}
  let s : V → T := Sum.inl
  have hex (w : W) (h : w ∈ S.image φ) : ∃ v, v ∈ S ∧ φ v = w :=
    Finset.mem_image.mp h
  let t : W → T := fun w => if h : w ∈ S.image φ then
    Sum.inl (Classical.choose (hex w h)) else Sum.inr ⟨w, h⟩
  have ht (v : V) (w : W) : s v = t w ↔ v ∈ S ∧ φ v = w := by
    dsimp [s, t]
    split_ifs with h
    · have hc := Classical.choose_spec (hex w h)
      constructor
      · intro he
        have he' := Sum.inl.inj he
        rw [he']
        exact hc
      · intro hv
        exact congrArg Sum.inl (hφ (hv.2.trans hc.2.symm))
    · simp only [false_iff, not_and]
      intro hv he
      exact h (Finset.mem_image.mpr ⟨v, hv, he⟩)
  refine ⟨T, inferInstance, s, t, Sum.inl_injective, ?_, ht, ?_⟩
  · intro w z hwz
    by_cases hw : w ∈ S.image φ
    · obtain ⟨v, hv, hvw⟩ := hex w hw
      have hvs := (ht v w).2 ⟨hv, hvw⟩
      exact hvw.symm.trans ((ht v z).1 (hvs.trans hwz)).2
    · by_cases hz : z ∈ S.image φ
      · obtain ⟨v, hv, hvz⟩ := hex z hz
        have hvs := (ht v z).2 ⟨hv, hvz⟩
        exact ((ht v w).1 (hvs.trans hwz.symm)).2.symm.trans hvz
      · have hh : (⟨w, hw⟩ : {w : W // w ∉ S.image φ}) = ⟨z, hz⟩ := by
          apply Sum.inr.inj (α := V)
          simpa only [t, dif_neg hw, dif_neg hz] using hwz
        exact congrArg Subtype.val hh
  · intro a
    cases a with
    | inl v => exact Or.inl ⟨v, rfl⟩
    | inr w => exact Or.inr ⟨w.val, by simp only [t, dif_neg w.property]⟩
