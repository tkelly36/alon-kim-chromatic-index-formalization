import Tablet.LineGraphOfHypergraph

-- [TABLET NODE: ThreeUniformIndependentTripleRootLabeling]
theorem ThreeUniformIndependentTripleRootLabeling
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (f : E) (v : Fin 3 → V)
    (hcover : ∀ y ∈ H.edge f, ∃ i, v i = y)
    (S : Finset E) (hcard : S.card = 3)
    (hneigh : ∀ e ∈ S, (H.edge e ∩ H.edge f).Nonempty)
    (hind : ∀ e ∈ S, ∀ g ∈ S, e ≠ g → ¬ (LineGraphOfHypergraph H).Adj e g) :
    ∃ q : Fin 3 → E, Finset.univ.image q = S ∧
      (∀ i, v i ∈ H.edge (q i)) ∧
      (∀ i e, e ∈ S → v i ∈ H.edge e → e = q i) := by
-- BODY
  classical
  have hex (e : S) : ∃ i, v i ∈ H.edge e := by
    obtain ⟨y, hy⟩ := hneigh e e.property
    obtain ⟨i, hi⟩ := hcover y (Finset.mem_inter.mp hy).2
    exact ⟨i, hi ▸ (Finset.mem_inter.mp hy).1⟩
  choose r hr using hex
  have hrinj : Function.Injective r := by
    intro e g heq
    apply Subtype.ext
    by_contra hne
    exact hind e e.property g g.property hne
      ⟨hne, ⟨v (r e), Finset.mem_inter.mpr ⟨hr e, heq ▸ hr g⟩⟩⟩
  have hrsurj : Function.Surjective r := by
    apply (Fintype.bijective_iff_injective_and_card r).mpr
      ⟨hrinj, by simp [hcard]⟩ |>.2
  choose q hq using hrsurj
  refine ⟨fun i => (q i).val, ?_, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro e he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact (q i).property
    · rw [Finset.card_image_of_injective]
      · simp [hcard]
      · intro i j hij
        have heq : q i = q j := Subtype.ext hij
        simpa only [hq] using congrArg r heq
  · intro i
    simpa only [hq] using hr (q i)
  · intro i e he hve
    by_contra hne
    have hvq : v i ∈ H.edge (q i) := by simpa only [hq] using hr (q i)
    exact hind e he (q i) (q i).property hne
      ⟨hne, ⟨v i, Finset.mem_inter.mpr ⟨hve, hvq⟩⟩⟩
