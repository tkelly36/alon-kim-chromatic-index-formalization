import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: FiniteUnorderedPairProductSum]
theorem FiniteUnorderedPairProductSum
    {V R : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] [CommSemiring R]
    (s : Finset V) (f : V → R) :
    (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ s), ∏ v ∈ p, f v) =
    ∑ v ∈ s, ∑ w ∈ s.filter (fun w => v < w), f v * f w := by
-- BODY
  classical
  let t := (s ×ˢ s).filter (fun p => p.1 < p.2)
  have hsum : (∑ p ∈ t, f p.1 * f p.2) =
      ∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ s), ∏ v ∈ p, f v := by
    apply Finset.sum_bij (fun p _ => {p.1, p.2})
    · intro p hp
      obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simp [ne_of_lt hlt], ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ha
      · exact (Finset.mem_singleton.mp hv) ▸ hb
    · intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      have ha : p.1 = q.1 ∨ p.1 = q.2 := by
        have : p.1 ∈ ({q.1, q.2} : Finset V) := by rw [← heq]; simp
        simpa using this
      have hb : p.2 = q.1 ∨ p.2 = q.2 := by
        have : p.2 ∈ ({q.1, q.2} : Finset V) := by rw [← heq]; simp
        simpa using this
      apply Prod.ext <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> grind
    · intro p hp
      obtain ⟨hcard, hsub⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
      have ha : a ∈ s := hsub (by simp)
      have hb : b ∈ s := hsub (by simp)
      rcases lt_or_gt_of_ne hab with hlt | hlt
      · exact ⟨(a,b), by simp [t, ha, hb, hlt], rfl⟩
      · exact ⟨(b,a), by simp [t, ha, hb, hlt], by simp [Finset.pair_comm]⟩
    · intro p hp
      exact (Finset.prod_pair (ne_of_lt (Finset.mem_filter.mp hp).2)).symm
  rw [← hsum]
  simp only [t, Finset.sum_filter, Finset.sum_product]
