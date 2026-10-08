import Tablet.Preamble

set_option linter.unusedSimpArgs false

open BigOperators

-- [TABLET NODE: SamplingThreeSetPairSumNormalizer]
theorem SamplingThreeSetPairSumNormalizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset V) (hQcard : Q.card = 3) (F : Finset V → ℝ) :
    ∃ a b c : V,
      a ∈ Q ∧ b ∈ Q ∧ c ∈ Q ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Q = ({a, b, c} : Finset V) ∧
      ((Finset.univ : Finset (Finset V)).filter
          (fun P : Finset V => P.card = 2 ∧ P ⊆ Q)) =
        ({({a, b} : Finset V), ({a, c} : Finset V), ({b, c} : Finset V)} :
          Finset (Finset V)) ∧
      (∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then F P else 0) =
        F ({a, b} : Finset V) + F ({a, c} : Finset V) + F ({b, c} : Finset V) := by
-- BODY
  classical
  rcases (Finset.card_eq_three.mp hQcard) with ⟨a, b, c, hab, hac, hbc, hQ⟩
  refine ⟨a, b, c, ?_, ?_, ?_, hab, hac, hbc, hQ, ?_, ?_⟩
  · simp [hQ]
  · simp [hQ]
  · simp [hQ]
  · ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hP
      rcases (Finset.card_eq_two.mp hP.1) with ⟨x, y, hxy, rfl⟩
      have hx : x = a ∨ x = b ∨ x = c := by
        have hxQ : x ∈ Q := hP.2 (by simp)
        rw [hQ] at hxQ
        simpa using hxQ
      have hy : y = a ∨ y = b ∨ y = c := by
        have hyQ : y ∈ Q := hP.2 (by simp)
        rw [hQ] at hyQ
        simpa using hyQ
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact (hxy rfl).elim
        | simp [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, Finset.pair_comm]
    · intro hP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl | rfl
      · constructor
        · simp [hab]
        · intro x hx
          rw [hQ]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl <;> simp
      · constructor
        · simp [hac]
        · intro x hx
          rw [hQ]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl <;> simp
      · constructor
        · simp [hbc]
        · intro x hx
          rw [hQ]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
          rcases hx with rfl | rfl <;> simp
  · rw [← Finset.sum_filter]
    rw [show ((Finset.univ : Finset (Finset V)).filter
          (fun P : Finset V => P.card = 2 ∧ P ⊆ Q)) =
        ({({a, b} : Finset V), ({a, c} : Finset V), ({b, c} : Finset V)} :
          Finset (Finset V)) by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hP
        rcases (Finset.card_eq_two.mp hP.1) with ⟨x, y, hxy, rfl⟩
        have hx : x = a ∨ x = b ∨ x = c := by
          have hxQ : x ∈ Q := hP.2 (by simp)
          rw [hQ] at hxQ
          simpa using hxQ
        have hy : y = a ∨ y = b ∨ y = c := by
          have hyQ : y ∈ Q := hP.2 (by simp)
          rw [hQ] at hyQ
          simpa using hyQ
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first
          | exact (hxy rfl).elim
          | simp [hab, hab.symm, hac, hac.symm, hbc, hbc.symm, Finset.pair_comm]
      · intro hP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hP
        rcases hP with rfl | rfl | rfl
        · constructor
          · simp [hab]
          · intro x hx
            rw [hQ]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl <;> simp
        · constructor
          · simp [hac]
          · intro x hx
            rw [hQ]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl <;> simp
        · constructor
          · simp [hbc]
          · intro x hx
            rw [hQ]
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            rcases hx with rfl | rfl <;> simp]
    have h_ab_ac : ({a, b} : Finset V) ≠ ({a, c} : Finset V) := by
      intro h
      have hc_mem : c ∈ ({a, b} : Finset V) := by
        rw [h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc_mem
      rcases hc_mem with hca | hcb
      · exact hac hca.symm
      · exact hbc hcb.symm
    have h_ab_bc : ({a, b} : Finset V) ≠ ({b, c} : Finset V) := by
      intro h
      have ha_mem : a ∈ ({b, c} : Finset V) := by
        rw [← h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with hab_eq | hac_eq
      · exact hab hab_eq
      · exact hac hac_eq
    have h_ac_bc : ({a, c} : Finset V) ≠ ({b, c} : Finset V) := by
      intro h
      have ha_mem : a ∈ ({b, c} : Finset V) := by
        rw [← h]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with hab_eq | hac_eq
      · exact hab hab_eq
      · exact hac hac_eq
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · simp
        ring
      · simp [h_ac_bc]
    · simp [h_ab_ac, h_ab_bc]
