import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTriplePatternCountingBridge]
theorem SamplingTriplePatternCountingBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ)
    (hregular : ∀ v : V, G.degree v = Delta)
    (r : V) (X : Finset V) (a b c : V)
    (haX : a ∈ X) (hbX : b ∈ X) (hcX : c ∈ X)
    (hXnbr : ∀ x : V, x ∈ X → G.Adj r x)
    (hclean :
      ∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
        ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab_ind : ¬ G.Adj a b) (hac_ind : ¬ G.Adj a c) (hbc_ind : ¬ G.Adj b c)
    (ell : Finset V → ℝ)
    (hell :
      ∀ P : Finset V,
        P.card = 2 → P ⊆ X →
          (∀ ⦃u⦄, u ∈ P → ∀ ⦃v⦄, v ∈ P → u ≠ v → ¬ G.Adj u v) →
            ∃ u : V, ∃ v : V,
              u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
                ell P =
                  ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) /
                    (Delta : ℝ)) :
    let Q : Finset V := {a, b, c}
    let n_a : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_b : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_c : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
    let n_ab : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_ac : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
    let n_bc : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
    let n_abc : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
    ell ({a, b} : Finset V) = ((n_ab + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
      ell ({a, c} : Finset V) = ((n_ac + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
      ell ({b, c} : Finset V) = ((n_bc + n_abc : ℕ) : ℝ) / (Delta : ℝ) ∧
      n_a + n_ab + n_ac + n_abc = Delta ∧
      n_b + n_ab + n_bc + n_abc = Delta ∧
      n_c + n_ac + n_bc + n_abc = Delta ∧
      n_b + n_bc = Delta - n_ab - n_abc ∧
      n_c = Delta - n_ac - n_bc - n_abc ∧
      r ∈ ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w) := by
-- BODY
  classical
  dsimp only
  set Q : Finset V := {a, b, c}
  set Sa : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w)
  set Sb : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w)
  set Sc : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w)
  set Sab : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w)
  set Sac : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w)
  set Sbc : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w)
  set Sabc : Finset V :=
    (Finset.univ.filter fun w : V =>
      w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w)
  have hclean_ab := hclean a haX b hbX hab
  have hclean_ac := hclean a haX c hcX hac
  have hclean_bc := hclean b hbX c hcX hbc
  have hpair_ab_card : ({a, b} : Finset V).card = 2 := by simp [hab]
  have hpair_ac_card : ({a, c} : Finset V).card = 2 := by simp [hac]
  have hpair_bc_card : ({b, c} : Finset V).card = 2 := by simp [hbc]
  have hpair_ab_sub : ({a, b} : Finset V) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haX
    · exact hbX
  have hpair_ac_sub : ({a, c} : Finset V) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haX
    · exact hcX
  have hpair_bc_sub : ({b, c} : Finset V) ⊆ X := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hbX
    · exact hcX
  have hpair_ab_ind :
      ∀ ⦃u⦄, u ∈ ({a, b} : Finset V) →
        ∀ ⦃v⦄, v ∈ ({a, b} : Finset V) → u ≠ v → ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hab_ind
    · exact fun h => hab_ind h.symm
    · exact (huv rfl).elim
  have hpair_ac_ind :
      ∀ ⦃u⦄, u ∈ ({a, c} : Finset V) →
        ∀ ⦃v⦄, v ∈ ({a, c} : Finset V) → u ≠ v → ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hac_ind
    · exact fun h => hac_ind h.symm
    · exact (huv rfl).elim
  have hpair_bc_ind :
      ∀ ⦃u⦄, u ∈ ({b, c} : Finset V) →
        ∀ ⦃v⦄, v ∈ ({b, c} : Finset V) → u ≠ v → ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hbc_ind
    · exact fun h => hbc_ind h.symm
    · exact (huv rfl).elim
  have hell_ab_raw := hell ({a, b} : Finset V) hpair_ab_card hpair_ab_sub hpair_ab_ind
  have hell_ac_raw := hell ({a, c} : Finset V) hpair_ac_card hpair_ac_sub hpair_ac_ind
  have hell_bc_raw := hell ({b, c} : Finset V) hpair_bc_card hpair_bc_sub hpair_bc_ind
  have hSabc_mem_r : r ∈ Sabc := by
    have hra : G.Adj r a := hXnbr a haX
    have hrb : G.Adj r b := hXnbr b hbX
    have hrc : G.Adj r c := hXnbr c hcX
    have hrau : r ≠ a := (G.ne_of_adj hra)
    have hrb_ne : r ≠ b := (G.ne_of_adj hrb)
    have hrc_ne : r ≠ c := (G.ne_of_adj hrc)
    simp [Sabc, Q, hrau, hrb_ne, hrc_ne, hra, hra.symm, hrb, hrb.symm, hrc, hrc.symm]
  have hnotQ_of_adj_a {w : V} (hwa : G.Adj a w) : w ∉ Q := by
    intro hw
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (G.ne_of_adj hwa rfl)
    · exact hab_ind hwa
    · exact hac_ind hwa
  have hnotQ_of_adj_b {w : V} (hwb : G.Adj b w) : w ∉ Q := by
    intro hw
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hab_ind hwb.symm
    · exact (G.ne_of_adj hwb rfl)
    · exact hbc_ind hwb
  have hnotQ_of_adj_c {w : V} (hwc : G.Adj c w) : w ∉ Q := by
    intro hw
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hac_ind hwc.symm
    · exact hbc_ind hwc.symm
    · exact (G.ne_of_adj hwc rfl)
  have hcommon_ab : (G.neighborFinset a ∩ G.neighborFinset b).card = Sab.card + Sabc.card := by
    have hsplit :
        (G.neighborFinset a ∩ G.neighborFinset b) =
          Sab ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        rcases hw with ⟨hwa, hwb⟩
        by_cases hwc : G.Adj c w
        · exact Finset.mem_union.mpr (Or.inr (by
            simp [Sabc, hnotQ_of_adj_a hwa, hwa, hwb, hwc]))
        · exact Finset.mem_union.mpr (Or.inl (by
            simp [Sab, hnotQ_of_adj_a hwa, hwa, hwb, hwc]))
      · intro hw
        rcases Finset.mem_union.mp hw with hw | hw
        · simp [Sab, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.1, hw.2.2.1⟩
        · simp [Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.1, hw.2.2.1⟩
    have hdis : Disjoint Sab Sabc := by
      rw [Finset.disjoint_left]
      intro w hwSab hwSabc
      simp [Sab] at hwSab
      simp [Sabc] at hwSabc
      exact hwSab.2.2.2 hwSabc.2.2.2
    rw [hsplit, Finset.card_union_of_disjoint hdis]
  have hcommon_ac : (G.neighborFinset a ∩ G.neighborFinset c).card = Sac.card + Sabc.card := by
    have hsplit :
        (G.neighborFinset a ∩ G.neighborFinset c) =
          Sac ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        rcases hw with ⟨hwa, hwc⟩
        by_cases hwb : G.Adj b w
        · exact Finset.mem_union.mpr (Or.inr (by
            simp [Sabc, hnotQ_of_adj_a hwa, hwa, hwb, hwc]))
        · exact Finset.mem_union.mpr (Or.inl (by
            simp [Sac, hnotQ_of_adj_a hwa, hwa, hwb, hwc]))
      · intro hw
        rcases Finset.mem_union.mp hw with hw | hw
        · simp [Sac, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.1, hw.2.2.2⟩
        · simp [Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.1, hw.2.2.2⟩
    have hdis : Disjoint Sac Sabc := by
      rw [Finset.disjoint_left]
      intro w hwSac hwSabc
      simp [Sac] at hwSac
      simp [Sabc] at hwSabc
      exact hwSac.2.2.1 hwSabc.2.2.1
    rw [hsplit, Finset.card_union_of_disjoint hdis]
  have hcommon_bc : (G.neighborFinset b ∩ G.neighborFinset c).card = Sbc.card + Sabc.card := by
    have hsplit :
        (G.neighborFinset b ∩ G.neighborFinset c) =
          Sbc ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
        rcases hw with ⟨hwb, hwc⟩
        by_cases hwa : G.Adj a w
        · exact Finset.mem_union.mpr (Or.inr (by
            simp [Sabc, hnotQ_of_adj_b hwb, hwa, hwb, hwc]))
        · exact Finset.mem_union.mpr (Or.inl (by
            simp [Sbc, hnotQ_of_adj_b hwb, hwa, hwb, hwc]))
      · intro hw
        rcases Finset.mem_union.mp hw with hw | hw
        · simp [Sbc, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.2.1, hw.2.2.2⟩
        · simp [Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
          exact ⟨hw.2.2.1, hw.2.2.2⟩
    have hdis : Disjoint Sbc Sabc := by
      rw [Finset.disjoint_left]
      intro w hwSbc hwSabc
      simp [Sbc] at hwSbc
      simp [Sabc] at hwSabc
      exact hwSbc.2.1 hwSabc.2.1
    rw [hsplit, Finset.card_union_of_disjoint hdis]
  have hell_ab : ell ({a, b} : Finset V) = ((Sab.card + Sabc.card : ℕ) : ℝ) / (Delta : ℝ) := by
    rcases hell_ab_raw with ⟨u, v, hu, hv, huv, hval⟩
    have hu_cases : u = a ∨ u = b := by simpa using hu
    have hv_cases : v = a ∨ v = b := by simpa using hv
    have hcard_uv :
        (G.neighborFinset u ∩ G.neighborFinset v).card =
          (G.neighborFinset a ∩ G.neighborFinset b).card := by
      rcases hu_cases with rfl | rfl <;> rcases hv_cases with rfl | rfl
      · exact (huv rfl).elim
      · rfl
      · rw [Finset.inter_comm]
      · exact (huv rfl).elim
    rw [hval, hcard_uv, hcommon_ab]
  have hell_ac : ell ({a, c} : Finset V) = ((Sac.card + Sabc.card : ℕ) : ℝ) / (Delta : ℝ) := by
    rcases hell_ac_raw with ⟨u, v, hu, hv, huv, hval⟩
    have hu_cases : u = a ∨ u = c := by simpa using hu
    have hv_cases : v = a ∨ v = c := by simpa using hv
    have hcard_uv :
        (G.neighborFinset u ∩ G.neighborFinset v).card =
          (G.neighborFinset a ∩ G.neighborFinset c).card := by
      rcases hu_cases with rfl | rfl <;> rcases hv_cases with rfl | rfl
      · exact (huv rfl).elim
      · rfl
      · rw [Finset.inter_comm]
      · exact (huv rfl).elim
    rw [hval, hcard_uv, hcommon_ac]
  have hell_bc : ell ({b, c} : Finset V) = ((Sbc.card + Sabc.card : ℕ) : ℝ) / (Delta : ℝ) := by
    rcases hell_bc_raw with ⟨u, v, hu, hv, huv, hval⟩
    have hu_cases : u = b ∨ u = c := by simpa using hu
    have hv_cases : v = b ∨ v = c := by simpa using hv
    have hcard_uv :
        (G.neighborFinset u ∩ G.neighborFinset v).card =
          (G.neighborFinset b ∩ G.neighborFinset c).card := by
      rcases hu_cases with rfl | rfl <;> rcases hv_cases with rfl | rfl
      · exact (huv rfl).elim
      · rfl
      · rw [Finset.inter_comm]
      · exact (huv rfl).elim
    rw [hval, hcard_uv, hcommon_bc]
  have hdeg_a : Sa.card + Sab.card + Sac.card + Sabc.card = Delta := by
    have hsplit :
        G.neighborFinset a = Sa ∪ Sab ∪ Sac ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [SimpleGraph.mem_neighborFinset] at hw
        have hnotQ := hnotQ_of_adj_a hw
        by_cases hwb : G.Adj b w <;> by_cases hwc : G.Adj c w
        · simp [Sa, Sab, Sac, Sabc, hnotQ, hw, hwb, hwc]
        · simp [Sa, Sab, Sac, Sabc, hnotQ, hw, hwb, hwc]
        · simp [Sa, Sab, Sac, Sabc, hnotQ, hw, hwb, hwc]
        · simp [Sa, Sab, Sac, Sabc, hnotQ, hw, hwb, hwc]
      · intro hw
        simp [Sa, Sab, Sac, Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
        tauto
    have hdis1 : Disjoint Sa Sab := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sa] at h1
      simp [Sab] at h2
      exact h1.2.2.1 h2.2.2.1
    have hdis2 : Disjoint (Sa ∪ Sab) Sac := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sa, Sab] at h1
      simp [Sac] at h2
      tauto
    have hdis3 : Disjoint (Sa ∪ Sab ∪ Sac) Sabc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sa, Sab, Sac] at h1
      simp [Sabc] at h2
      tauto
    have hcard :
        (G.neighborFinset a).card =
          Sa.card + Sab.card + Sac.card + Sabc.card := by
      rw [hsplit]
      rw [Finset.card_union_of_disjoint hdis3, Finset.card_union_of_disjoint hdis2,
        Finset.card_union_of_disjoint hdis1]
    rw [← hcard, SimpleGraph.card_neighborFinset_eq_degree, hregular a]
  have hdeg_b_full : Sb.card + Sab.card + Sbc.card + Sabc.card = Delta := by
    have hsplit :
        G.neighborFinset b = Sb ∪ Sab ∪ Sbc ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [SimpleGraph.mem_neighborFinset] at hw
        have hnotQ := hnotQ_of_adj_b hw
        by_cases hwa : G.Adj a w <;> by_cases hwc : G.Adj c w
        · simp [Sb, Sab, Sbc, Sabc, hnotQ, hw, hwa, hwc]
        · simp [Sb, Sab, Sbc, Sabc, hnotQ, hw, hwa, hwc]
        · simp [Sb, Sab, Sbc, Sabc, hnotQ, hw, hwa, hwc]
        · simp [Sb, Sab, Sbc, Sabc, hnotQ, hw, hwa, hwc]
      · intro hw
        simp [Sb, Sab, Sbc, Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
        tauto
    have hdis1 : Disjoint Sb Sab := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sb] at h1
      simp [Sab] at h2
      exact h1.2.1 h2.2.1
    have hdis2 : Disjoint (Sb ∪ Sab) Sbc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sb, Sab] at h1
      simp [Sbc] at h2
      tauto
    have hdis3 : Disjoint (Sb ∪ Sab ∪ Sbc) Sabc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sb, Sab, Sbc] at h1
      simp [Sabc] at h2
      tauto
    have hcard :
        (G.neighborFinset b).card =
          Sb.card + Sab.card + Sbc.card + Sabc.card := by
      rw [hsplit]
      rw [Finset.card_union_of_disjoint hdis3, Finset.card_union_of_disjoint hdis2,
        Finset.card_union_of_disjoint hdis1]
    rw [← hcard, SimpleGraph.card_neighborFinset_eq_degree, hregular b]
  have hdeg_c_full : Sc.card + Sac.card + Sbc.card + Sabc.card = Delta := by
    have hsplit :
        G.neighborFinset c = Sc ∪ Sac ∪ Sbc ∪ Sabc := by
      ext w
      constructor
      · intro hw
        simp only [SimpleGraph.mem_neighborFinset] at hw
        have hnotQ := hnotQ_of_adj_c hw
        by_cases hwa : G.Adj a w <;> by_cases hwb : G.Adj b w
        · simp [Sc, Sac, Sbc, Sabc, hnotQ, hw, hwa, hwb]
        · simp [Sc, Sac, Sbc, Sabc, hnotQ, hw, hwa, hwb]
        · simp [Sc, Sac, Sbc, Sabc, hnotQ, hw, hwa, hwb]
        · simp [Sc, Sac, Sbc, Sabc, hnotQ, hw, hwa, hwb]
      · intro hw
        simp [Sc, Sac, Sbc, Sabc, SimpleGraph.mem_neighborFinset] at hw ⊢
        tauto
    have hdis1 : Disjoint Sc Sac := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sc] at h1
      simp [Sac] at h2
      exact h1.2.1 h2.2.1
    have hdis2 : Disjoint (Sc ∪ Sac) Sbc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sc, Sac] at h1
      simp [Sbc] at h2
      tauto
    have hdis3 : Disjoint (Sc ∪ Sac ∪ Sbc) Sabc := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp [Sc, Sac, Sbc] at h1
      simp [Sabc] at h2
      tauto
    have hcard :
        (G.neighborFinset c).card =
          Sc.card + Sac.card + Sbc.card + Sabc.card := by
      rw [hsplit]
      rw [Finset.card_union_of_disjoint hdis3, Finset.card_union_of_disjoint hdis2,
        Finset.card_union_of_disjoint hdis1]
    rw [← hcard, SimpleGraph.card_neighborFinset_eq_degree, hregular c]
  refine ⟨hell_ab, hell_ac, hell_bc, hdeg_a, hdeg_b_full, hdeg_c_full, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact hSabc_mem_r
