import Tablet.Preamble

open BigOperators

set_option maxHeartbeats 2000000

-- [TABLET NODE: SamplingTripleCorrectionReindexing]
theorem SamplingTripleCorrectionReindexing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ)
    (hregular : ∀ v : V, G.degree v = Delta)
    (r : V) (X : Finset V)
    (hXnbr : ∀ x : V, x ∈ X → G.Adj r x)
    (hclean : ∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
      ¬ ∃ w : V, G.Adj u w ∧ G.Adj v w ∧ w ≠ r ∧ ¬ G.Adj r w)
    (W : Finset V → ℝ)
    (hW : ∀ P : Finset V,
      P ∈ ((Finset.univ : Finset (Finset V)).filter fun P : Finset V =>
        P.card = 2 ∧ P ⊆ X ∧
          ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b) → 0 ≤ W P) :
    let J2 : Finset (Finset V) :=
      (Finset.univ.filter fun P : Finset V =>
        P.card = 2 ∧ P ⊆ X ∧
          ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
    let J3 : Finset (Finset V) :=
      (Finset.univ.filter fun Q : Finset V =>
        Q.card = 3 ∧ Q ⊆ X ∧
          ∀ ⦃a⦄, a ∈ Q → ∀ ⦃b⦄, b ∈ Q → a ≠ b → ¬ G.Adj a b)
    let C : Finset V → Finset V := fun P : Finset V =>
      (Finset.univ.filter fun w : V => ∀ u : V, u ∈ P → G.Adj u w)
    (∑ Q : Finset V, if Q ∈ J3 then
        ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
      else 0) ≤
      ∑ P : Finset V, if P ∈ J2 then ((Delta - (C P).card : ℕ) : ℝ) * W P else 0 := by
-- BODY
  classical
  intro J2 J3 C
  have hpair_of_triple : ∀ P Q : Finset V, Q ∈ J3 → P.card = 2 → P ⊆ Q → P ∈ J2 := by
    intro P Q hQ hPcard hPQ
    have hQdata := Finset.mem_filter.mp hQ
    simp only [J2, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hPcard, fun x hx => hQdata.2.2.1 (hPQ hx), ?_⟩
    intro a ha b hb hab
    exact hQdata.2.2.2 (hPQ ha) (hPQ hb) hab
  have hcount_le : ∀ P : Finset V, P ∈ J2 → ((J3.filter fun Q => P ⊆ Q).card) ≤
      Delta - (C P).card := by
    intro P hPJ2
    have hPdata := Finset.mem_filter.mp hPJ2
    have hPcard : P.card = 2 := hPdata.2.1
    have hPX : P ⊆ X := hPdata.2.2.1
    rcases Finset.card_eq_two.mp hPcard with ⟨u, v, huv_ne, hPuv⟩
    have huP : u ∈ P := by simp [hPuv]
    have hvP : v ∈ P := by simp [hPuv]
    have huX : u ∈ X := hPX huP
    have hvX : v ∈ X := hPX hvP
    have hrC : r ∈ C P := by
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      intro z hz
      rw [hPuv] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · subst z
        exact (hXnbr u huX).symm
      · subst z
        exact (hXnbr v hvX).symm
    have hCerase_sub : (C P).erase r ⊆ G.neighborFinset r \ P := by
      intro w hw
      have hwC : w ∈ C P := (Finset.mem_erase.mp hw).2
      have hwr : w ≠ r := (Finset.mem_erase.mp hw).1
      have huw : G.Adj u w := (Finset.mem_filter.mp hwC).2 u huP
      have hvw : G.Adj v w := (Finset.mem_filter.mp hwC).2 v hvP
      have hrw : G.Adj r w := by
        by_contra hnot
        exact (hclean u huX v hvX huv_ne) ⟨w, huw, hvw, hwr, hnot⟩
      have hw_not_P : w ∉ P := by
        intro hwP
        have hww : G.Adj w w := (Finset.mem_filter.mp hwC).2 w hwP
        exact SimpleGraph.irrefl G hww
      simp [SimpleGraph.mem_neighborFinset, hrw, hw_not_P]
    let A : Finset V := X \ (C P ∪ P)
    let F : Finset (Finset V) := J3.filter fun Q => P ⊆ Q
    have hthird_exists : ∀ Q : Finset V, Q ∈ F → ∃ w : V, w ∈ Q ∧ w ∉ P ∧
        Q = insert w P := by
      intro Q hQF
      have hQJ3 : Q ∈ J3 := (Finset.mem_filter.mp hQF).1
      have hPQ : P ⊆ Q := (Finset.mem_filter.mp hQF).2
      have hQdata := Finset.mem_filter.mp hQJ3
      have hdiff_card : (Q \ P).card = 1 := by
        rw [Finset.card_sdiff_of_subset hPQ, hQdata.2.1, hPcard]
      rcases Finset.card_eq_one.mp hdiff_card with ⟨w, hw_eq⟩
      refine ⟨w, ?_, ?_, ?_⟩
      · have : w ∈ Q \ P := by simp [hw_eq]
        exact (Finset.mem_sdiff.mp this).1
      · have : w ∈ Q \ P := by simp [hw_eq]
        exact (Finset.mem_sdiff.mp this).2
      · ext z
        constructor
        · intro hzQ
          by_cases hzP : z ∈ P
          · simp [hzP]
          · have hzDiff : z ∈ Q \ P := by simp [hzQ, hzP]
            have hzw : z = w := by
              have : z ∈ ({w} : Finset V) := by simpa [hw_eq] using hzDiff
              simpa using this
            simp [hzw]
        · intro hz
          simp only [Finset.mem_insert] at hz
          rcases hz with hzw | hzP
          · subst z
            have : w ∈ Q \ P := by simp [hw_eq]
            exact (Finset.mem_sdiff.mp this).1
          · exact hPQ hzP
    let thirdOpt : Finset V → Option V := fun Q =>
      if h : ∃ w : V, w ∈ Q ∧ w ∉ P ∧ Q = insert w P then some (Classical.choose h)
      else none
    have hmap : (F : Set (Finset V)).MapsTo thirdOpt (A.image some : Set (Option V)) := by
      intro Q hQF
      have hex := hthird_exists Q hQF
      have hspec := Classical.choose_spec hex
      have hQJ3 : Q ∈ J3 := (Finset.mem_filter.mp hQF).1
      have hPQ : P ⊆ Q := (Finset.mem_filter.mp hQF).2
      have hQdata := Finset.mem_filter.mp hQJ3
      have hwA : Classical.choose hex ∈ A := by
        have hwQ := hspec.1
        have hnotP := hspec.2.1
        have hwX : Classical.choose hex ∈ X := hQdata.2.2.1 hwQ
        have hnotC : Classical.choose hex ∉ C P := by
          intro hwC
          have hadj_u : G.Adj u (Classical.choose hex) := (Finset.mem_filter.mp hwC).2 u huP
          have hwu_ne : u ≠ Classical.choose hex := by
            intro h
            subst h
            exact hnotP huP
          exact hQdata.2.2.2 (hPQ huP) hwQ hwu_ne hadj_u
        simp [A, hwX, hnotC, hnotP]
      simp [thirdOpt, hex, hwA]
    have hinj : Set.InjOn thirdOpt (↑F : Set (Finset V)) := by
      intro Q hQF R hRF heq
      have hexQ := hthird_exists Q hQF
      have hexR := hthird_exists R hRF
      have hspecQ := Classical.choose_spec hexQ
      have hspecR := Classical.choose_spec hexR
      have hthird_eq : Classical.choose hexQ = Classical.choose hexR := by
        have := heq
        simp [thirdOpt, hexQ, hexR] at this
        exact this
      rw [hspecQ.2.2, hspecR.2.2, hthird_eq]
    have hF_le_Aimg : F.card ≤ (A.image some).card :=
      Finset.card_le_card_of_injOn thirdOpt hmap hinj
    have hAimg_card : (A.image some).card = A.card := by
      rw [Finset.card_image_of_injective]
      intro a b h
      exact Option.some.inj h
    have hF_le_A : F.card ≤ A.card := by simpa [hAimg_card] using hF_le_Aimg
    have hA_union_sub : A ∪ (C P).erase r ⊆ G.neighborFinset r \ P := by
      intro w hw
      simp only [Finset.mem_union] at hw
      rcases hw with hwA | hwCe
      · have hwX : w ∈ X := by simpa [A] using (Finset.mem_sdiff.mp hwA).1
        have hnot_union : w ∉ C P ∪ P := (Finset.mem_sdiff.mp (by simpa [A] using hwA)).2
        have hw_nei : w ∈ G.neighborFinset r := by
          simpa [SimpleGraph.mem_neighborFinset] using hXnbr w hwX
        have hw_notP : w ∉ P := by
          intro hwP
          exact hnot_union (by simp [hwP])
        simp [hw_nei, hw_notP]
      · exact hCerase_sub hwCe
    have hdisj : Disjoint A ((C P).erase r) := by
      rw [Finset.disjoint_left]
      intro w hwA hwCe
      have hwC : w ∈ C P := (Finset.mem_erase.mp hwCe).2
      have hnot_union : w ∉ C P ∪ P := (Finset.mem_sdiff.mp (by simpa [A] using hwA)).2
      exact hnot_union (by simp [hwC])
    have hcard_union : (A ∪ (C P).erase r).card = A.card + ((C P).erase r).card := by
      rw [Finset.card_union_of_disjoint hdisj]
    have hneighbor_diff_card : (G.neighborFinset r \ P).card = Delta - 2 := by
      have hP_sub_nei : P ⊆ G.neighborFinset r := by
        intro z hz
        have hzX := hPX hz
        simpa [SimpleGraph.mem_neighborFinset] using hXnbr z hzX
      rw [Finset.card_sdiff_of_subset hP_sub_nei]
      rw [SimpleGraph.card_neighborFinset_eq_degree, hregular r, hPcard]
    have hsum_le : A.card + ((C P).erase r).card ≤ Delta - 2 := by
      rw [← hcard_union]
      calc
        (A ∪ (C P).erase r).card ≤ (G.neighborFinset r \ P).card :=
          Finset.card_le_card hA_union_sub
        _ = Delta - 2 := hneighbor_diff_card
    have hCerase_card : ((C P).erase r).card = (C P).card - 1 := by
      rw [Finset.card_erase_of_mem hrC]
    have hA_le : A.card ≤ Delta - (C P).card := by
      rw [hCerase_card] at hsum_le
      omega
    simpa [F] using hF_le_A.trans hA_le
  have hleft_rewrite :
      (∑ Q : Finset V, if Q ∈ J3 then
          ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
        else 0) =
        ∑ P : Finset V, ∑ Q : Finset V,
          if Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q then W P else 0 := by
    calc
      (∑ Q : Finset V, if Q ∈ J3 then
          ∑ P : Finset V, if P.card = 2 ∧ P ⊆ Q then W P else 0
        else 0)
          = ∑ Q : Finset V, ∑ P : Finset V,
              if Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q then W P else 0 := by
              apply Finset.sum_congr rfl
              intro Q _
              by_cases hQ : Q ∈ J3 <;> simp [hQ]
      _ = ∑ P : Finset V, ∑ Q : Finset V,
              if Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q then W P else 0 := by
              rw [Finset.sum_comm]
  rw [hleft_rewrite]
  refine Finset.sum_le_sum ?_
  intro P _
  by_cases hPJ2 : P ∈ J2
  · have hPcard : P.card = 2 := (Finset.mem_filter.mp hPJ2).2.1
    have hinner :
        (∑ Q : Finset V, if Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q then W P else 0) =
          (((J3.filter fun Q => P ⊆ Q).card : ℕ) : ℝ) * W P := by
      rw [← Finset.sum_filter]
      have hfilter_eq :
          ((Finset.univ : Finset (Finset V)).filter
              (fun Q : Finset V => Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q)) =
            J3.filter fun Q => P ⊆ Q := by
        ext Q
        simp [hPcard]
      rw [hfilter_eq]
      simp [mul_comm]
    rw [hinner, if_pos hPJ2]
    have hcount_real : (((J3.filter fun Q => P ⊆ Q).card : ℕ) : ℝ) ≤
        ((Delta - (C P).card : ℕ) : ℝ) := by
      exact_mod_cast hcount_le P hPJ2
    exact mul_le_mul_of_nonneg_right hcount_real (hW P hPJ2)
  · have hinner_zero :
        (∑ Q : Finset V, if Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q then W P else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro Q _
      by_cases hcond : Q ∈ J3 ∧ P.card = 2 ∧ P ⊆ Q
      · have hPmem : P ∈ J2 := hpair_of_triple P Q hcond.1 hcond.2.1 hcond.2.2
        exact (hPJ2 hPmem).elim
      · simp [hcond]
    rw [hinner_zero, if_neg hPJ2]
