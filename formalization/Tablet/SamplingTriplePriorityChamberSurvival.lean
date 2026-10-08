import Tablet.SamplingTripleProductChamberIntegral

open BigOperators

-- [TABLET NODE: SamplingTriplePriorityChamberSurvival]
theorem SamplingTriplePriorityChamberSurvival
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (a b c : V)
    (hgamma_pos : 0 < gamma)
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab_ind : ¬ G.Adj a b) (hac_ind : ¬ G.Adj a c) (hbc_ind : ¬ G.Adj b c)
    (hcube :
      ν {ω |
        ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
            ν {ω | ω.1 = A} *
              ENNReal.ofReal (∏ v : V, t v)) :
    let Q : Finset V := {a, b, c}
    let n_a : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_b : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_c : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
    let n_ab : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
    let n_ac : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
    let n_bc : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
    let n_abc : ℕ :=
      (A.filter fun w : V =>
        w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
    ν {ω |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            ∀ q : V, q ∈ Q →
              ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ≤
      ν {ω | ω.1 = A} *
        ENNReal.ofReal
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^ (n_a + n_ab + n_ac + n_abc) *
                    (1 - y / gamma) ^ (n_b + n_bc) *
                      (1 - z / gamma) ^ n_c) := by
-- BODY
  classical
  let Q : Finset V := {a, b, c}
  let Sx : Finset V :=
    A.filter fun w : V => w ∉ Q ∧ G.Adj a w
  let Sy : Finset V :=
    A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w
  let Sz : Finset V :=
    A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w
  have hSxQ : Disjoint Sx Q := by
    rw [Finset.disjoint_left]
    intro w hw hQ
    exact (Finset.mem_filter.mp hw).2.1 hQ
  have hSyQ : Disjoint Sy Q := by
    rw [Finset.disjoint_left]
    intro w hw hQ
    exact (Finset.mem_filter.mp hw).2.1 hQ
  have hSzQ : Disjoint Sz Q := by
    rw [Finset.disjoint_left]
    intro w hw hQ
    exact (Finset.mem_filter.mp hw).2.1 hQ
  have hSxy : Disjoint Sx Sy := by
    rw [Finset.disjoint_left]
    intro w hwx hwy
    have hax : G.Adj a w := (Finset.mem_filter.mp hwx).2.2
    have hnax : ¬ G.Adj a w := (Finset.mem_filter.mp hwy).2.2.1
    exact hnax hax
  have hSxz : Disjoint Sx Sz := by
    rw [Finset.disjoint_left]
    intro w hwx hwz
    have hax : G.Adj a w := (Finset.mem_filter.mp hwx).2.2
    have hnax : ¬ G.Adj a w := (Finset.mem_filter.mp hwz).2.2.1
    exact hnax hax
  have hSyz : Disjoint Sy Sz := by
    rw [Finset.disjoint_left]
    intro w hwy hwz
    have hbx : G.Adj b w := (Finset.mem_filter.mp hwy).2.2.2
    have hnbx : ¬ G.Adj b w := (Finset.mem_filter.mp hwz).2.2.2.1
    exact hnbx hbx
  have hcore :=
    SamplingTripleProductChamberIntegral (gamma := gamma) (ν := ν) (A := A)
      (a := a) (b := b) (c := c) (Sx := Sx) (Sy := Sy) (Sz := Sz)
      hgamma_pos hab hac hbc
      (by simpa [Q] using hSxQ)
      (by simpa [Q] using hSyQ)
      (by simpa [Q] using hSzQ)
      hSxy hSxz hSyz hcube hlower_rect
  have hmono :
      {ω : Finset V × (V → ℝ) |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            ∀ q : V, q ∈ Q →
              ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ⊆
      {ω : Finset V × (V → ℝ) |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            (∀ w : V, w ∈ Sx → ω.2 w < ω.2 a) ∧
              (∀ w : V, w ∈ Sy → ω.2 w < ω.2 b) ∧
                ∀ w : V, w ∈ Sz → ω.2 w < ω.2 c} := by
    intro ω hω
    rcases hω with ⟨hA, habc₁, habc₂, hsurv⟩
    refine ⟨hA, habc₁, habc₂, ?_, ?_, ?_⟩
    · intro w hw
      have hwA : w ∈ A := (Finset.mem_filter.mp hw).1
      have haw : G.Adj a w := (Finset.mem_filter.mp hw).2.2
      exact hsurv a (by simp [Q]) w hwA haw
    · intro w hw
      have hwA : w ∈ A := (Finset.mem_filter.mp hw).1
      have hbw : G.Adj b w := (Finset.mem_filter.mp hw).2.2.2
      exact hsurv b (by simp [Q]) w hwA hbw
    · intro w hw
      have hwA : w ∈ A := (Finset.mem_filter.mp hw).1
      have hcw : G.Adj c w := (Finset.mem_filter.mp hw).2.2.2.2
      exact hsurv c (by simp [Q]) w hwA hcw
  have hmeasure :
      ν {ω : Finset V × (V → ℝ) |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            ∀ q : V, q ∈ Q →
              ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ≤
      ν {ω : Finset V × (V → ℝ) |
        ω.1 = A ∧
          ω.2 a ≤ ω.2 b ∧ ω.2 b ≤ ω.2 c ∧
            (∀ w : V, w ∈ Sx → ω.2 w < ω.2 a) ∧
              (∀ w : V, w ∈ Sy → ω.2 w < ω.2 b) ∧
                ∀ w : V, w ∈ Sz → ω.2 w < ω.2 c} :=
    MeasureTheory.measure_mono hmono
  have hSx_card :
      Sx.card =
        (A.filter fun w : V =>
          w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card +
        (A.filter fun w : V =>
          w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card +
        (A.filter fun w : V =>
          w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card +
        (A.filter fun w : V =>
          w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card := by
    change (A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card = _
    rw [← Finset.card_filter_add_card_filter_not (s :=
      A.filter fun w : V => w ∉ Q ∧ G.Adj a w) (p := fun w : V => G.Adj b w)]
    rw [← Finset.card_filter_add_card_filter_not (s :=
      (A.filter fun w : V => w ∉ Q ∧ G.Adj a w).filter fun w : V => ¬ G.Adj b w)
      (p := fun w : V => G.Adj c w)]
    rw [← Finset.card_filter_add_card_filter_not (s :=
      (A.filter fun w : V => w ∉ Q ∧ G.Adj a w).filter fun w : V => G.Adj b w)
      (p := fun w : V => G.Adj c w)]
    simp [Finset.filter_filter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      and_assoc]
  have hSy_card :
      Sy.card =
        (A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card +
        (A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card := by
    change (A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card = _
    rw [← Finset.card_filter_add_card_filter_not (s :=
      A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w)
      (p := fun w : V => G.Adj c w)]
    simp [Finset.filter_filter, Nat.add_comm, and_assoc]
  have hSz_card :
      Sz.card =
        (A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card := by
    simp [Sz]
  exact le_trans hmeasure (by
    simpa [Q, hSx_card, hSy_card, hSz_card] using hcore)
