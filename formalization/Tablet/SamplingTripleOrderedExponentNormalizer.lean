import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingTripleOrderedExponentNormalizer]
theorem SamplingTripleOrderedExponentNormalizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (a b c : V) :
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
    n_a + n_ab + n_ac + n_abc =
        (A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card ∧
      n_b + n_bc =
        (A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card ∧
      n_c =
        (A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card := by
-- BODY
  classical
  intro Q n_a n_b n_c n_ab n_ac n_bc n_abc
  constructor
  · let S : Finset V := A.filter fun w : V => w ∉ Q ∧ G.Adj a w
    have h_not_b :
        n_ac + n_a = (S.filter fun w : V => ¬ G.Adj b w).card := by
      have hraw :=
        (Finset.card_filter_add_card_filter_not
          (s := S.filter fun w : V => ¬ G.Adj b w)
          (p := fun w : V => G.Adj c w))
      have hleft :
          ((S.filter fun w : V => ¬ G.Adj b w).filter
              (fun w : V => G.Adj c w)).card = n_ac := by
        change ((S.filter fun w : V => ¬ G.Adj b w).filter
              (fun w : V => G.Adj c w)).card =
            (A.filter fun w : V =>
              w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      have hright :
          ((S.filter fun w : V => ¬ G.Adj b w).filter
              (fun w : V => ¬ G.Adj c w)).card = n_a := by
        change ((S.filter fun w : V => ¬ G.Adj b w).filter
              (fun w : V => ¬ G.Adj c w)).card =
            (A.filter fun w : V =>
              w ∉ Q ∧ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      omega
    have h_b :
        n_abc + n_ab = (S.filter fun w : V => G.Adj b w).card := by
      have hraw :=
        (Finset.card_filter_add_card_filter_not
          (s := S.filter fun w : V => G.Adj b w)
          (p := fun w : V => G.Adj c w))
      have hleft :
          ((S.filter fun w : V => G.Adj b w).filter
              (fun w : V => G.Adj c w)).card = n_abc := by
        change ((S.filter fun w : V => G.Adj b w).filter
              (fun w : V => G.Adj c w)).card =
            (A.filter fun w : V =>
              w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      have hright :
          ((S.filter fun w : V => G.Adj b w).filter
              (fun w : V => ¬ G.Adj c w)).card = n_ab := by
        change ((S.filter fun w : V => G.Adj b w).filter
              (fun w : V => ¬ G.Adj c w)).card =
            (A.filter fun w : V =>
              w ∉ Q ∧ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      omega
    have h_split :
        (S.filter fun w : V => G.Adj b w).card +
          (S.filter fun w : V => ¬ G.Adj b w).card = S.card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := S) (p := fun w : V => G.Adj b w))
    have hS :
        S.card = (A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card := rfl
    omega
  constructor
  · let S : Finset V :=
      A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w
    have hsplit :
        n_bc + n_b = S.card := by
      have hraw :=
        (Finset.card_filter_add_card_filter_not
          (s := S) (p := fun w : V => G.Adj c w))
      have hleft :
          (S.filter fun w : V => G.Adj c w).card = n_bc := by
        change (S.filter fun w : V => G.Adj c w).card =
          (A.filter fun w : V =>
            w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      have hright :
          (S.filter fun w : V => ¬ G.Adj c w).card = n_b := by
        change (S.filter fun w : V => ¬ G.Adj c w).card =
          (A.filter fun w : V =>
            w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w ∧ ¬ G.Adj c w).card
        congr 1
        ext w
        simp [S]
        tauto
      omega
    have hS :
        S.card =
          (A.filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card := rfl
    omega
  · rfl
