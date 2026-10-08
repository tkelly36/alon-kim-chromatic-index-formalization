import Tablet.Preamble
import Mathlib.Data.Nat.Choose.Cast

open BigOperators

-- [TABLET NODE: SamplingIndependentPairsHalfDegreeSquare]
theorem SamplingIndependentPairsHalfDegreeSquare {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Delta : ℕ) (r : V) (X : Finset V)
    (hregular : ∀ v : V, G.degree v = Delta)
    (hX : ∀ x : V, x ∈ X → G.Adj r x) :
    let J2 : Finset (Finset V) :=
      (Finset.univ.filter fun P : Finset V =>
        P.card = 2 ∧ P ⊆ X ∧
          ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ G.Adj a b)
    (J2.card : ℝ) ≤ (Delta : ℝ)^2 / 2 := by
-- BODY
  classical
  intro J2
  have hJ2_sub : J2 ⊆ X.powersetCard 2 := by
    intro P hP
    have hp := Finset.mem_filter.mp hP
    exact Finset.mem_powersetCard.mpr ⟨hp.2.2.1, hp.2.1⟩
  have hcard_le_choose : J2.card ≤ Nat.choose X.card 2 := by
    calc
      J2.card ≤ (X.powersetCard 2).card := Finset.card_le_card hJ2_sub
      _ = Nat.choose X.card 2 := Finset.card_powersetCard ..
  have hX_sub : X ⊆ G.neighborFinset r := by
    intro x hx
    simpa [SimpleGraph.mem_neighborFinset] using hX x hx
  have hX_card_le : X.card ≤ Delta := by
    calc
      X.card ≤ (G.neighborFinset r).card := Finset.card_le_card hX_sub
      _ = G.degree r := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ = Delta := hregular r
  have hJ2_real : (J2.card : ℝ) ≤ (Nat.choose X.card 2 : ℝ) := by
    exact_mod_cast hcard_le_choose
  have hchoose_eq :
      (Nat.choose X.card 2 : ℝ) = (X.card : ℝ) * ((X.card : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℝ) X.card)
  have hX_le_real : (X.card : ℝ) ≤ (Delta : ℝ) := by
    exact_mod_cast hX_card_le
  have hX_nonneg : 0 ≤ (X.card : ℝ) := by
    positivity
  nlinarith
