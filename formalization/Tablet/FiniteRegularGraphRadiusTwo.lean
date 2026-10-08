import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Finite

open Finset

-- [TABLET NODE: FiniteRegularGraphRadiusTwo]
theorem FiniteRegularGraphRadiusTwo {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (Delta : ℕ)
    (hreg : ∀ v, (G.neighborSet v).ncard = Delta) (hDelta : 1 ≤ Delta) :
    let R := fun v => Finset.univ.filter fun w =>
      w = v ∨ G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w
    (∀ v, (R v).card ≤ 1 + Delta^2) ∧
    (∀ v, (R v).card ≤ 2 * Delta^2) ∧
    (∀ v w, w ∈ R v ↔ v ∈ R w) := by
-- BODY
  classical
  dsimp only
  let N := fun v => G.neighborFinset v
  have hn (v) : (N v).card = Delta := by
    rw [← hreg v, Set.ncard_eq_toFinset_card']
    rfl
  have hb (v) : (Finset.univ.filter fun w =>
      w = v ∨ G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w).card ≤
        1 + Delta^2 := by
    have hs : (Finset.univ.filter fun w =>
        w = v ∨ G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w) ⊆
        {v} ∪ N v ∪ (N v).biUnion (fun u => (N u).erase v) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      rcases hw with rfl | hw | ⟨u, hu, huw⟩
      · simp
      · simp [N, hw]
      · by_cases hwv : w = v
        · simp [hwv]
        · apply mem_union_right
          exact mem_biUnion.mpr ⟨u, by simpa [N] using hu,
            mem_erase.mpr ⟨hwv, by simpa [N] using huw⟩⟩
    have he : ((N v).biUnion (fun u => (N u).erase v)).card ≤
        Delta * (Delta - 1) := by
      calc
        _ ≤ ∑ u ∈ N v, ((N u).erase v).card := card_biUnion_le
        _ = Delta * (Delta - 1) := by
          have hc : ∀ u ∈ N v, ((N u).erase v).card = Delta - 1 := by
            intro u hu
            rw [card_erase_of_mem, hn]
            simpa [N] using (G.mem_neighborFinset v u).mp hu |>.symm
          rw [sum_congr rfl hc, sum_const, hn, smul_eq_mul]
    have hd : Delta * (Delta - 1) + Delta = Delta^2 := by
      have := Nat.sub_add_cancel hDelta
      nlinarith
    calc
      _ ≤ ({v} ∪ N v ∪ (N v).biUnion (fun u => (N u).erase v)).card := card_le_card hs
      _ ≤ ({v} ∪ N v).card + ((N v).biUnion (fun u => (N u).erase v)).card := card_union_le _ _
      _ ≤ ({v} : Finset W).card + (N v).card + Delta * (Delta - 1) :=
        Nat.add_le_add (card_union_le _ _) he
      _ = 1 + Delta^2 := by rw [card_singleton, hn]; omega
  refine ⟨hb, fun v => (hb v).trans ?_, ?_⟩
  · have : 1 ≤ Delta^2 := by nlinarith
    omega
  · intro v w
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> rintro (h | h | ⟨u, h, h'⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr ⟨u, h'.symm, h.symm⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr ⟨u, h'.symm, h.symm⟩)
