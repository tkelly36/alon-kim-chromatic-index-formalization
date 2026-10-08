import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: FiniteBipartiteIntersectionEdgeCount]
theorem FiniteBipartiteIntersectionEdgeCount
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (edge : E → Finset V) (A B : Finset E) (X : Finset V)
    (hX : ∀ a ∈ A, ∀ b ∈ B, edge a ∩ edge b ⊆ X) :
    (((A ×ˢ B).filter (fun p => (edge p.1 ∩ edge p.2).Nonempty)).card : ℤ) =
      (∑ x ∈ X, ((A.filter (fun a => x ∈ edge a)).card : ℤ) *
        ((B.filter (fun b => x ∈ edge b)).card : ℤ)) -
      ∑ a ∈ A, ∑ b ∈ B, max (0 : ℤ) (((edge a ∩ edge b).card : ℤ) - 1) := by
-- BODY
  classical
  have hdouble : (∑ x ∈ X, ((A.filter (fun a => x ∈ edge a)).card : ℤ) *
      ((B.filter (fun b => x ∈ edge b)).card : ℤ)) =
      ∑ a ∈ A, ∑ b ∈ B, ((edge a ∩ edge b).card : ℤ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    have heq : X.filter (fun x => x ∈ edge a ∧ x ∈ edge b) = edge a ∩ edge b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => h.2, fun h => ⟨hX a ha b hb (Finset.mem_inter.mpr h), h⟩⟩
    have hind (x : V) :
        (if x ∈ edge a then (1 : ℤ) else 0) * (if x ∈ edge b then 1 else 0) =
        if x ∈ edge a ∧ x ∈ edge b then 1 else 0 := by
      split_ifs <;> simp_all
    simp_rw [hind]
    rw [← Finset.sum_filter, heq]
  have hleft : (((A ×ˢ B).filter
      (fun p => (edge p.1 ∩ edge p.2).Nonempty)).card : ℤ) =
      ∑ a ∈ A, ∑ b ∈ B, if (edge a ∩ edge b).Nonempty then (1 : ℤ) else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_product]
  rw [hleft, hdouble, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hn : (edge a ∩ edge b).Nonempty ↔ 0 < (edge a ∩ edge b).card :=
    Finset.card_pos.symm
  have hc : (0 : ℤ) ≤ ((edge a ∩ edge b).card : ℤ) := Int.natCast_nonneg _
  split_ifs with h
  · have hp : (0 : ℤ) < ((edge a ∩ edge b).card : ℤ) := by exact_mod_cast hn.mp h
    omega
  · have hz : (edge a ∩ edge b).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [hz]
