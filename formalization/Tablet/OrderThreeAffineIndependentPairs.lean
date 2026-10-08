import Tablet.OrderThreeAffineGeometry
import Tablet.IndependentPairCount

-- [TABLET NODE: OrderThreeAffineIndependentPairs]
theorem OrderThreeAffineIndependentPairs (q : ℕ) :
    @IndependentPairCount _ _ _
      (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q))
      (Classical.decRel (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)).Adj)
      none = 9 * q ^ 2 := by
-- BODY
  classical
  let J := {ab : ZMod 3 × ZMod 3 // ab.1.val < ab.2.val}
  let E := Option (ZMod 3 × ZMod 3 × Fin q)
  let G := LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)
  let F : (ZMod 3 × J × Fin q × Fin q) → Finset E := fun t =>
    {some (t.1, t.2.1.val.1, t.2.2.1), some (t.1, t.2.1.val.2, t.2.2.2)}
  have hgeom := OrderThreeAffineGeometry q
  have hnonadj (m a n b : ZMod 3) (i j : Fin q)
      (hne : (some (m, a, i) : E) ≠ some (n, b, j)) :
      ¬ G.Adj (some (m, a, i)) (some (n, b, j)) ↔ m = n ∧ a ≠ b := by
    rw [← hgeom.2.2.2 m a n b i j]
    simp only [G, LineGraphOfHypergraph, ne_eq, not_and, hne, not_false_eq_true,
      true_implies]
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.not_nonempty_iff_eq_empty]
  have hmem (t : ZMod 3 × J × Fin q × Fin q) :
      (F t).card = 2 ∧ F t ⊆ G.neighborFinset none ∧
        ∀ ⦃x⦄, x ∈ F t → ∀ ⦃y⦄, y ∈ F t → x ≠ y → ¬ G.Adj x y := by
    rcases t with ⟨m, ⟨⟨a, b⟩, hab⟩, i, j⟩
    have hab' : a ≠ b := by intro h; subst b; exact (lt_irrefl _ hab)
    have hne : (some (m, a, i) : E) ≠ some (m, b, j) := by simp [hab']
    refine ⟨by simp [F, hne], ?_, ?_⟩
    · intro x hx
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;>
        apply (G.mem_neighborFinset _ _).mpr <;>
        exact (hgeom.2.1 _).mpr (Option.some_ne_none _)
    · intro x hx y hy hxy
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact (hnonadj m a m b i j hne).2 ⟨rfl, hab'⟩
      · exact (hnonadj m b m a j i hne.symm).2 ⟨rfl, hab'.symm⟩
      · exact (hxy rfl).elim
  have hinj : Function.Injective F := by
    rintro ⟨m, ⟨⟨a, b⟩, hab⟩, i, j⟩ ⟨n, ⟨⟨c, d⟩, hcd⟩, k, l⟩ heq
    have hleft : some (m, a, i) ∈ F (n, ⟨(c, d), hcd⟩, k, l) := by
      rw [← heq]; simp [F]
    have hright : some (m, b, j) ∈ F (n, ⟨(c, d), hcd⟩, k, l) := by
      rw [← heq]; simp [F]
    simp only [F, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq,
      Prod.mk.injEq] at hleft hright
    rcases hleft with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hright with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
    · exact (lt_irrefl _ hab).elim
    · rfl
    · exact (Nat.lt_asymm hab hcd).elim
    · exact (lt_irrefl _ hab).elim
  have himage : (Finset.univ.image F) =
      ((Finset.univ : Finset (Finset E)).filter (fun S =>
        S.card = 2 ∧ S ⊆ G.neighborFinset none ∧
          ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; exact hmem t
    · rintro ⟨hcard, hsub, hind⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      have hx := hsub (Finset.mem_insert_self x {y})
      have hy := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      have hx' : x ≠ none := (hgeom.2.1 x).mp ((G.mem_neighborFinset _ _).mp hx)
      have hy' : y ≠ none := (hgeom.2.1 y).mp ((G.mem_neighborFinset _ _).mp hy)
      obtain ⟨⟨m, a, i⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hx'
      obtain ⟨⟨n, b, j⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hy'
      have hab := (hnonadj m a n b i j hxy).mp
        (hind (by simp) (by simp) hxy)
      obtain ⟨rfl, hab⟩ := hab
      have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective 3 h)
      rcases lt_or_gt_of_ne hv with h | h
      · exact ⟨(m, ⟨(a, b), h⟩, i, j), rfl⟩
      · exact ⟨(m, ⟨(b, a), h⟩, j, i), Finset.pair_comm _ _⟩
  have hJ : Fintype.card J = 3 := by decide
  have hcount : IndependentPairCount G none = (Finset.univ.image F).card := by
    unfold IndependentPairCount
    congr 1
    ext S
    rw [himage]
    simp
  rw [hcount, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, hJ, ZMod.card, Fintype.card_fin]
  ring
