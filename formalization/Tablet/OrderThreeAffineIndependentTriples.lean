import Tablet.OrderThreeAffineGeometry
import Tablet.IndependentTripleCount

-- [TABLET NODE: OrderThreeAffineIndependentTriples]
theorem OrderThreeAffineIndependentTriples (q : ℕ) :
    @IndependentTripleCount _ _ _
      (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q))
      (Classical.decRel (LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)).Adj)
      none = 3 * q ^ 3 := by
-- BODY
  classical
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  let E := Option (ZMod 3 × ZMod 3 × Fin q)
  let G := LineGraphOfHypergraph (OrderThreeAffineMultihypergraph q)
  let F : (ZMod 3 × Fin q × Fin q × Fin q) → Finset E := fun t =>
    {some (t.1, 0, t.2.1), some (t.1, 1, t.2.2.1), some (t.1, 2, t.2.2.2)}
  have hgeom := OrderThreeAffineGeometry q
  have hnonadj (m a n b : ZMod 3) (i j : Fin q)
      (hne : (some (m, a, i) : E) ≠ some (n, b, j)) :
      ¬ G.Adj (some (m, a, i)) (some (n, b, j)) ↔ m = n ∧ a ≠ b := by
    rw [← hgeom.2.2.2 m a n b i j]
    simp only [G, LineGraphOfHypergraph, ne_eq, not_and, hne, not_false_eq_true,
      true_implies]
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.not_nonempty_iff_eq_empty]
  have hmem (t : ZMod 3 × Fin q × Fin q × Fin q) :
      (F t).card = 3 ∧ F t ⊆ G.neighborFinset none ∧
        ∀ ⦃x⦄, x ∈ F t → ∀ ⦃y⦄, y ∈ F t → x ≠ y → ¬ G.Adj x y := by
    rcases t with ⟨m, i, j, k⟩
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.card_eq_three.mpr
      exact ⟨some (m, 0, i), some (m, 1, j), some (m, 2, k),
        fun h => zero_ne_one (congrArg (fun t => t.2.1) (Option.some.inj h)),
        fun h => h02 (congrArg (fun t => t.2.1) (Option.some.inj h)),
        fun h => h12 (congrArg (fun t => t.2.1) (Option.some.inj h)), rfl⟩
    · intro x hx
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;>
        apply (G.mem_neighborFinset _ _).mpr <;>
        exact (hgeom.2.1 _).mpr (Option.some_ne_none _)
    · intro x hx y hy hxy
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact (hxy rfl).elim
        | apply (hnonadj _ _ _ _ _ _ hxy).2; simp [h02, h12, h02.symm, h12.symm]
  have hinj : Function.Injective F := by
    rintro ⟨m, i, j, k⟩ ⟨n, l, u, v⟩ heq
    have h0 : some (m, 0, i) ∈ F (n, l, u, v) := by
      rw [← heq]; simp [F]
    have h1 : some (m, 1, j) ∈ F (n, l, u, v) := by
      rw [← heq]; simp [F]
    have h2 : some (m, 2, k) ∈ F (n, l, u, v) := by
      rw [← heq]; simp [F]
    simp [F, h02, h12, h02.symm, h12.symm] at h0 h1 h2
    rcases h0 with ⟨rfl, rfl⟩
    rcases h1 with ⟨_, rfl⟩
    rcases h2 with ⟨_, rfl⟩
    rfl
  have himage : (Finset.univ.image F) =
      ((Finset.univ : Finset (Finset E)).filter (fun S =>
        S.card = 3 ∧ S ⊆ G.neighborFinset none ∧
          ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; exact hmem t
    · rintro ⟨hcard, hsub, hind⟩
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
      have hn (e : E) (he : e ∈ ({x, y, z} : Finset E)) : e ≠ none :=
        (hgeom.2.1 e).mp ((G.mem_neighborFinset _ _).mp (hsub he))
      obtain ⟨⟨m, a, i⟩, rfl⟩ := Option.ne_none_iff_exists'.mp (hn x (by simp))
      obtain ⟨⟨n, b, j⟩, rfl⟩ := Option.ne_none_iff_exists'.mp (hn y (by simp))
      obtain ⟨⟨o, c, k⟩, rfl⟩ := Option.ne_none_iff_exists'.mp (hn z (by simp))
      obtain ⟨rfl, hab⟩ := (hnonadj m a n b i j hxy).mp
        (hind (by simp) (by simp) hxy)
      obtain ⟨rfl, hac⟩ := (hnonadj m a o c i k hxz).mp
        (hind (by simp) (by simp) hxz)
      have hbc := ((hnonadj m b m c j k hyz).mp
        (hind (by simp) (by simp) hyz)).2
      clear hgeom hnonadj hmem hinj hcard hsub hind hn hxy hxz hyz h02 h12
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp_all only [ne_eq, not_true_eq_false]
      · refine ⟨(m, i, j, k), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨(m, i, k, j), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨(m, j, i, k), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨(m, k, i, j), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨(m, j, k, i), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨(m, k, j, i), ?_⟩
        ext e
        simp only [F, Finset.mem_insert, Finset.mem_singleton]
        tauto
  have hcount : IndependentTripleCount G none = (Finset.univ.image F).card := by
    unfold IndependentTripleCount
    congr 1
    ext S
    rw [himage]
    simp
  rw [hcount, Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring
