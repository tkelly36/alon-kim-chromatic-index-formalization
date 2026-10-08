import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators

-- [TABLET NODE: KPartiteEdgeCountByPartPairs]
theorem KPartiteEdgeCountByPartPairs :
    ∀ k : ℕ, 0 < k →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
          ∀ part : V → Fin k,
            (∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
            G.edgeFinset.card =
              ((Finset.univ : Finset (Fin k × Fin k)).filter
                (fun p => p.1 < p.2)).sum
                (fun p =>
                  ((Finset.univ : Finset (V × V)).filter
                    (fun q =>
                      G.Adj q.1 q.2 ∧ part q.1 = p.1 ∧ part q.2 = p.2)).card) := by
-- BODY
  classical
  intro k _hk V _ _ G _ part hpart
  let darts : Finset (V × V) :=
    (Finset.univ.filter (fun q : V × V => G.Adj q.1 q.2))
  let f : Fin k × Fin k → ℕ := fun p =>
    ((Finset.univ : Finset (V × V)).filter
      (fun q => G.Adj q.1 q.2 ∧ part q.1 = p.1 ∧ part q.2 = p.2)).card
  have hdarts_card : darts.card = ∑ p : Fin k × Fin k, f p := by
    have hmap : ∀ q ∈ darts, (part q.1, part q.2) ∈
        (Finset.univ : Finset (Fin k × Fin k)) := by
      intro q hq
      simp
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    dsimp [darts, f]
    refine Finset.sum_congr rfl ?_
    intro p hp
    congr 1
    ext q
    simp [Prod.ext_iff]
  have htwo : 2 * G.edgeFinset.card = darts.card := by
    simpa [darts] using (SimpleGraph.two_mul_card_edgeFinset (G := G))
  have f_diag_zero : ∀ i : Fin k, f (i, i) = 0 := by
    intro i
    dsimp [f]
    apply Finset.card_eq_zero.mpr
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp
    intro hadj h1 h2
    exact hpart hadj (h1.trans h2.symm)
  have f_swap : ∀ i j : Fin k, f (i, j) = f (j, i) := by
    intro i j
    dsimp [f]
    let S : Finset (V × V) := (Finset.univ.filter
      (fun q : V × V => G.Adj q.1 q.2 ∧ part q.1 = i ∧ part q.2 = j))
    let T : Finset (V × V) := (Finset.univ.filter
      (fun q : V × V => G.Adj q.1 q.2 ∧ part q.1 = j ∧ part q.2 = i))
    change S.card = T.card
    refine Finset.card_bij' (fun q _ => (q.2, q.1)) (fun q _ => (q.2, q.1)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨G.symm hq.1, hq.2.2, hq.2.1⟩
    · intro q hq
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨G.symm hq.1, hq.2.2, hq.2.1⟩
    · intro q hq
      rfl
    · intro q hq
      rfl
  have hsum_all :
      (∑ p : Fin k × Fin k, f p) =
        2 * (((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun p => p.1 < p.2)).sum f) := by
    let ltPairs : Finset (Fin k × Fin k) := (Finset.univ.filter
      (fun p : Fin k × Fin k => p.1 < p.2))
    let gtPairs : Finset (Fin k × Fin k) := (Finset.univ.filter
      (fun p : Fin k × Fin k => p.2 < p.1))
    let eqPairs : Finset (Fin k × Fin k) := (Finset.univ.filter
      (fun p : Fin k × Fin k => p.1 = p.2))
    have hpartition : (Finset.univ : Finset (Fin k × Fin k)) =
        ltPairs ∪ gtPairs ∪ eqPairs := by
      ext p
      dsimp [ltPairs, gtPairs, eqPairs]
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      constructor
      · intro _
        rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
        · exact Or.inl (Or.inl hlt)
        · exact Or.inr heq
        · exact Or.inl (Or.inr hgt)
      · intro _
        trivial
    have hdis_l_g : Disjoint ltPairs gtPairs := by
      rw [Finset.disjoint_left]
      intro p hp hq
      dsimp [ltPairs, gtPairs] at hp hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact (not_lt_of_gt hp) hq
    have hdis_lg_e : Disjoint (ltPairs ∪ gtPairs) eqPairs := by
      rw [Finset.disjoint_left]
      intro p hp hq
      dsimp [ltPairs, gtPairs, eqPairs] at hp hq
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      rcases hp with hp | hp
      · exact (ne_of_lt hp) hq
      · exact (ne_of_gt hp) hq
    have h_eq_sum_zero : eqPairs.sum f = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      dsimp [eqPairs] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      cases p with
      | mk a b =>
        simp only at hp
        subst b
        exact f_diag_zero a
    have h_gt_eq_lt : gtPairs.sum f = ltPairs.sum f := by
      refine Finset.sum_bij (fun p hp => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        dsimp [gtPairs, ltPairs] at hp ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro p1 hp1 p2 hp2 h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        refine ⟨(q.2, q.1), ?_, rfl⟩
        dsimp [gtPairs, ltPairs] at hq ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        exact hq
      · intro p hp
        exact f_swap p.1 p.2
    calc
      (∑ p : Fin k × Fin k, f p) = (ltPairs ∪ gtPairs ∪ eqPairs).sum f := by
        rw [← hpartition]
      _ = (ltPairs.sum f + gtPairs.sum f) + eqPairs.sum f := by
        rw [Finset.sum_union hdis_lg_e, Finset.sum_union hdis_l_g]
      _ = (ltPairs.sum f + ltPairs.sum f) + 0 := by
        rw [h_gt_eq_lt, h_eq_sum_zero]
      _ = 2 * ltPairs.sum f := by
        omega
  have htwo_eq :
      2 * G.edgeFinset.card =
        2 * (((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun p => p.1 < p.2)).sum f) := by
    rw [htwo, hdarts_card, hsum_all]
  exact Nat.mul_left_cancel (by omega : 0 < 2) htwo_eq
