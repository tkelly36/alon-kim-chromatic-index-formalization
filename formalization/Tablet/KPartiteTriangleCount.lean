import Tablet.Preamble
import Tablet.KPartiteTriangleDistinctParts
import Tablet.KPartiteFixedThreePartProductEstimate
import Tablet.KPartiteEdgeCountByPartPairs
import Tablet.KPartiteTriangleFibreBridge
import Tablet.KPartiteTrianglePartTripleProductSumBound
import Tablet.KPartiteWeightedTriangleInequality

-- [TABLET NODE: KPartiteTriangleCount]
theorem KPartiteTriangleCount :
    ∀ k : ℕ, 0 < k →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
          (∃ part : V → Fin k, ∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
          (((Finset.univ : Finset (Finset V)).filter
              (fun s =>
                s.card = 3 ∧
                  ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)).card : ℝ)
            ≤ (Nat.choose k 3 : ℝ) *
              (((G.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
-- BODY
  intro k hk V _ _ G _ hpartite
  classical
  rcases hpartite with ⟨part, hpart⟩
  have triangle_distinct_parts :
      ∀ s : Finset V,
        s.card = 3 →
        (∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v) →
        (s.image part).card = 3 := by
    intro s hs hclique
    exact KPartiteTriangleDistinctParts k hk G part hpart s hs hclique
  have fixed_three_part_product :
      ∀ A B C : Finset V,
        (((A.product (B.product C)).filter
            (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)).card : ℝ)
          ≤ Real.sqrt
            ((((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
              (((A.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
              (((B.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ)) := by
    intro A B C
    exact KPartiteFixedThreePartProductEstimate G A B C
  have edge_count_by_part_pairs :
      G.edgeFinset.card =
        ((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun p => p.1 < p.2)).sum
          (fun p =>
            ((Finset.univ : Finset (V × V)).filter
              (fun q =>
                    G.Adj q.1 q.2 ∧ part q.1 = p.1 ∧ part q.2 = p.2)).card) := by
    exact KPartiteEdgeCountByPartPairs k hk G part hpart
  have triangle_fibre_bridge :
      ((Finset.univ : Finset (Finset V)).filter
        (fun s =>
          s.card = 3 ∧
            ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)).card
        ≤
      let triples : Finset (Fin k × Fin k × Fin k) :=
        (Finset.univ.filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      let A : Fin k → Finset V := fun i =>
        (Finset.univ.filter (fun v => part v = i))
      let triCount : Fin k × Fin k × Fin k → ℕ := fun t =>
        (((A t.1).product ((A t.2.1).product (A t.2.2))).filter
          (fun x =>
            G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2)).card
      triples.sum triCount := by
    exact KPartiteTriangleFibreBridge k hk G part hpart
  have part_triple_product_sum_bound :
      let triples : Finset (Fin k × Fin k × Fin k) :=
        (Finset.univ.filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      let A : Fin k → Finset V := fun i =>
        (Finset.univ.filter (fun v => part v = i))
      let triCount : Fin k × Fin k × Fin k → ℝ := fun t =>
        ((((A t.1).product ((A t.2.1).product (A t.2.2))).filter
          (fun x =>
            G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2)).card : ℝ)
      let m : Fin k → Fin k → ℝ := fun i j =>
        (((Finset.univ : Finset (V × V)).filter
          (fun q => G.Adj q.1 q.2 ∧ part q.1 = i ∧ part q.2 = j)).card : ℝ)
      triples.sum triCount ≤
      triples.sum (fun t => Real.sqrt (m t.1 t.2.1 * m t.1 t.2.2 * m t.2.1 t.2.2)) := by
    exact KPartiteTrianglePartTripleProductSumBound k G part
  let T : Finset (Finset V) :=
    (Finset.univ.filter
      (fun s =>
        s.card = 3 ∧
          ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v))
  let triples : Finset (Fin k × Fin k × Fin k) :=
    (Finset.univ.filter (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
  let A : Fin k → Finset V := fun i =>
    (Finset.univ.filter (fun v => part v = i))
  let triCount : Fin k × Fin k × Fin k → ℝ := fun t =>
    ((((A t.1).product ((A t.2.1).product (A t.2.2))).filter
      (fun x =>
        G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2)).card : ℝ)
  let m : Fin k → Fin k → ℝ := fun i j =>
    (((Finset.univ : Finset (V × V)).filter
      (fun q => G.Adj q.1 q.2 ∧ part q.1 = i ∧ part q.2 = j)).card : ℝ)
  have hbridge_real : (T.card : ℝ) ≤ triples.sum triCount := by
    dsimp [T, triples, A, triCount]
    exact_mod_cast triangle_fibre_bridge
  have hprod_sum :
      triples.sum triCount ≤
        triples.sum (fun t => Real.sqrt (m t.1 t.2.1 * m t.1 t.2.2 * m t.2.1 t.2.2)) := by
    simpa [triples, A, triCount, m] using part_triple_product_sum_bound
  by_cases hk3 : 3 ≤ k
  · have hm_nonneg : ∀ i j : Fin k, 0 ≤ m i j := by
      intro i j
      dsimp [m]
      positivity
    have hweighted :
        triples.sum (fun t => Real.sqrt (m t.1 t.2.1 * m t.1 t.2.2 * m t.2.1 t.2.2))
          ≤ (Nat.choose k 3 : ℝ) *
              (((((Finset.univ : Finset (Fin k × Fin k)).filter
                    (fun p => p.1 < p.2)).sum
                    (fun p => m p.1 p.2)) /
              (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
      simpa [triples] using KPartiteWeightedTriangleInequality k hk3 m hm_nonneg
    have hpair_sum :
        (((Finset.univ : Finset (Fin k × Fin k)).filter
            (fun p => p.1 < p.2)).sum
            (fun p => m p.1 p.2)) = (G.edgeFinset.card : ℝ) := by
      dsimp [m]
      rw [← Nat.cast_sum]
      exact_mod_cast edge_count_by_part_pairs.symm
    calc
      (T.card : ℝ) ≤ triples.sum triCount := hbridge_real
      _ ≤ triples.sum
            (fun t => Real.sqrt (m t.1 t.2.1 * m t.1 t.2.2 * m t.2.1 t.2.2)) := hprod_sum
      _ ≤ (Nat.choose k 3 : ℝ) *
              (((((Finset.univ : Finset (Fin k × Fin k)).filter
                    (fun p => p.1 < p.2)).sum
                    (fun p => m p.1 p.2)) /
              (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := hweighted
      _ = (Nat.choose k 3 : ℝ) *
              (((G.edgeFinset.card : ℝ) / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
            rw [hpair_sum]
  · have hno_triples : triples = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro t ht
      have htlt : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
        simpa [triples] using ht
      have hijval : (t.1 : ℕ) < (t.2.1 : ℕ) := by
        exact_mod_cast htlt.1
      have hjlval : (t.2.1 : ℕ) < (t.2.2 : ℕ) := by
        exact_mod_cast htlt.2
      have hchain : 2 ≤ (t.2.2 : ℕ) := by
        omega
      have hk_ge : 3 ≤ k := by
        omega
      exact hk3 hk_ge
    have hT_zero : T.card = 0 := by
      have hnat : T.card ≤ 0 := by
        simpa [T, triples, hno_triples] using triangle_fibre_bridge
      exact Nat.eq_zero_of_le_zero hnat
    have hchoose3_zero : (Nat.choose k 3 : ℝ) = 0 := by
      have hklt : k < 3 := lt_of_not_ge hk3
      simp [Nat.choose_eq_zero_of_lt hklt]
    simp [T, hT_zero, hchoose3_zero]
