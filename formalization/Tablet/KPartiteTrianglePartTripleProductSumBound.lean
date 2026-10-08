import Tablet.Preamble
import Tablet.KPartiteFixedThreePartProductEstimate

open scoped BigOperators

-- [TABLET NODE: KPartiteTrianglePartTripleProductSumBound]
theorem KPartiteTrianglePartTripleProductSumBound :
    ∀ k : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
          ∀ part : V → Fin k,
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
-- BODY
  intro k V _ _ G _ part
  classical
  refine Finset.sum_le_sum ?_
  intro t ht
  let A : Finset V := (Finset.univ.filter (fun v => part v = t.1))
  let B : Finset V := (Finset.univ.filter (fun v => part v = t.2.1))
  let C : Finset V := (Finset.univ.filter (fun v => part v = t.2.2))
  have hfixed := KPartiteFixedThreePartProductEstimate G A B C
  have hAB :
      ((A.product B).filter (fun p : V × V => G.Adj p.1 p.2)) =
        ((Finset.univ : Finset (V × V)).filter
          (fun q => G.Adj q.1 q.2 ∧ part q.1 = t.1 ∧ part q.2 = t.2.1)) := by
    ext q
    simp [A, B, and_assoc, and_left_comm, and_comm]
  have hAC :
      ((A.product C).filter (fun p : V × V => G.Adj p.1 p.2)) =
        ((Finset.univ : Finset (V × V)).filter
          (fun q => G.Adj q.1 q.2 ∧ part q.1 = t.1 ∧ part q.2 = t.2.2)) := by
    ext q
    simp [A, C, and_assoc, and_left_comm, and_comm]
  have hBC :
      ((B.product C).filter (fun p : V × V => G.Adj p.1 p.2)) =
        ((Finset.univ : Finset (V × V)).filter
          (fun q => G.Adj q.1 q.2 ∧ part q.1 = t.2.1 ∧ part q.2 = t.2.2)) := by
    ext q
    simp [B, C, and_assoc, and_left_comm, and_comm]
  rw [hAB, hAC, hBC] at hfixed
  simpa [A, B, C] using hfixed
