import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingOneVertexActivationDecisionProduct]
theorem SamplingOneVertexActivationDecisionProduct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q a : ℝ) (v : V) :
    (∑ b : V → Bool,
      ∏ u : V,
        if b u then
          if u = v then p else if G.Adj v u then p * a else p
        else
          if u = v then 0 else q) =
      p * ∏ u : V, if u = v then 1 else if G.Adj v u then q + p * a else q + p := by
-- BODY
  classical
  change
    (∑ b : V → Bool,
      ∏ u : V,
        (fun u (c : Bool) =>
          if c then
            if u = v then p else if G.Adj v u then p * a else p
          else
            if u = v then 0 else q) u (b u)) =
      p * ∏ u : V, if u = v then 1 else if G.Adj v u then q + p * a else q + p
  rw [← Fintype.prod_sum (fun u (c : Bool) =>
    if c then
      if u = v then p else if G.Adj v u then p * a else p
    else
      if u = v then 0 else q)]
  simp
  have hfactor :
      (∏ x : V, ((if x = v then p else if G.Adj v x then p * a else p) +
          if x = v then 0 else q)) =
        (∏ x : V, if x = v then p else if G.Adj v x then p * a + q else p + q) := by
    apply Finset.prod_congr rfl
    intro x _hx
    by_cases hx : x = v
    · simp [hx]
    · by_cases hAdj : G.Adj v x
      · simp [hx, hAdj]
      · simp [hx, hAdj]
  rw [hfactor]
  let f : V → ℝ := fun u => if u = v then p else if G.Adj v u then p * a + q else p + q
  let g : V → ℝ := fun u => if u = v then 1 else if G.Adj v u then q + p * a else q + p
  have hsplit :
      (∏ x : V, f x) = p * ∏ x ∈ (Finset.univ : Finset V) \ {v}, f x := by
    rw [Finset.prod_eq_mul_prod_diff_singleton (s := (Finset.univ : Finset V)) v f
      (by simp [f])]
    simp [f]
  have hdiff :
      (∏ x ∈ (Finset.univ : Finset V) \ {v}, f x) =
        ∏ x ∈ (Finset.univ : Finset V) \ {v}, g x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := by
      simpa using (Finset.mem_sdiff.mp hx).2
    by_cases hAdj : G.Adj v x
    · simp [f, g, hxv, hAdj, add_comm]
    · simp [f, g, hxv, hAdj, add_comm]
  have huniv :
      (∏ x : V, g x) = ∏ x ∈ (Finset.univ : Finset V) \ {v}, g x := by
    rw [Finset.prod_eq_mul_prod_diff_singleton (s := (Finset.univ : Finset V)) v g
      (by simp [g])]
    simp [g]
  rw [hsplit, hdiff, ← huniv]
