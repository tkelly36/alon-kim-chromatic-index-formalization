import Tablet.SamplingOneVertexActivationDecisionProduct

open BigOperators

-- [TABLET NODE: SamplingOneVertexFixedThresholdProduct]
theorem SamplingOneVertexFixedThresholdProduct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma a : ℝ) (v : V)
    (hregular : ∀ v : V, G.degree v = Delta) :
    (∑ b : V → Bool,
      ∏ u : V,
        if b u then
          if u = v then gamma / (Delta : ℝ)
          else if G.Adj v u then (gamma / (Delta : ℝ)) * a
          else gamma / (Delta : ℝ)
        else
          if u = v then 0 else 1 - gamma / (Delta : ℝ)) =
      (gamma / (Delta : ℝ)) *
        (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta := by
-- BODY
  classical
  have hprod := SamplingOneVertexActivationDecisionProduct G
    (gamma / (Delta : ℝ)) (1 - gamma / (Delta : ℝ)) a v
  rw [hprod]
  congr 1
  let c : ℝ := 1 - (gamma / (Delta : ℝ)) * (1 - a)
  have hfactor :
      (∏ u : V,
        if u = v then 1
        else if G.Adj v u then (1 - gamma / (Delta : ℝ)) + (gamma / (Delta : ℝ)) * a
        else (1 - gamma / (Delta : ℝ)) + gamma / (Delta : ℝ)) =
        ∏ u : V, if G.Adj v u then c else 1 := by
    apply Finset.prod_congr rfl
    intro u _hu
    by_cases huv : u = v
    · simp [huv]
    · by_cases hadj : G.Adj v u
      · ring_nf
        simp [huv, hadj, c]
        ring
      · simp [huv, hadj]
  rw [hfactor]
  have hfilter :
      (∏ u : V, if G.Adj v u then c else 1) =
        c ^ ((Finset.univ.filter fun u : V => G.Adj v u).card) := by
    rw [← Finset.prod_filter]
    simp
  rw [hfilter]
  have hcard : ((Finset.univ.filter fun u : V => G.Adj v u).card) = Delta := by
    rw [← hregular v]
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr
    ext u
    simp [SimpleGraph.mem_neighborFinset]
  rw [hcard]
