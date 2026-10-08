import Tablet.SamplingOneVertexFixedThresholdProduct

open BigOperators

-- [TABLET NODE: SamplingOneVertexActivationIntegralSum]
theorem SamplingOneVertexActivationIntegralSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ) (v : V)
    (hregular : ∀ v : V, G.degree v = Delta) :
    (∑ A : Finset V,
      if v ∈ A then
        ((gamma / (Delta : ℝ)) ^ A.card *
          (1 - gamma / (Delta : ℝ)) ^
            ((Finset.univ : Finset V).card - A.card)) *
          (∫ a in (0 : ℝ)..1,
            a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
      else 0) =
      (gamma / (Delta : ℝ)) *
        (∫ a in (0 : ℝ)..1,
          (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta) := by
-- BODY
  classical
  let F : Finset V → ℝ → ℝ := fun A a =>
    if v ∈ A then
      (gamma / (Delta : ℝ)) ^ A.card *
        (1 - gamma / (Delta : ℝ)) ^
          ((Finset.univ : Finset V).card - A.card) *
        a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)
    else 0
  have hterm :
      (∑ A : Finset V,
        if v ∈ A then
          ((gamma / (Delta : ℝ)) ^ A.card *
            (1 - gamma / (Delta : ℝ)) ^
              ((Finset.univ : Finset V).card - A.card)) *
            (∫ a in (0 : ℝ)..1,
              a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
        else 0) =
        ∑ A : Finset V, ∫ a in (0 : ℝ)..1, F A a := by
    apply Finset.sum_congr rfl
    intro A _hA
    by_cases hv : v ∈ A
    · simp [F, hv, intervalIntegral.integral_const_mul, mul_assoc]
    · simp [F, hv]
  have hsum_integral :
      (∑ A : Finset V, ∫ a in (0 : ℝ)..1, F A a) =
        ∫ a in (0 : ℝ)..1, ∑ A : Finset V, F A a := by
    rw [intervalIntegral.integral_finset_sum]
    intro A _hA
    dsimp [F]
    by_cases hv : v ∈ A
    · apply Continuous.intervalIntegrable
      continuity
    · simp [hv]
  have hpointwise (a : ℝ) :
      (∑ A : Finset V, F A a) =
        (gamma / (Delta : ℝ)) *
          (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta := by
    dsimp [F]
    let e : Finset V ≃ (V → Bool) := {
      toFun A := fun u => decide (u ∈ A)
      invFun b := Finset.univ.filter fun u : V => b u
      left_inv := by
        intro A
        ext u
        simp
      right_inv := by
        intro b
        funext u
        simp
    }
    have hsum_bool :
        (∑ A : Finset V,
          if v ∈ A then
            (gamma / (Delta : ℝ)) ^ A.card *
              (1 - gamma / (Delta : ℝ)) ^
                ((Finset.univ : Finset V).card - A.card) *
              a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)
          else 0) =
          (∑ b : V → Bool,
            ∏ u : V,
              if b u then
                if u = v then gamma / (Delta : ℝ)
                else if G.Adj v u then (gamma / (Delta : ℝ)) * a
                else gamma / (Delta : ℝ)
              else
                if u = v then 0 else 1 - gamma / (Delta : ℝ)) := by
      rw [Fintype.sum_equiv e]
      intro A
      by_cases hv : v ∈ A
      · simp only [e]
        simp [hv]
        let p : ℝ := gamma / (Delta : ℝ)
        let q : ℝ := 1 - gamma / (Delta : ℝ)
        have hfactor :
            (∏ u : V,
              if u ∈ A then
                if u = v then gamma / (Delta : ℝ)
                else if G.Adj v u then (gamma / (Delta : ℝ)) * a
                else gamma / (Delta : ℝ)
              else
                if u = v then 0 else 1 - gamma / (Delta : ℝ)) =
              (∏ u : V, if u ∈ A then p else q) *
                (∏ u : V, if u ∈ A ∧ G.Adj v u then a else 1) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro u _hu
          by_cases huA : u ∈ A
          · by_cases huv : u = v
            · subst u
              simp [p, q, hv]
            · by_cases hadj : G.Adj v u
              · simp [p, q, huA, huv, hadj]
              · simp [p, q, huA, huv, hadj]
          · have huv_ne : u ≠ v := by
              intro huv
              subst u
              exact huA hv
            simp [p, q, huA, huv_ne]
        have hbase :
            (∏ u : V, if u ∈ A then p else q) =
              p ^ A.card * q ^ ((Finset.univ : Finset V).card - A.card) := by
          rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset V))
            (p := fun u => u ∈ A) (f := fun u => if u ∈ A then p else q)]
          have hcompl :
              ((Finset.univ.filter fun u : V => ¬ u ∈ A).card) =
                (Finset.univ : Finset V).card - A.card := by
            simpa [Finset.sdiff_eq_filter] using
              (Finset.card_sdiff_of_subset (s := A) (t := (Finset.univ : Finset V))
                (by simp))
          have hleft : (∏ x with x ∈ A, if x ∈ A then p else q) = p ^ A.card := by
            trans ∏ x with x ∈ A, p
            · apply Finset.prod_congr rfl
              intro x hx
              simp at hx
              simp [hx]
            · simp [Finset.prod_const]
          have hright :
              (∏ x with x ∉ A, if x ∈ A then p else q) =
                q ^ ((Finset.univ : Finset V).card - A.card) := by
            trans ∏ x ∈ (Finset.univ.filter fun x : V => x ∉ A), q
            · apply Finset.prod_congr rfl
              intro x hx
              simp at hx
              simp [hx]
            · simp [Finset.prod_const, hcompl]
          rw [hleft, hright]
        have hneighbor :
            (∏ u : V, if u ∈ A ∧ G.Adj v u then a else 1) =
              a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card) := by
          rw [← Finset.prod_filter]
          simp
        rw [hfactor, hbase, hneighbor]
        simp [p, q]
      · have hzero :
            (∏ u : V,
              if decide (u ∈ A) then
                if u = v then gamma / (Delta : ℝ)
                else if G.Adj v u then (gamma / (Delta : ℝ)) * a
                else gamma / (Delta : ℝ)
              else
                if u = v then 0 else 1 - gamma / (Delta : ℝ)) = 0 := by
          rw [Finset.prod_eq_zero_iff]
          exact ⟨v, by simp, by simp [hv]⟩
        simpa [e, hv, decide_eq_true_eq] using hzero.symm
    exact hsum_bool.trans
      (SamplingOneVertexFixedThresholdProduct G Delta gamma a v hregular)
  calc
    (∑ A : Finset V,
      if v ∈ A then
        ((gamma / (Delta : ℝ)) ^ A.card *
          (1 - gamma / (Delta : ℝ)) ^
            ((Finset.univ : Finset V).card - A.card)) *
          (∫ a in (0 : ℝ)..1,
            a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
      else 0)
        = ∑ A : Finset V, ∫ a in (0 : ℝ)..1, F A a := hterm
    _ = ∫ a in (0 : ℝ)..1, ∑ A : Finset V, F A a := hsum_integral
    _ = ∫ a in (0 : ℝ)..1,
          (gamma / (Delta : ℝ)) *
            (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta := by
      apply intervalIntegral.integral_congr
      intro a _ha
      exact hpointwise a
    _ = (gamma / (Delta : ℝ)) *
        (∫ a in (0 : ℝ)..1,
          (1 - (gamma / (Delta : ℝ)) * (1 - a)) ^ Delta) := by
      rw [intervalIntegral.integral_const_mul]
