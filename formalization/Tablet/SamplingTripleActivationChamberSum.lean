import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option maxHeartbeats 2000000

open BigOperators

-- [TABLET NODE: SamplingTripleActivationChamberSum]
theorem SamplingTripleActivationChamberSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (μ : Finset V → ℝ)
    (hsample : RandomIndependentSetSampling G Delta gamma μ)
    (hDelta_pos : 0 < Delta)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let Q : Finset V := {a, b, c}
    let N_x : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ G.Adj a w).card
    let N_y : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card
    let N_z : ℕ :=
      ((Finset.univ : Finset V).filter fun w : V =>
        w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card
    (∑ A : Finset V,
      if Q ⊆ A then
        ((gamma / (Delta : ℝ)) ^ A.card *
            (1 - gamma / (Delta : ℝ)) ^
              ((Finset.univ : Finset V).card - A.card)) *
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma,
                  (1 - x / gamma) ^
                      ((A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card) *
                    (1 - y / gamma) ^
                      ((A.filter fun w : V =>
                        w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card) *
                      (1 - z / gamma) ^
                        ((A.filter fun w : V =>
                          w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card))
      else 0) =
    (1 / (Delta : ℝ) ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / (Delta : ℝ)) ^ N_x *
                (1 - y / (Delta : ℝ)) ^ N_y *
                  (1 - z / (Delta : ℝ)) ^ N_z := by
-- BODY
  classical
  have hgamma_pos : 0 < gamma := hsample.1
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hDelta_real_pos : 0 < (Delta : ℝ) := by exact_mod_cast hDelta_pos
  have hDelta_ne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_real_pos
  let Q : Finset V := {a, b, c}
  let p : ℝ := gamma / (Delta : ℝ)
  let q : ℝ := 1 - gamma / (Delta : ℝ)
  let Xset : Finset V :=
    (Finset.univ : Finset V).filter fun w : V => w ∉ Q ∧ G.Adj a w
  let Yset : Finset V :=
    (Finset.univ : Finset V).filter fun w : V => w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w
  let Zset : Finset V :=
    (Finset.univ : Finset V).filter fun w : V =>
      w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w
  let atom : Finset V → ℝ := fun A =>
    p ^ A.card * q ^ ((Finset.univ : Finset V).card - A.card)
  let chamber : Finset V → ℝ → ℝ → ℝ → ℝ := fun A x y z =>
    (1 - x / gamma) ^
        ((A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card) *
      (1 - y / gamma) ^
        ((A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card) *
        (1 - z / gamma) ^
          ((A.filter fun w : V =>
            w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card)
  let target : ℝ → ℝ → ℝ → ℝ := fun x y z =>
    (1 - x / (Delta : ℝ)) ^ Xset.card *
      (1 - y / (Delta : ℝ)) ^ Yset.card *
        (1 - z / (Delta : ℝ)) ^ Zset.card
  have hQcard : Q.card = 3 := by
    simp [Q, hab, hac, hbc]
  have hpointwise (x y z : ℝ) :
      (∑ A : Finset V, if Q ⊆ A then atom A * chamber A x y z else 0) =
        p ^ 3 * target x y z := by
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
    let loc : V → Bool → ℝ := fun u active =>
      if active then
        if u ∈ Q then p
        else if G.Adj a u then p * (1 - x / gamma)
        else if G.Adj b u then p * (1 - y / gamma)
        else if G.Adj c u then p * (1 - z / gamma)
        else p
      else
        if u ∈ Q then 0 else q
    have hsum_bool :
        (∑ A : Finset V, if Q ⊆ A then atom A * chamber A x y z else 0) =
          ∑ b : V → Bool, ∏ u : V, loc u (b u) := by
      rw [Fintype.sum_equiv e]
      intro A
      by_cases hQA : Q ⊆ A
      · have hprod_factor :
            (∏ u : V, loc u (decide (u ∈ A))) =
              (∏ u : V, if u ∈ A then p else q) *
                (∏ u : V, if u ∈ A ∧ u ∉ Q ∧ G.Adj a u then
                    (1 - x / gamma) else 1) *
                  (∏ u : V, if u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u then
                    (1 - y / gamma) else 1) *
                    (∏ u : V,
                      if u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u then
                        (1 - z / gamma) else 1) := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
            ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro u _hu
          by_cases huA : u ∈ A
          · have hdec : decide (u ∈ A) = true := by simp [huA]
            by_cases huQ : u ∈ Q
            · simp [loc, hdec, huA, huQ]
            · by_cases hua : G.Adj a u
              · simp [loc, hdec, huA, huQ, hua, mul_assoc]
              · by_cases hub : G.Adj b u
                · simp [loc, hdec, huA, huQ, hua, hub, mul_assoc]
                · by_cases huc : G.Adj c u
                  · simp [loc, hdec, huA, huQ, hua, hub, huc, mul_assoc]
                  · simp [loc, hdec, huA, huQ, hua, hub, huc]
          · have hdec : decide (u ∈ A) = false := by simp [huA]
            have huQnot : u ∉ Q := by
              intro huQ
              exact huA (hQA huQ)
            simp [loc, hdec, huA, huQnot]
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
          have hleft : (∏ u with u ∈ A, if u ∈ A then p else q) = p ^ A.card := by
            trans ∏ u with u ∈ A, p
            · apply Finset.prod_congr rfl
              intro u hu
              simp at hu
              simp [hu]
            · simp [Finset.prod_const]
          have hright :
              (∏ u with u ∉ A, if u ∈ A then p else q) =
                q ^ ((Finset.univ : Finset V).card - A.card) := by
            trans ∏ u ∈ (Finset.univ.filter fun u : V => u ∉ A), q
            · apply Finset.prod_congr rfl
              intro u hu
              simp at hu
              simp [hu]
            · simp [Finset.prod_const, hcompl]
          rw [hleft, hright]
        have hxprod :
            (∏ u : V, if u ∈ A ∧ u ∉ Q ∧ G.Adj a u then
                (1 - x / gamma) else 1) =
              (1 - x / gamma) ^
                ((A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card) := by
          rw [← Finset.prod_filter]
          have hcard :
              ((Finset.univ.filter fun u : V => u ∈ A ∧ u ∉ Q ∧ G.Adj a u).card) =
                ((A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card) := by
            congr 1
            ext u
            simp [and_assoc]
          simp [Finset.prod_const, hcard]
        have hyprod :
            (∏ u : V, if u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u then
                (1 - y / gamma) else 1) =
              (1 - y / gamma) ^
                ((A.filter fun w : V =>
                  w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card) := by
          rw [← Finset.prod_filter]
          have hcard :
              ((Finset.univ.filter fun u : V =>
                u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u).card) =
                ((A.filter fun w : V =>
                  w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card) := by
            congr 1
            ext u
            simp [and_assoc]
          simp [Finset.prod_const, hcard]
        have hzprod :
            (∏ u : V,
                if u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u then
                  (1 - z / gamma) else 1) =
              (1 - z / gamma) ^
                ((A.filter fun w : V =>
                  w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card) := by
          rw [← Finset.prod_filter]
          have hcard :
              ((Finset.univ.filter fun u : V =>
                u ∈ A ∧ u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u).card) =
                ((A.filter fun w : V =>
                  w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card) := by
            congr 1
            ext u
            simp [and_assoc]
          simp [Finset.prod_const, hcard]
        change (if Q ⊆ A then atom A * chamber A x y z else 0) =
          ∏ u : V, loc u (decide (u ∈ A))
        rw [hprod_factor, hbase, hxprod, hyprod, hzprod]
        simp [atom, chamber, hQA, mul_assoc]
      · have hzero :
            (∏ u : V, loc u (decide (u ∈ A))) = 0 := by
          rw [Finset.prod_eq_zero_iff]
          obtain ⟨u, huQ, huA⟩ : ∃ u, u ∈ Q ∧ u ∉ A := by
            simpa [Finset.subset_iff] using hQA
          refine ⟨u, by simp, ?_⟩
          have hdec : decide (u ∈ A) = false := by simp [huA]
          simp [loc, hdec, huQ]
        simpa [hQA] using hzero.symm
    have hdecision :
        (∑ b : V → Bool, ∏ u : V, loc u (b u)) =
          ∏ u : V, (loc u true + loc u false) := by
      simpa using
        (Fintype.prod_sum (fun u (bb : Bool) => loc u bb)).symm
    have hprod_split :
        (∏ u : V, (loc u true + loc u false)) =
          p ^ 3 * target x y z := by
      let f : V → ℝ := fun u => loc u true + loc u false
      have hfQ (u : V) (hu : u ∈ Q) : f u = p := by
        simp [f, loc, hu]
      have hfX (u : V) (hu : u ∈ Xset) : f u = 1 - x / (Delta : ℝ) := by
        rcases (by simpa [Xset] using hu : u ∉ Q ∧ G.Adj a u) with ⟨huQ, hua⟩
        simp [f, loc, huQ, hua, p, q]
        field_simp [hgamma_ne, hDelta_ne]
        ring
      have hfY (u : V) (hu : u ∈ Yset) : f u = 1 - y / (Delta : ℝ) := by
        rcases (by simpa [Yset] using hu :
          u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u) with ⟨huQ, hua, hub⟩
        simp [f, loc, huQ, hua, hub, p, q]
        field_simp [hgamma_ne, hDelta_ne]
        ring
      have hfZ (u : V) (hu : u ∈ Zset) : f u = 1 - z / (Delta : ℝ) := by
        rcases (by simpa [Zset] using hu :
          u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u) with
          ⟨huQ, hua, hub, huc⟩
        simp [f, loc, huQ, hua, hub, huc, p, q]
        field_simp [hgamma_ne, hDelta_ne]
        ring
      have hfOther (u : V) (huQ : u ∉ Q) (huX : u ∉ Xset) (huY : u ∉ Yset)
          (huZ : u ∉ Zset) : f u = 1 := by
        have hx : ¬ G.Adj a u := by
          intro h
          exact huX (by simp [Xset, huQ, h])
        have hy : ¬ G.Adj b u := by
          intro h
          exact huY (by simp [Yset, huQ, hx, h])
        have hz : ¬ G.Adj c u := by
          intro h
          exact huZ (by simp [Zset, huQ, hx, hy, h])
        simp [f, loc, huQ, hx, hy, hz, p, q]
      have hdisjQX : Disjoint Q Xset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huQ huX
        exact (by simpa [Xset] using huX : u ∉ Q ∧ G.Adj a u).1 huQ
      have hdisjQY : Disjoint Q Yset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huQ huY
        exact (by simpa [Yset] using huY :
          u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u).1 huQ
      have hdisjQZ : Disjoint Q Zset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huQ huZ
        exact (by simpa [Zset] using huZ :
          u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u).1 huQ
      have hdisjXY : Disjoint Xset Yset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huX huY
        have hxa : G.Adj a u :=
          (by simpa [Xset] using huX : u ∉ Q ∧ G.Adj a u).2
        have hya : ¬ G.Adj a u :=
          (by simpa [Yset] using huY : u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u).2.1
        exact hya hxa
      have hdisjXZ : Disjoint Xset Zset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huX huZ
        have hxa : G.Adj a u :=
          (by simpa [Xset] using huX : u ∉ Q ∧ G.Adj a u).2
        have hza : ¬ G.Adj a u :=
          (by simpa [Zset] using huZ :
            u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u).2.1
        exact hza hxa
      have hdisjYZ : Disjoint Yset Zset := by
        refine Finset.disjoint_left.mpr ?_
        intro u huY huZ
        have hyb : G.Adj b u :=
          (by simpa [Yset] using huY : u ∉ Q ∧ ¬ G.Adj a u ∧ G.Adj b u).2.2
        have hzb : ¬ G.Adj b u :=
          (by simpa [Zset] using huZ :
            u ∉ Q ∧ ¬ G.Adj a u ∧ ¬ G.Adj b u ∧ G.Adj c u).2.2.1
        exact hzb hyb
      have hunion :
          (∏ u : V, f u) =
            (∏ u ∈ Q, f u) *
              (∏ u ∈ Xset, f u) *
                (∏ u ∈ Yset, f u) *
                  (∏ u ∈ Zset, f u) := by
        let U : Finset V := ((Q ∪ Xset) ∪ Yset) ∪ Zset
        have houtside : (∏ u ∈ (Finset.univ : Finset V) \ U, f u) = 1 := by
          apply Finset.prod_eq_one
          intro u hu
          have huU : u ∉ U := (Finset.mem_sdiff.mp hu).2
          have huQ : u ∉ Q := by
            intro h
            exact huU (by simp [U, h])
          have huX : u ∉ Xset := by
            intro h
            exact huU (by simp [U, h])
          have huY : u ∉ Yset := by
            intro h
            exact huU (by simp [U, h])
          have huZ : u ∉ Zset := by
            intro h
            exact huU (by simp [U, h])
          exact hfOther u huQ huX huY huZ
        rw [← Finset.prod_sdiff (by simp : U ⊆ (Finset.univ : Finset V))]
        rw [houtside, one_mul]
        have hUX : Disjoint Q Xset := hdisjQX
        have hQ_X_Y : Disjoint (Q ∪ Xset) Yset := by
          rw [Finset.disjoint_union_left]
          exact ⟨hdisjQY, hdisjXY⟩
        have hQ_X_Y_Z : Disjoint (Q ∪ Xset ∪ Yset) Zset := by
          rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
          exact ⟨⟨hdisjQZ, hdisjXZ⟩, hdisjYZ⟩
        calc
          (∏ u ∈ U, f u)
              = (∏ u ∈ (Q ∪ Xset ∪ Yset), f u) * (∏ u ∈ Zset, f u) := by
                rw [show U = Q ∪ Xset ∪ Yset ∪ Zset by simp [U]]
                rw [Finset.prod_union hQ_X_Y_Z]
          _ = ((∏ u ∈ (Q ∪ Xset), f u) * (∏ u ∈ Yset, f u)) *
                (∏ u ∈ Zset, f u) := by
                rw [Finset.prod_union hQ_X_Y]
          _ = (((∏ u ∈ Q, f u) * (∏ u ∈ Xset, f u)) *
                (∏ u ∈ Yset, f u)) * (∏ u ∈ Zset, f u) := by
                rw [Finset.prod_union hUX]
          _ = (∏ u ∈ Q, f u) * (∏ u ∈ Xset, f u) *
                (∏ u ∈ Yset, f u) * (∏ u ∈ Zset, f u) := by ring
      have hQprod : (∏ u ∈ Q, f u) = p ^ 3 := by
        trans ∏ u ∈ Q, p
        · apply Finset.prod_congr rfl
          intro u hu
          exact hfQ u hu
        · simp [Finset.prod_const, hQcard]
      have hXprod : (∏ u ∈ Xset, f u) = (1 - x / (Delta : ℝ)) ^ Xset.card := by
        trans ∏ u ∈ Xset, (1 - x / (Delta : ℝ))
        · apply Finset.prod_congr rfl
          intro u hu
          exact hfX u hu
        · simp [Finset.prod_const]
      have hYprod : (∏ u ∈ Yset, f u) = (1 - y / (Delta : ℝ)) ^ Yset.card := by
        trans ∏ u ∈ Yset, (1 - y / (Delta : ℝ))
        · apply Finset.prod_congr rfl
          intro u hu
          exact hfY u hu
        · simp [Finset.prod_const]
      have hZprod : (∏ u ∈ Zset, f u) = (1 - z / (Delta : ℝ)) ^ Zset.card := by
        trans ∏ u ∈ Zset, (1 - z / (Delta : ℝ))
        · apply Finset.prod_congr rfl
          intro u hu
          exact hfZ u hu
        · simp [Finset.prod_const]
      calc
        (∏ u : V, (loc u true + loc u false))
            = ∏ u : V, f u := rfl
        _ = (∏ u ∈ Q, f u) * (∏ u ∈ Xset, f u) *
              (∏ u ∈ Yset, f u) * (∏ u ∈ Zset, f u) := hunion
        _ = p ^ 3 * target x y z := by
          rw [hQprod, hXprod, hYprod, hZprod]
          simp [target, mul_assoc]
    exact hsum_bool.trans (hdecision.trans hprod_split)
  have hpointwise_scaled (x y z : ℝ) :
      (∑ A : Finset V,
          if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0) =
        (1 / (Delta : ℝ) ^ 3) * target x y z := by
    calc
      (∑ A : Finset V,
          if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0)
          = (1 / gamma ^ 3) *
              (∑ A : Finset V, if Q ⊆ A then atom A * chamber A x y z else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A _hA
            by_cases hQA : Q ⊆ A
            · ring_nf
              simp [hQA, mul_assoc, mul_left_comm, mul_comm]
            · simp [hQA]
      _ = (1 / gamma ^ 3) * (p ^ 3 * target x y z) := by rw [hpointwise]
      _ = (1 / (Delta : ℝ) ^ 3) * target x y z := by
        dsimp [p]
        field_simp [hgamma_ne, hDelta_ne]
  have hterm :
      (∑ A : Finset V,
        if Q ⊆ A then
          (atom A) *
            ((1 / gamma ^ 3) *
              ∫ z in (0 : ℝ)..gamma,
                ∫ y in z..gamma,
                  ∫ x in y..gamma, chamber A x y z)
        else 0) =
        ∑ A : Finset V,
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma,
                if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0 := by
    apply Finset.sum_congr rfl
    intro A _hA
    by_cases hQA : Q ⊆ A
    · simp [hQA, intervalIntegral.integral_const_mul, mul_assoc]
    · simp [hQA]
  have hsum_integral :
      (∑ A : Finset V,
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma,
                if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0) =
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              ∑ A : Finset V,
                if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0 := by
    let F : Finset V → ℝ → ℝ → ℝ → ℝ := fun A x y z =>
      if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0
    let coeff : Finset V → ℝ := fun A => if Q ⊆ A then atom A * (1 / gamma ^ 3) else 0
    let xp : Finset V → ℝ → ℝ := fun A x =>
      (1 - x / gamma) ^
        ((A.filter fun w : V => w ∉ Q ∧ G.Adj a w).card)
    let yp : Finset V → ℝ → ℝ := fun A y =>
      (1 - y / gamma) ^
        ((A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ G.Adj b w).card)
    let zp : Finset V → ℝ → ℝ := fun A z =>
      (1 - z / gamma) ^
        ((A.filter fun w : V =>
          w ∉ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ G.Adj c w).card)
    have hFfactor (A : Finset V) (x y z : ℝ) :
        F A x y z = coeff A * xp A x * yp A y * zp A z := by
      by_cases hQA : Q ⊆ A
      · simp [F, coeff, xp, yp, zp, chamber, hQA]
        ring
      · simp [F, coeff, hQA]
    have hxp_cont (A : Finset V) : Continuous (xp A) := by
      dsimp [xp]
      continuity
    have hyp_cont (A : Finset V) : Continuous (yp A) := by
      dsimp [yp]
      continuity
    have hzp_cont (A : Finset V) : Continuous (zp A) := by
      dsimp [zp]
      continuity
    have hprim_x_cont (A : Finset V) :
        Continuous fun y : ℝ => ∫ x in y..gamma, xp A x := by
      have hbase : Continuous fun y : ℝ => ∫ x in gamma..y, xp A x :=
        intervalIntegral.continuous_primitive
          (fun r s => (hxp_cont A).intervalIntegrable r s) gamma
      have hneg : Continuous fun y : ℝ => - ∫ x in gamma..y, xp A x := hbase.neg
      convert hneg using 1
      ext y
      rw [intervalIntegral.integral_symm]
    have hinner_eq (A : Finset V) (y z : ℝ) :
        (∫ x in y..gamma, F A x y z) =
          (coeff A * yp A y * zp A z) * ∫ x in y..gamma, xp A x := by
      calc
        (∫ x in y..gamma, F A x y z)
            = ∫ x in y..gamma, (coeff A * yp A y * zp A z) * xp A x := by
              apply intervalIntegral.integral_congr
              intro x _hx
              change F A x y z = (coeff A * yp A y * zp A z) * xp A x
              rw [hFfactor]
              ring
        _ = (coeff A * yp A y * zp A z) * ∫ x in y..gamma, xp A x := by
              rw [intervalIntegral.integral_const_mul]
    have hmid_integrable (A : Finset V) (z : ℝ) :
        IntervalIntegrable (fun y => ∫ x in y..gamma, F A x y z) MeasureTheory.volume z gamma := by
      have hcont : Continuous fun y : ℝ =>
          (coeff A * yp A y * zp A z) * ∫ x in y..gamma, xp A x := by
        exact (((continuous_const.mul (hyp_cont A)).mul continuous_const).mul (hprim_x_cont A))
      have hci := hcont.intervalIntegrable (μ := MeasureTheory.volume) z gamma
      convert hci using 1
      ext y
      exact hinner_eq A y z
    have hphi_cont (A : Finset V) :
        Continuous fun y : ℝ => (coeff A * yp A y) * ∫ x in y..gamma, xp A x := by
      exact ((continuous_const.mul (hyp_cont A)).mul (hprim_x_cont A))
    have hprim_phi_cont (A : Finset V) :
        Continuous fun z : ℝ =>
          ∫ y in z..gamma, (coeff A * yp A y) * ∫ x in y..gamma, xp A x := by
      have hbase : Continuous fun z : ℝ =>
          ∫ y in gamma..z, (coeff A * yp A y) * ∫ x in y..gamma, xp A x :=
        intervalIntegral.continuous_primitive
          (fun r s => (hphi_cont A).intervalIntegrable r s) gamma
      have hneg : Continuous fun z : ℝ =>
          - ∫ y in gamma..z, (coeff A * yp A y) * ∫ x in y..gamma, xp A x := hbase.neg
      convert hneg using 1
      ext z
      rw [intervalIntegral.integral_symm]
    have houter_eq (A : Finset V) (z : ℝ) :
        (∫ y in z..gamma, ∫ x in y..gamma, F A x y z) =
          zp A z * ∫ y in z..gamma,
            (coeff A * yp A y) * ∫ x in y..gamma, xp A x := by
      calc
        (∫ y in z..gamma, ∫ x in y..gamma, F A x y z)
            = ∫ y in z..gamma,
                zp A z * ((coeff A * yp A y) * ∫ x in y..gamma, xp A x) := by
              apply intervalIntegral.integral_congr
              intro y _hy
              change (∫ x in y..gamma, F A x y z) =
                zp A z * (coeff A * yp A y * ∫ x in y..gamma, xp A x)
              rw [hinner_eq]
              ring
        _ = zp A z * ∫ y in z..gamma,
              (coeff A * yp A y) * ∫ x in y..gamma, xp A x := by
              rw [intervalIntegral.integral_const_mul]
    have houter_integrable (A : Finset V) :
        IntervalIntegrable (fun z => ∫ y in z..gamma, ∫ x in y..gamma, F A x y z)
          MeasureTheory.volume 0 gamma := by
      have hcont : Continuous fun z : ℝ =>
          zp A z * ∫ y in z..gamma,
            (coeff A * yp A y) * ∫ x in y..gamma, xp A x :=
        (hzp_cont A).mul (hprim_phi_cont A)
      have hci := hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 gamma
      convert hci using 1
      ext z
      exact houter_eq A z
    calc
      (∑ A : Finset V,
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma, F A x y z)
          = ∫ z in (0 : ℝ)..gamma,
              ∑ A : Finset V,
                ∫ y in z..gamma,
                  ∫ x in y..gamma, F A x y z := by
            simpa using
              (intervalIntegral.integral_finset_sum
                (s := (Finset.univ : Finset (Finset V)))
                (f := fun A z =>
                  ∫ y in z..gamma, ∫ x in y..gamma, F A x y z)
                (a := (0 : ℝ)) (b := gamma)
                (by
                  intro A _hA
                  exact houter_integrable A)).symm
      _ = ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∑ A : Finset V,
                ∫ x in y..gamma, F A x y z := by
            apply intervalIntegral.integral_congr
            intro z _hz
            simpa using
              (intervalIntegral.integral_finset_sum
                (s := (Finset.univ : Finset (Finset V)))
                (f := fun A y => ∫ x in y..gamma, F A x y z)
                (a := z) (b := gamma)
                (by
                  intro A _hA
                  exact hmid_integrable A z)).symm
      _ = ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma,
                ∑ A : Finset V, F A x y z := by
            apply intervalIntegral.integral_congr
            intro z _hz
            apply intervalIntegral.integral_congr
            intro y _hy
            simpa using
              (intervalIntegral.integral_finset_sum
                (s := (Finset.univ : Finset (Finset V)))
                (f := fun A x => F A x y z)
                (a := y) (b := gamma)
                (by
                  intro A _hA
                  by_cases hQA : Q ⊆ A
                  · apply Continuous.intervalIntegrable
                    continuity
                  · simp [F, hQA])).symm
  dsimp only
  change
    (∑ A : Finset V,
      if Q ⊆ A then
        atom A *
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma, chamber A x y z)
      else 0) =
      (1 / (Delta : ℝ) ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma, target x y z
  calc
    (∑ A : Finset V,
      if Q ⊆ A then
        atom A *
          ((1 / gamma ^ 3) *
            ∫ z in (0 : ℝ)..gamma,
              ∫ y in z..gamma,
                ∫ x in y..gamma, chamber A x y z)
      else 0)
        = ∑ A : Finset V,
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma,
                if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0 :=
          hterm
    _ = ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              ∑ A : Finset V,
                if Q ⊆ A then atom A * ((1 / gamma ^ 3) * chamber A x y z) else 0 :=
          hsum_integral
    _ = ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 / (Delta : ℝ) ^ 3) * target x y z := by
          apply intervalIntegral.integral_congr
          intro z _hz
          apply intervalIntegral.integral_congr
          intro y _hy
          apply intervalIntegral.integral_congr
          intro x _hx
          exact hpointwise_scaled x y z
    _ = (1 / (Delta : ℝ) ^ 3) *
          ∫ z in (0 : ℝ)..gamma,
            ∫ y in z..gamma,
              ∫ x in y..gamma, target x y z := by
          simp [intervalIntegral.integral_const_mul, mul_assoc]
