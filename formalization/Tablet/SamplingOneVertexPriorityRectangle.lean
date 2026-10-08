import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingOneVertexPriorityRectangle]
theorem SamplingOneVertexPriorityRectangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) ⊤)
    (A : Finset V) (v : V) (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hrect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ u : V, t u ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧
            ∀ u : V, 0 ≤ ω.2 u ∧ ω.2 u ≤ t u} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ u : V, t u)) :
    ν {ω |
      ω.1 = A ∧
        ∀ u : V, 0 ≤ ω.2 u ∧
          ω.2 u ≤ if u = v then b else if u ∈ A ∧ G.Adj v u then a else 1} =
      ν {ω | ω.1 = A} *
        ENNReal.ofReal
          (b * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
-- BODY
  classical
  let t : V → ℝ := fun u => if u = v then b else if u ∈ A ∧ G.Adj v u then a else 1
  have ht : ∀ u : V, t u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u
    by_cases huv : u = v
    · simp [t, huv, hb0, hb1]
    · by_cases h : u ∈ A ∧ G.Adj v u
      · simp [t, huv, h, ha0, ha1]
      · simp [t, huv, h]
  have hprod :
      (∏ u : V, t u) =
        b * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card) := by
    change (∏ u ∈ (Finset.univ : Finset V), t u) =
        b * a ^ ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)
    rw [Finset.prod_eq_mul_prod_diff_singleton (s := (Finset.univ : Finset V)) v t
      (by intro hv; simp at hv)]
    have ht_v : t v = b := by simp [t]
    rw [ht_v]
    congr 1
    have hdiff :
        (∏ x ∈ (Finset.univ : Finset V) \ {v}, t x) =
          ∏ x ∈ (Finset.univ : Finset V) \ {v},
            if x ∈ A ∧ G.Adj v x then a else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      have hxv : x ≠ v := by
        simpa using (Finset.mem_sdiff.mp hx).2
      simp [t, hxv]
    rw [hdiff]
    have hfilter_diff :
        (∏ x ∈ (Finset.univ : Finset V) \ {v},
            if x ∈ A ∧ G.Adj v x then a else 1) =
          ∏ x ∈ (Finset.univ : Finset V) \ {v} with
              (x ∈ A ∧ G.Adj v x), a := by
      rw [← Finset.prod_filter]
    rw [hfilter_diff]
    have hfilter_eq :
        ((Finset.univ : Finset V) \ {v}).filter
            (fun x : V => x ∈ A ∧ G.Adj v x) =
          (Finset.univ.filter fun x : V => x ∈ A ∧ G.Adj v x) := by
      ext x
      by_cases hxv : x = v
      · subst x
        simp
      · simp [hxv]
    rw [hfilter_eq]
    simp
  simpa [t, hprod] using hrect A t ht
