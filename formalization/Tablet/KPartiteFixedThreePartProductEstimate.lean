import Tablet.Preamble

open scoped BigOperators

-- [TABLET NODE: KPartiteFixedThreePartProductEstimate]
theorem KPartiteFixedThreePartProductEstimate :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
        ∀ A B C : Finset V,
          (((A.product (B.product C)).filter
              (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)).card : ℝ)
            ≤ Real.sqrt
              ((((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
                (((A.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
                (((B.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ)) := by
-- BODY
  classical
  intro V _ _ G _ A B C
  let T : Finset (V × V × V) :=
    (A.product (B.product C)).filter
      (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)
  let AB : Finset (V × V) := (A.product B).filter (fun p => G.Adj p.1 p.2)
  let AC : Finset (V × V) := (A.product C).filter (fun p => G.Adj p.1 p.2)
  let BC : Finset (V × V) := (B.product C).filter (fun p => G.Adj p.1 p.2)
  let Tb : V → Finset (V × V × V) := fun b => T.filter (fun t => t.2.1 = b)
  let ab : V → Finset (V × V) := fun b => AB.filter (fun p => p.2 = b)
  let cb : V → Finset (V × V) := fun b => BC.filter (fun p => p.1 = b)
  have hT_maps : (T : Set (V × V × V)).MapsTo (fun t => t.2.1) B := by
    intro t ht
    have htprod : t ∈ A.product (B.product C) := (Finset.mem_filter.mp ht).1
    have hbc : t.2 ∈ B.product C := (Finset.mem_product.mp htprod).2
    exact (Finset.mem_product.mp hbc).1
  have hT_sum_nat :
      T.card = ∑ b ∈ B, (Tb b).card := by
    rw [Finset.card_eq_sum_card_fiberwise hT_maps]
  have hab_sum_nat : AB.card = ∑ b ∈ B, (ab b).card := by
    have hAB_maps : (AB : Set (V × V)).MapsTo (fun p => p.2) B := by
      intro p hp
      have hprod : p ∈ A.product B := (Finset.mem_filter.mp hp).1
      exact (Finset.mem_product.mp hprod).2
    rw [Finset.card_eq_sum_card_fiberwise hAB_maps]
  have hcb_sum_nat : BC.card = ∑ b ∈ B, (cb b).card := by
    have hBC_maps : (BC : Set (V × V)).MapsTo (fun p => p.1) B := by
      intro p hp
      have hprod : p ∈ B.product C := (Finset.mem_filter.mp hp).1
      exact (Finset.mem_product.mp hprod).1
    rw [Finset.card_eq_sum_card_fiberwise hBC_maps]
  have hTb_le_mul : ∀ b : V, (Tb b).card ≤ (ab b).card * (cb b).card := by
    intro b
    let F : {t // t ∈ Tb b} → ({p // p ∈ ab b} × {p // p ∈ cb b}) := fun t =>
      (⟨(t.1.1, t.1.2.1), by
          have htT : t.1 ∈ T := (Finset.mem_filter.mp t.2).1
          have hb : t.1.2.1 = b := (Finset.mem_filter.mp t.2).2
          have htprod : t.1 ∈ A.product (B.product C) := (Finset.mem_filter.mp htT).1
          have htadj := (Finset.mem_filter.mp htT).2
          have hA : t.1.1 ∈ A := (Finset.mem_product.mp htprod).1
          have hBCprod : t.1.2 ∈ B.product C := (Finset.mem_product.mp htprod).2
          have hB : t.1.2.1 ∈ B := (Finset.mem_product.mp hBCprod).1
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hA, hB⟩, htadj.1⟩, hb⟩⟩,
        ⟨(t.1.2.1, t.1.2.2), by
          have htT : t.1 ∈ T := (Finset.mem_filter.mp t.2).1
          have hb : t.1.2.1 = b := (Finset.mem_filter.mp t.2).2
          have htprod : t.1 ∈ A.product (B.product C) := (Finset.mem_filter.mp htT).1
          have htadj := (Finset.mem_filter.mp htT).2
          have hBCprod : t.1.2 ∈ B.product C := (Finset.mem_product.mp htprod).2
          have hB : t.1.2.1 ∈ B := (Finset.mem_product.mp hBCprod).1
          have hC : t.1.2.2 ∈ C := (Finset.mem_product.mp hBCprod).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨hB, hC⟩, htadj.2.2⟩, hb⟩⟩)
    have hF_inj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      have h1 : x.1.1 = y.1.1 := congrArg (fun z => z.1.1.1) hxy
      have h3 : x.1.2.2 = y.1.2.2 := congrArg (fun z => z.2.1.2) hxy
      have hx_b : x.1.2.1 = b := (Finset.mem_filter.mp x.2).2
      have hy_b : y.1.2.1 = b := (Finset.mem_filter.mp y.2).2
      cases x
      cases y
      simp only at h1 h3 hx_b hy_b ⊢
      exact Prod.ext h1 (Prod.ext (hx_b.trans hy_b.symm) h3)
    have hcard_le :
        Fintype.card {t // t ∈ Tb b} ≤
          Fintype.card ({p // p ∈ ab b} × {p // p ∈ cb b}) :=
      Fintype.card_le_of_injective F hF_inj
    rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_subtype, Fintype.card_subtype] at hcard_le
    simpa using hcard_le
  have hTb_le_AC : ∀ b : V, (Tb b).card ≤ AC.card := by
    intro b
    let F : {t // t ∈ Tb b} → {p // p ∈ AC} := fun t =>
      ⟨(t.1.1, t.1.2.2), by
        have htT : t.1 ∈ T := (Finset.mem_filter.mp t.2).1
        have htprod : t.1 ∈ A.product (B.product C) := (Finset.mem_filter.mp htT).1
        have htadj := (Finset.mem_filter.mp htT).2
        have hA : t.1.1 ∈ A := (Finset.mem_product.mp htprod).1
        have hBCprod : t.1.2 ∈ B.product C := (Finset.mem_product.mp htprod).2
        have hC : t.1.2.2 ∈ C := (Finset.mem_product.mp hBCprod).2
        simp [AC, hA, hC, htadj.2.1]⟩
    have hF_inj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      have h1 : x.1.1 = y.1.1 := congrArg (fun z => z.1.1) hxy
      have h3 : x.1.2.2 = y.1.2.2 := congrArg (fun z => z.1.2) hxy
      have hx_b : x.1.2.1 = b := (Finset.mem_filter.mp x.2).2
      have hy_b : y.1.2.1 = b := (Finset.mem_filter.mp y.2).2
      cases x
      cases y
      simp only at h1 h3 hx_b hy_b ⊢
      exact Prod.ext h1 (Prod.ext (hx_b.trans hy_b.symm) h3)
    have hcard_le : Fintype.card {t // t ∈ Tb b} ≤ Fintype.card {p // p ∈ AC} :=
      Fintype.card_le_of_injective F hF_inj
    rw [Fintype.card_subtype, Fintype.card_subtype] at hcard_le
    simpa using hcard_le
  have hterm_bound :
      ∀ b ∈ B,
        ((Tb b).card : ℝ) ≤
          Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ)) := by
    intro b hb
    have h1 : (((Tb b).card : ℝ) ^ 2) ≤
        (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ)) := by
      have hm : ((Tb b).card : ℝ) ≤ ((ab b).card : ℝ) * ((cb b).card : ℝ) := by
        exact_mod_cast hTb_le_mul b
      have hy : ((Tb b).card : ℝ) ≤ (AC.card : ℝ) := by
        exact_mod_cast hTb_le_AC b
      have ht_nonneg : 0 ≤ ((Tb b).card : ℝ) := by positivity
      have hm_nonneg : 0 ≤ (((ab b).card : ℝ) * ((cb b).card : ℝ)) := by positivity
      nlinarith
    exact Real.le_sqrt_of_sq_le h1
  have hsum_T_le :
      ((T.card : ℝ)) ≤
        ∑ b ∈ B, Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ)) := by
    rw [hT_sum_nat, Nat.cast_sum]
    exact Finset.sum_le_sum (by
      intro b hb
      exact hterm_bound b hb)
  have hsum_sqrt_le :
      (∑ b ∈ B, Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ))) ≤
        Real.sqrt (AC.card : ℝ) *
          (Real.sqrt (∑ b ∈ B, ((ab b).card : ℝ)) *
            Real.sqrt (∑ b ∈ B, ((cb b).card : ℝ))) := by
    have hrewrite :
        (∑ b ∈ B, Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ))) =
          Real.sqrt (AC.card : ℝ) *
            (∑ b ∈ B, Real.sqrt ((ab b).card : ℝ) * Real.sqrt ((cb b).card : ℝ)) := by
      calc
        (∑ b ∈ B, Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ)))
            = ∑ b ∈ B,
                Real.sqrt (AC.card : ℝ) *
                  (Real.sqrt ((ab b).card : ℝ) * Real.sqrt ((cb b).card : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hab_nonneg : 0 ≤ ((ab b).card : ℝ) := by positivity
              have hcb_nonneg : 0 ≤ ((cb b).card : ℝ) := by positivity
              have hAC_nonneg : 0 ≤ (AC.card : ℝ) := by positivity
              calc
                Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ))
                    = Real.sqrt ((AC.card : ℝ) * (((ab b).card : ℝ) * ((cb b).card : ℝ))) := by
                        ring_nf
                _ = Real.sqrt (AC.card : ℝ) *
                    Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ)) := by
                        rw [Real.sqrt_mul hAC_nonneg (((ab b).card : ℝ) * ((cb b).card : ℝ))]
                _ = Real.sqrt (AC.card : ℝ) *
                    (Real.sqrt ((ab b).card : ℝ) * Real.sqrt ((cb b).card : ℝ)) := by
                        rw [Real.sqrt_mul hab_nonneg ((cb b).card : ℝ)]
        _ = Real.sqrt (AC.card : ℝ) *
            (∑ b ∈ B, Real.sqrt ((ab b).card : ℝ) * Real.sqrt ((cb b).card : ℝ)) := by
              rw [Finset.mul_sum]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left
      (Real.sum_sqrt_mul_sqrt_le B
        (f := fun b => ((ab b).card : ℝ))
        (g := fun b => ((cb b).card : ℝ))
        (by intro b; positivity)
        (by intro b; positivity))
      (Real.sqrt_nonneg _)
  have hfinal_rewrite :
      Real.sqrt (AC.card : ℝ) *
          (Real.sqrt (∑ b ∈ B, ((ab b).card : ℝ)) *
            Real.sqrt (∑ b ∈ B, ((cb b).card : ℝ))) =
        Real.sqrt ((AB.card : ℝ) * (AC.card : ℝ) * (BC.card : ℝ)) := by
    have hAB : (∑ b ∈ B, ((ab b).card : ℝ)) = (AB.card : ℝ) := by
      rw [← Nat.cast_sum, ← hab_sum_nat]
    have hBC : (∑ b ∈ B, ((cb b).card : ℝ)) = (BC.card : ℝ) := by
      rw [← Nat.cast_sum, ← hcb_sum_nat]
    rw [hAB, hBC]
    have hAB_nonneg : 0 ≤ (AB.card : ℝ) := by positivity
    have hAC_nonneg : 0 ≤ (AC.card : ℝ) := by positivity
    have hBC_nonneg : 0 ≤ (BC.card : ℝ) := by positivity
    calc
      Real.sqrt (AC.card : ℝ) * (Real.sqrt (AB.card : ℝ) * Real.sqrt (BC.card : ℝ))
          = Real.sqrt ((AC.card : ℝ) * ((AB.card : ℝ) * (BC.card : ℝ))) := by
              rw [Real.sqrt_mul hAC_nonneg ((AB.card : ℝ) * (BC.card : ℝ))]
              rw [Real.sqrt_mul hAB_nonneg (BC.card : ℝ)]
      _ = Real.sqrt ((AB.card : ℝ) * (AC.card : ℝ) * (BC.card : ℝ)) := by
          ring_nf
  calc
    (((A.product (B.product C)).filter
        (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)).card : ℝ)
        = (T.card : ℝ) := by rfl
    _ ≤ ∑ b ∈ B, Real.sqrt (((ab b).card : ℝ) * ((cb b).card : ℝ) * (AC.card : ℝ)) := hsum_T_le
    _ ≤ Real.sqrt (AC.card : ℝ) *
          (Real.sqrt (∑ b ∈ B, ((ab b).card : ℝ)) *
            Real.sqrt (∑ b ∈ B, ((cb b).card : ℝ))) := hsum_sqrt_le
    _ = Real.sqrt ((AB.card : ℝ) * (AC.card : ℝ) * (BC.card : ℝ)) := hfinal_rewrite
    _ = Real.sqrt
              ((((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
                (((A.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ) *
                (((B.product C).filter (fun p => G.Adj p.1 p.2)).card : ℝ)) := by
          rfl
