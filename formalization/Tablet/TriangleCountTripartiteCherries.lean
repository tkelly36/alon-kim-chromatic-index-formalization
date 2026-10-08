import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic

open scoped BigOperators

set_option maxHeartbeats 800000

-- [TABLET NODE: TriangleCountTripartiteCherries]
theorem TriangleCountTripartiteCherries :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
        (∃ part : V → Fin 3, ∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
        (((Finset.univ : Finset (Finset V)).filter
            (fun s =>
              s.card = 3 ∧
                ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)).card : ℝ)
          ≤ (1 / 12 : ℝ) * ∑ v, ((G.degree v : ℝ) ^ (2 : ℕ)) := by
-- BODY
  classical
  intro V _ _ G _ htrip
  rcases htrip with ⟨part, hpart⟩
  let C : Finset (Finset V) := G.cliqueFinset 3
  have htriangle_eq :
      ((Finset.univ : Finset (Finset V)).filter
          (fun s =>
            s.card = 3 ∧
              ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)) = C := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, C,
      SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
    constructor
    · intro h
      exact ⟨by intro u hu v hv hne; exact h.2 hu hv hne, h.1⟩
    · intro h
      exact ⟨h.2, by intro u hu v hv hne; exact h.1 hu hv hne⟩
  rw [htriangle_eq]
  have vertex_bound_nat : ∀ (v : V) (i j : Fin 3), i ≠ j →
      (∀ w, G.Adj v w → part w = i ∨ part w = j) →
      ((C.filter (fun s => v ∈ s)).card ≤
        (((G.neighborFinset v).filter (fun u => part u = i)).card *
          ((G.neighborFinset v).filter (fun u => part u = j)).card)) := by
    intro v i j hij hcover
    let Tv : Finset (Finset V) := C.filter (fun s => v ∈ s)
    let A : Finset V := (G.neighborFinset v).filter (fun u => part u = i)
    let B : Finset V := (G.neighborFinset v).filter (fun u => part u = j)
    have exists_color (c d : Fin 3) (_hcd : c ≠ d)
        (hcov : ∀ w, G.Adj v w → part w = c ∨ part w = d)
        {s : Finset V} (hs : s ∈ G.cliqueFinset 3) (hvs : v ∈ s) :
        ∃ u, u ∈ s ∧ G.Adj v u ∧ part u = c := by
      rcases (SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs)) with
        ⟨a, b, c', hab, hac, hbc, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvs ⊢
      rcases hvs with rfl | rfl | rfl
      · have hb : part b = c ∨ part b = d := hcov b hab
        have hc : part c' = c ∨ part c' = d := hcov c' hac
        have hbcpart : part b ≠ part c' := hpart hbc
        rcases hb with hb | hb <;> rcases hc with hc | hc
        · exact False.elim (hbcpart (hb.trans hc.symm))
        · exact ⟨b, by simp, hab, hb⟩
        · exact ⟨c', by simp, hac, hc⟩
        · exact False.elim (hbcpart (hb.trans hc.symm))
      · have ha : part a = c ∨ part a = d := hcov a hab.symm
        have hc : part c' = c ∨ part c' = d := hcov c' hbc
        have hacpart : part a ≠ part c' := hpart hac
        rcases ha with ha | ha <;> rcases hc with hc | hc
        · exact False.elim (hacpart (ha.trans hc.symm))
        · exact ⟨a, by simp, hab.symm, ha⟩
        · exact ⟨c', by simp, hbc, hc⟩
        · exact False.elim (hacpart (ha.trans hc.symm))
      · have ha : part a = c ∨ part a = d := hcov a hac.symm
        have hb : part b = c ∨ part b = d := hcov b hbc.symm
        have habpart : part a ≠ part b := hpart hab
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact False.elim (habpart (ha.trans hb.symm))
        · exact ⟨a, by simp, hac.symm, ha⟩
        · exact ⟨b, by simp, hbc.symm, hb⟩
        · exact False.elim (habpart (ha.trans hb.symm))
    let ai : {s // s ∈ Tv} → V := fun x =>
      Classical.choose (exists_color i j hij hcover
        (by simpa [C, Tv] using (Finset.mem_filter.mp x.2).1) (Finset.mem_filter.mp x.2).2)
    let bj : {s // s ∈ Tv} → V := fun x =>
      Classical.choose (exists_color j i hij.symm (by intro w hw; exact (hcover w hw).symm)
        (by simpa [C, Tv] using (Finset.mem_filter.mp x.2).1) (Finset.mem_filter.mp x.2).2)
    have ai_spec : ∀ x : {s // s ∈ Tv}, ai x ∈ x.1 ∧ G.Adj v (ai x) ∧ part (ai x) = i := by
      intro x
      exact Classical.choose_spec (exists_color i j hij hcover
        (by simpa [C, Tv] using (Finset.mem_filter.mp x.2).1) (Finset.mem_filter.mp x.2).2)
    have bj_spec : ∀ x : {s // s ∈ Tv}, bj x ∈ x.1 ∧ G.Adj v (bj x) ∧ part (bj x) = j := by
      intro x
      exact Classical.choose_spec (exists_color j i hij.symm (by intro w hw; exact (hcover w hw).symm)
        (by simpa [C, Tv] using (Finset.mem_filter.mp x.2).1) (Finset.mem_filter.mp x.2).2)
    let F : {s // s ∈ Tv} → ({u // u ∈ A} × {u // u ∈ B}) := fun x =>
      (⟨ai x, by simp [A, ai_spec x]⟩, ⟨bj x, by simp [B, bj_spec x]⟩)
    have hset : ∀ x : {s // s ∈ Tv}, x.1 = {v, ai x, bj x} := by
      intro x
      have hxcl : x.1 ∈ G.cliqueFinset 3 := by
        simpa [C, Tv] using (Finset.mem_filter.mp x.2).1
      have hxv : v ∈ x.1 := (Finset.mem_filter.mp x.2).2
      have hcard : x.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp hxcl).card_eq
      have hai := ai_spec x
      have hbj := bj_spec x
      have hvi : v ≠ ai x := (hai.2.1).ne
      have hvj : v ≠ bj x := (hbj.2.1).ne
      have hijv : ai x ≠ bj x := by
        intro h
        exact hij (by rw [← hai.2.2, h, hbj.2.2])
      have hsub : {v, ai x, bj x} ⊆ x.1 := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hxv
        · exact hai.1
        · exact hbj.1
      have htriple_card : ({v, ai x, bj x} : Finset V).card = 3 := by
        simp [hvi, hvj, hijv]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, htriple_card])).symm
    have hF_inj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      have h1 : ai x = ai y := congrArg (fun z => z.1.1) hxy
      have h2 : bj x = bj y := congrArg (fun z => z.2.1) hxy
      calc
        x.1 = {v, ai x, bj x} := hset x
        _ = {v, ai y, bj y} := by rw [h1, h2]
        _ = y.1 := (hset y).symm
    have hcard_le : Fintype.card {s // s ∈ Tv} ≤
        Fintype.card ({u // u ∈ A} × {u // u ∈ B}) :=
      Fintype.card_le_of_injective F hF_inj
    have hTv_card : Fintype.card {s // s ∈ Tv} = Tv.card := by
      rw [Fintype.card_subtype]
      simp
    have hA_card : Fintype.card {u // u ∈ A} = A.card := by
      rw [Fintype.card_subtype]
      simp
    have hB_card : Fintype.card {u // u ∈ B} = B.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hTv_card, Fintype.card_prod, hA_card, hB_card] at hcard_le
    simpa [C, Tv, A, B] using hcard_le
  have part_size_sum : ∀ (v : V) (i j : Fin 3), i ≠ j →
      (∀ w, G.Adj v w → part w = i ∨ part w = j) →
      ((G.neighborFinset v).filter (fun u => part u = i)).card +
        ((G.neighborFinset v).filter (fun u => part u = j)).card = G.degree v := by
    intro v i j hij hcover
    let A : Finset V := (G.neighborFinset v).filter (fun u => part u = i)
    let B : Finset V := (G.neighborFinset v).filter (fun u => part u = j)
    have hdis : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      have hxi : part x = i := (Finset.mem_filter.mp hxA).2
      have hxj : part x = j := (Finset.mem_filter.mp hxB).2
      exact hij (hxi ▸ hxj)
    have hunion : A ∪ B = G.neighborFinset v := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_filter.mp hx).1
        · exact (Finset.mem_filter.mp hx).1
      · intro hx
        have hc := hcover x ((SimpleGraph.mem_neighborFinset G v x).mp hx)
        rcases hc with hc | hc
        · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hx, hc⟩)
        · exact Finset.mem_union_right A (Finset.mem_filter.mpr ⟨hx, hc⟩)
    have hcard_union := Finset.card_union_of_disjoint hdis
    rw [hunion, SimpleGraph.card_neighborFinset_eq_degree] at hcard_union
    exact hcard_union.symm
  have product_bound : ∀ p q d : ℕ, p + q = d →
      ((p * q : ℕ) : ℝ) ≤ (1 / 4 : ℝ) * ((d : ℝ) ^ (2 : ℕ)) := by
    intro p q d hsum
    have hsq : (0 : ℝ) ≤ ((p : ℝ) - q) ^ (2 : ℕ) := sq_nonneg _
    have hsumR : (p : ℝ) + q = d := by exact_mod_cast hsum
    have hpq : ((p * q : ℕ) : ℝ) = (p : ℝ) * q := by norm_num
    rw [hpq]
    nlinarith [hsq]
  have vertex_bound_real : ∀ v : V,
      (((C.filter (fun s => v ∈ s)).card : ℝ) ≤
        (1 / 4 : ℝ) * ((G.degree v : ℝ) ^ (2 : ℕ))) := by
    intro v
    generalize hpv : part v = pv
    fin_cases pv
    · have hcover : ∀ w, G.Adj v w → part w = (1 : Fin 3) ∨ part w = (2 : Fin 3) := by
        intro w hw
        have hne : part v ≠ part w := hpart hw
        generalize hpw : part w = pw
        fin_cases pw <;> simp [hpv, hpw] at hne ⊢
      have hnat := vertex_bound_nat v (1 : Fin 3) (2 : Fin 3) (by decide) hcover
      have hsum := part_size_sum v (1 : Fin 3) (2 : Fin 3) (by decide) hcover
      exact le_trans (by exact_mod_cast hnat) (product_bound _ _ _ hsum)
    · have hcover : ∀ w, G.Adj v w → part w = (0 : Fin 3) ∨ part w = (2 : Fin 3) := by
        intro w hw
        have hne : part v ≠ part w := hpart hw
        generalize hpw : part w = pw
        fin_cases pw <;> simp [hpv, hpw] at hne ⊢
      have hnat := vertex_bound_nat v (0 : Fin 3) (2 : Fin 3) (by decide) hcover
      have hsum := part_size_sum v (0 : Fin 3) (2 : Fin 3) (by decide) hcover
      exact le_trans (by exact_mod_cast hnat) (product_bound _ _ _ hsum)
    · have hcover : ∀ w, G.Adj v w → part w = (0 : Fin 3) ∨ part w = (1 : Fin 3) := by
        intro w hw
        have hne : part v ≠ part w := hpart hw
        generalize hpw : part w = pw
        fin_cases pw <;> simp [hpv, hpw] at hne ⊢
      have hnat := vertex_bound_nat v (0 : Fin 3) (1 : Fin 3) (by decide) hcover
      have hsum := part_size_sum v (0 : Fin 3) (1 : Fin 3) (by decide) hcover
      exact le_trans (by exact_mod_cast hnat) (product_bound _ _ _ hsum)
  have incidence_sum : (∑ v : V, (C.filter fun s => v ∈ s).card) = C.card * 3 := by
    calc
      (∑ v : V, (C.filter fun s => v ∈ s).card)
          = ∑ s ∈ C, s.card := by
            calc
              (∑ v : V, (C.filter fun s => v ∈ s).card)
                  = ∑ v : V, ∑ s ∈ C, if v ∈ s then (1 : ℕ) else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro v hv
                    exact (Finset.sum_boole (R := ℕ) (fun s => v ∈ s) C).symm
              _ = ∑ s ∈ C, ∑ v : V, if v ∈ s then (1 : ℕ) else 0 := by
                    rw [Finset.sum_comm]
              _ = ∑ s ∈ C, s.card := by
                    refine Finset.sum_congr rfl ?_
                    intro s hs
                    rw [Finset.sum_boole (R := ℕ) (fun v => v ∈ s) Finset.univ]
                    simp
      _ = C.card * 3 := by
            exact Finset.sum_const_nat (s := C) (m := 3) (f := fun s => s.card)
              (by intro s hs; exact (SimpleGraph.mem_cliqueFinset_iff.mp (by simpa [C] using hs)).card_eq)
  have hsum_real : (∑ v : V, (((C.filter fun s => v ∈ s).card : ℝ))) ≤
      ∑ v : V, ((1 / 4 : ℝ) * ((G.degree v : ℝ) ^ (2 : ℕ))) := by
    exact Finset.sum_le_sum (by intro v _hv; exact vertex_bound_real v)
  have hdouble_real : (3 : ℝ) * (C.card : ℝ) =
      ∑ v : V, (((C.filter fun s => v ∈ s).card : ℝ)) := by
    have hcast :
        ((∑ v : V, (C.filter fun s => v ∈ s).card : ℕ) : ℝ) =
          ((C.card * 3 : ℕ) : ℝ) := by
      exact_mod_cast incidence_sum
    rw [Nat.cast_sum, Nat.cast_mul] at hcast
    norm_num at hcast
    calc
      (3 : ℝ) * (C.card : ℝ) = (C.card : ℝ) * 3 := by ring
      _ = ∑ v : V, (((C.filter fun s => v ∈ s).card : ℝ)) := hcast.symm
  calc
    (C.card : ℝ) = (1 / 3 : ℝ) * ((3 : ℝ) * (C.card : ℝ)) := by ring_nf
    _ = (1 / 3 : ℝ) * (∑ v : V, (((C.filter fun s => v ∈ s).card : ℝ))) := by
      rw [hdouble_real]
    _ ≤ (1 / 3 : ℝ) * (∑ v : V, ((1 / 4 : ℝ) * ((G.degree v : ℝ) ^ (2 : ℕ)))) := by
      exact mul_le_mul_of_nonneg_left hsum_real (by norm_num)
    _ = (1 / 12 : ℝ) * ∑ v : V, ((G.degree v : ℝ) ^ (2 : ℕ)) := by
      calc
        (1 / 3 : ℝ) * (∑ v : V, ((1 / 4 : ℝ) * ((G.degree v : ℝ) ^ (2 : ℕ))))
            = ∑ v : V, ((1 / 12 : ℝ) * ((G.degree v : ℝ) ^ (2 : ℕ))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro v _hv
              ring
        _ = (1 / 12 : ℝ) * ∑ v : V, ((G.degree v : ℝ) ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
