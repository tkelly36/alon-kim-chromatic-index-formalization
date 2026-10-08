import Tablet.Preamble
import Tablet.KPartiteTriangleDistinctParts

open scoped BigOperators

-- [TABLET NODE: KPartiteTriangleFibreBridge]
theorem KPartiteTriangleFibreBridge :
    ∀ k : ℕ, 0 < k →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
          ∀ part : V → Fin k,
            (∀ ⦃u v : V⦄, G.Adj u v → part u ≠ part v) →
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
-- BODY
  intro k hk V _ _ G _ part hpart
  classical
  let T : Finset (Finset V) :=
    (Finset.univ.filter
      (fun s =>
        s.card = 3 ∧
          ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v))
  let triples : Finset (Fin k × Fin k × Fin k) :=
    (Finset.univ.filter (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
  let A : Fin k → Finset V := fun i => (Finset.univ.filter (fun v => part v = i))
  let triSet : Fin k × Fin k × Fin k → Finset (V × V × V) := fun t =>
    ((A t.1).product ((A t.2.1).product (A t.2.2))).filter
      (fun x => G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2)
  let C := Σ t : {t : Fin k × Fin k × Fin k // t ∈ triples}, {x : V × V × V // x ∈ triSet t.1}
  let H : C → {s : Finset V // s ∈ T} := fun y =>
    let t := y.1.1
    let x := y.2.1
    let S : Finset V := {x.1, x.2.1, x.2.2}
    have hxmem : x ∈ triSet t := y.2.2
    have htmem : t ∈ triples := y.1.2
    have htlt : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
      simpa [triples] using htmem
    have hprod : x ∈ (A t.1).product ((A t.2.1).product (A t.2.2)) :=
      (Finset.mem_filter.mp hxmem).1
    have hadj : G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 :=
      (Finset.mem_filter.mp hxmem).2
    have hA : x.1 ∈ A t.1 := (Finset.mem_product.mp hprod).1
    have hBC : x.2 ∈ (A t.2.1).product (A t.2.2) := (Finset.mem_product.mp hprod).2
    have hB : x.2.1 ∈ A t.2.1 := (Finset.mem_product.mp hBC).1
    have hC : x.2.2 ∈ A t.2.2 := (Finset.mem_product.mp hBC).2
    have hpa : part x.1 = t.1 := by simpa [A] using hA
    have hpb : part x.2.1 = t.2.1 := by simpa [A] using hB
    have hpc : part x.2.2 = t.2.2 := by simpa [A] using hC
    have hab_ne : x.1 ≠ x.2.1 := by
      intro h
      have : t.1 = t.2.1 := by
        rw [← hpa, h, hpb]
      exact (ne_of_lt htlt.1) this
    have hac_ne : x.1 ≠ x.2.2 := by
      intro h
      have : t.1 = t.2.2 := by
        rw [← hpa, h, hpc]
      exact (ne_of_lt (lt_trans htlt.1 htlt.2)) this
    have hbc_ne : x.2.1 ≠ x.2.2 := by
      intro h
      have : t.2.1 = t.2.2 := by
        rw [← hpb, h, hpc]
      exact (ne_of_lt htlt.2) this
    have hS_card : S.card = 3 := by
      simp [S, hab_ne, hac_ne, hbc_ne]
    have hS_clique :
        ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → G.Adj u v := by
      intro u hu v hv huv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · contradiction
      · exact hadj.1
      · exact hadj.2.1
      · exact G.symm hadj.1
      · contradiction
      · exact hadj.2.2
      · exact G.symm hadj.2.1
      · exact G.symm hadj.2.2
      · contradiction
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, ⟨hS_card, hS_clique⟩⟩⟩
  have hH_surj : Function.Surjective H := by
    intro s
    let hsT : s.1 ∈ T := s.2
    let hs_card : s.1.card = 3 := (Finset.mem_filter.mp hsT).2.1
    let hs_clique :
        ∀ ⦃u⦄, u ∈ s.1 → ∀ ⦃v⦄, v ∈ s.1 → u ≠ v → G.Adj u v :=
      (Finset.mem_filter.mp hsT).2.2
    let P : Finset (Fin k) := s.1.image part
    let hP_card : P.card = 3 :=
      KPartiteTriangleDistinctParts k hk G part hpart s.1 hs_card hs_clique
    let e : Fin 3 ↪o Fin k := P.orderEmbOfFin hP_card
    let i : Fin k := e 0
    let j : Fin k := e 1
    let l : Fin k := e 2
    let hltij : i < j := e.strictMono (by decide : (0 : Fin 3) < 1)
    let hltjl : j < l := e.strictMono (by decide : (1 : Fin 3) < 2)
    let htmem : (i, j, l) ∈ triples := by
      simp [triples, hltij, hltjl]
    let chooseVertex : (r : Fin 3) → {v : V // v ∈ s.1 ∧ part v = e r} := fun r =>
      let hmemP : e r ∈ P := P.orderEmbOfFin_mem hP_card r
      let hex : ∃ v, v ∈ s.1 ∧ part v = e r := by
        simpa [P] using hmemP
      ⟨Classical.choose hex, Classical.choose_spec hex⟩
    let a : V := chooseVertex 0
    let b : V := chooseVertex 1
    let c : V := chooseVertex 2
    let hxmem : (a, b, c) ∈ triSet (i, j, l) := by
      have ha := (chooseVertex 0).2
      have hb := (chooseVertex 1).2
      have hc := (chooseVertex 2).2
      have hab_ne : a ≠ b := by
        intro hab
        have : i = j := by
          calc
            i = part a := by exact ha.2.symm
            _ = part b := by exact congrArg part hab
            _ = j := by exact hb.2
        exact (ne_of_lt hltij) this
      have hac_ne : a ≠ c := by
        intro hac
        have hlt_il : i < l := lt_trans hltij hltjl
        have : i = l := by
          calc
            i = part a := by exact ha.2.symm
            _ = part c := by exact congrArg part hac
            _ = l := by exact hc.2
        exact (ne_of_lt hlt_il) this
      have hbc_ne : b ≠ c := by
        intro hbc
        have : j = l := by
          calc
            j = part b := by exact hb.2.symm
            _ = part c := by exact congrArg part hbc
            _ = l := by exact hc.2
        exact (ne_of_lt hltjl) this
      have hadj_ab : G.Adj a b := hs_clique ha.1 hb.1 hab_ne
      have hadj_ac : G.Adj a c := hs_clique ha.1 hc.1 hac_ne
      have hadj_bc : G.Adj b c := hs_clique hb.1 hc.1 hbc_ne
      simp [triSet, A, a, b, c, i, j, l, ha.2, hb.2, hc.2, hadj_ab, hadj_ac, hadj_bc]
    refine ⟨⟨⟨(i, j, l), htmem⟩, ⟨(a, b, c), hxmem⟩⟩, ?_⟩
    apply Subtype.ext
    dsimp [H]
    have ha := (chooseVertex 0).2
    have hb := (chooseVertex 1).2
    have hc := (chooseVertex 2).2
    have hab_ne : a ≠ b := by
      intro hab
      have : i = j := by
        calc
          i = part a := by exact ha.2.symm
          _ = part b := by exact congrArg part hab
          _ = j := by exact hb.2
      exact (ne_of_lt hltij) this
    have hac_ne : a ≠ c := by
      intro hac
      have hlt_il : i < l := lt_trans hltij hltjl
      have : i = l := by
        calc
          i = part a := by exact ha.2.symm
          _ = part c := by exact congrArg part hac
          _ = l := by exact hc.2
      exact (ne_of_lt hlt_il) this
    have hbc_ne : b ≠ c := by
      intro hbc
      have : j = l := by
        calc
          j = part b := by exact hb.2.symm
          _ = part c := by exact congrArg part hbc
          _ = l := by exact hc.2
      exact (ne_of_lt hltjl) this
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ha.1
      · exact hb.1
      · exact hc.1
    · simp [hs_card, hab_ne, hac_ne, hbc_ne]
  have hcard_le : Fintype.card {s : Finset V // s ∈ T} ≤ Fintype.card C :=
    Fintype.card_le_of_surjective H hH_surj
  rw [Fintype.card_subtype] at hcard_le
  have hC :
      Fintype.card C = triples.sum (fun t => (triSet t).card) := by
    dsimp [C]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_subtype]
    simpa [Finset.univ_eq_attach] using Finset.sum_attach triples (fun t => (triSet t).card)
  simpa [T, triples, A, triSet] using hcard_le.trans_eq hC
