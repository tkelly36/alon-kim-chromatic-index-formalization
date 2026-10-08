import Tablet.IndependentPairCount
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option maxHeartbeats 800000

-- [TABLET NODE: NeighborhoodComplementEdgeCountLeIndependentPairCount]
theorem NeighborhoodComplementEdgeCountLeIndependentPairCount :
    ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj], ∀ v : V,
        ∀ C : SimpleGraph {u : V // u ∈ G.neighborFinset v}, ∀ [DecidableRel C.Adj],
          (∀ x y, C.Adj x y ↔ x ≠ y ∧ ¬ G.Adj x.1 y.1) →
        C.edgeFinset.card ≤ IndependentPairCount G v := by
-- BODY
  classical
  intro V _ _ G _ v C _ hC
  have sym2_toFinset_inj_on_edges :
      Set.InjOn (fun e : Sym2 {u : V // u ∈ G.neighborFinset v} => e.toFinset)
        ↑C.edgeFinset := by
    intro e he e' he' h
    have hene : ¬ e.IsDiag := C.not_isDiag_of_mem_edgeFinset he
    have he'ne : ¬ e'.IsDiag := C.not_isDiag_of_mem_edgeFinset he'
    induction e using Sym2.ind with
    | h a b =>
      induction e' using Sym2.ind with
      | h c d =>
        rw [Sym2.mk_isDiag_iff] at hene he'ne
        rw [Sym2.eq_iff]
        have hac_or_had : a = c ∨ a = d := by
          have ha_mem : a ∈ (Sym2.mk c d).toFinset := by
            change a ∈
              (fun e : Sym2 {u : V // u ∈ G.neighborFinset v} => e.toFinset)
                (Sym2.mk c d)
            rw [← h]
            simp [Sym2.mem_toFinset]
          simpa [Sym2.mem_toFinset, Sym2.mem_iff] using ha_mem
        have hbc_or_hbd : b = c ∨ b = d := by
          have hb_mem : b ∈ (Sym2.mk c d).toFinset := by
            change b ∈
              (fun e : Sym2 {u : V // u ∈ G.neighborFinset v} => e.toFinset)
                (Sym2.mk c d)
            rw [← h]
            simp [Sym2.mem_toFinset]
          simpa [Sym2.mem_toFinset, Sym2.mem_iff] using hb_mem
        rcases hac_or_had with rfl | rfl
        · rcases hbc_or_hbd with hbc | hbd
          · exact (hene hbc.symm).elim
          · exact Or.inl ⟨rfl, hbd⟩
        · rcases hbc_or_hbd with hbc | hbd
          · exact Or.inr ⟨rfl, hbc⟩
          · exact (hene hbd.symm).elim
  unfold IndependentPairCount
  let toSet : Sym2 {u : V // u ∈ G.neighborFinset v} → Finset V := fun e =>
    e.toFinset.image Subtype.val
  have hmaps :
      ∀ e ∈ C.edgeFinset,
        toSet e ∈ (Finset.univ : Finset (Finset V)).filter (fun S =>
          S.card = 2 ∧ S ⊆ G.neighborFinset v ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hcard : (toSet e).card = 2 := by
      dsimp [toSet]
      have himage : (Finset.image Subtype.val e.toFinset).card = e.toFinset.card := by
        rw [Finset.card_image_iff]
        intro x _ y _ hxy
        exact Subtype.ext hxy
      rw [himage]
      exact SimpleGraph.card_toFinset_mem_edgeFinset (G := C) ⟨e, he⟩
    refine ⟨hcard, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
      exact a.2
    · intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      have hne : a ≠ b := by
        intro hab
        exact hxy (congrArg Subtype.val hab)
      have hedge : C.Adj a b := by
        have heEdge : e ∈ C.edgeSet := SimpleGraph.mem_edgeFinset.mp he
        have ha0 : a ∈ e.toFinset := ha
        have hb0 : b ∈ e.toFinset := hb
        induction e using Sym2.ind with
        | h p q =>
          rw [SimpleGraph.mem_edgeSet] at heEdge
          have ha' : a = p ∨ a = q := by
            simpa [Sym2.mem_toFinset, Sym2.mem_iff] using ha0
          have hb' : b = p ∨ b = q := by
            simpa [Sym2.mem_toFinset, Sym2.mem_iff] using hb0
          rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
          · exact (hne rfl).elim
          · exact heEdge
          · exact C.symm heEdge
          · exact (hne rfl).elim
      exact ((hC a b).mp hedge).2
  refine Finset.card_le_card_of_injOn (fun e => toSet e) hmaps ?_
  intro e he e' he' h
  apply sym2_toFinset_inj_on_edges
  · exact he
  · exact he'
  · dsimp [toSet] at h
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hx_image : (x : V) ∈ toSet e := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      change (x : V) ∈ Finset.image Subtype.val e.toFinset at hx_image
      rw [h] at hx_image
      rcases Finset.mem_image.mp hx_image with ⟨y, hy, hval⟩
      have hxy : x = y := Subtype.ext hval.symm
      simpa [hxy] using hy
    · intro hx
      have hx_image : (x : V) ∈ toSet e' := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      change (x : V) ∈ Finset.image Subtype.val e'.toFinset at hx_image
      rw [← h] at hx_image
      rcases Finset.mem_image.mp hx_image with ⟨y, hy, hval⟩
      have hxy : x = y := Subtype.ext hval.symm
      simpa [hxy] using hy
