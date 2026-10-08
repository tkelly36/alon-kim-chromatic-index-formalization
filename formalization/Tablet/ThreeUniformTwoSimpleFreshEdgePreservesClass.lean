import Tablet.KUniformFreshEdgePreservesClass

-- [TABLET NODE: ThreeUniformTwoSimpleFreshEdgePreservesClass]
theorem ThreeUniformTwoSimpleFreshEdgePreservesClass
    {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (D : ℕ) (H : MultiHypergraph V E)
    (hH : H ∈ HypergraphClass (V := V) (E := E) 3 2 D)
    (v : V) (hv : HypergraphDegree H v < D) :
    KUniformFreshEdgeHypergraph 3 H v ∈
      HypergraphClass (V := V ⊕ Fin (3 - 1)) (E := E ⊕ Unit) 3 2 D := by
-- BODY
  classical
  have hweak : H ∈ HypergraphClass (V := V) (E := E) 3 3 D :=
    ⟨hH.1, fun _ _ h => le_trans (hH.2.1 h) (by decide), hH.2.2⟩
  have hc := KUniformFreshEdgePreservesClass 3 D (by decide) H hweak v hv
  refine ⟨hc.1, ?_, hc.2.2⟩
  intro e f hef
  have hold (a b : E) (hab : a ≠ b) :
      (((H.edge a).image (Sum.inl : V → V ⊕ Fin (3 - 1))) ∩
        (H.edge b).image Sum.inl).card ≤ 2 := by
    rw [← Finset.image_inter (H.edge a) (H.edge b) Sum.inl_injective]
    simpa only [Finset.card_image_of_injective _ Sum.inl_injective] using hH.2.1 hab
  have hfresh (a : E) (u : Unit) :
      ((KUniformFreshEdgeHypergraph 3 H v).edge (Sum.inl a) ∩
        (KUniformFreshEdgeHypergraph 3 H v).edge (Sum.inr u)).card ≤ 2 := by
    have hs : ((KUniformFreshEdgeHypergraph 3 H v).edge (Sum.inl a) ∩
        (KUniformFreshEdgeHypergraph 3 H v).edge (Sum.inr u)) ⊆ {Sum.inl v} := by
      intro x hx
      obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      simpa [KUniformFreshEdgeHypergraph] using hy
    exact le_trans (Finset.card_le_card hs) (by simp)
  cases e with
  | inl a =>
    cases f with
    | inl b => exact hold a b (fun h => hef (congrArg Sum.inl h))
    | inr u => exact hfresh a u
  | inr u =>
    cases f with
    | inl b => simpa only [Finset.inter_comm] using hfresh b u
    | inr w => exact False.elim (hef (by congr))
