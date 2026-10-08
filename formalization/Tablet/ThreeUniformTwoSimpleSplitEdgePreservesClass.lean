import Tablet.KUniformSplitEdgePreservesClass

-- [TABLET NODE: ThreeUniformTwoSimpleSplitEdgePreservesClass]
theorem ThreeUniformTwoSimpleSplitEdgePreservesClass
    {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (D : ℕ) (hD : 2 ≤ D) (H : MultiHypergraph V E)
    (hH : H ∈ HypergraphClass (V := V) (E := E) 3 2 D)
    (g : E) (v : V) (hv : v ∈ H.edge g) (x1 : Fin (3 - 1)) :
    KUniformSplitEdgeHypergraph 3 H g v hv x1 ∈
      HypergraphClass (V := V ⊕ Fin (3 - 1)) (E := E ⊕ Unit) 3 2 D := by
-- BODY
  classical
  have hweak : H ∈ HypergraphClass (V := V) (E := E) 3 3 D :=
    ⟨hH.1, fun _ _ h => le_trans (hH.2.1 h) (by decide), hH.2.2⟩
  have hc := KUniformSplitEdgePreservesClass 3 D hD H hweak g v hv x1
  refine ⟨hc.1, ?_, hc.2.2⟩
  let K := KUniformSplitEdgeHypergraph 3 H g v hv x1
  have hold (a b : E) (hab : a ≠ b) (hb : b ≠ g) :
      (K.edge (Sum.inl a) ∩ K.edge (Sum.inl b)).card ≤ 2 := by
    have hs : K.edge (Sum.inl a) ∩ K.edge (Sum.inl b) ⊆
        (H.edge a ∩ H.edge b).image (Sum.inl : V → V ⊕ Fin (3 - 1)) := by
      intro x hx
      obtain ⟨ha, hxb⟩ := Finset.mem_inter.mp hx
      have hxb' : x ∈ (H.edge b).image Sum.inl := by
        simpa [K, KUniformSplitEdgeHypergraph, hb] using hxb
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxb'
      have hwa : w ∈ H.edge a := by
        by_cases hag : a = g
        · subst a
          have hwg : w ≠ v ∧ w ∈ H.edge g := by
            simpa [K, KUniformSplitEdgeHypergraph] using ha
          exact hwg.2
        · simpa [K, KUniformSplitEdgeHypergraph, hag] using ha
      exact Finset.mem_image.mpr ⟨w, Finset.mem_inter.mpr ⟨hwa, hw⟩, rfl⟩
    calc
      _ ≤ ((H.edge a ∩ H.edge b).image (Sum.inl : V → V ⊕ Fin (3 - 1))).card :=
        Finset.card_le_card hs
      _ = (H.edge a ∩ H.edge b).card := Finset.card_image_of_injective _ Sum.inl_injective
      _ ≤ 2 := hH.2.1 hab
  have hfresh (a : E) (u : Unit) :
      (K.edge (Sum.inl a) ∩ K.edge (Sum.inr u)).card ≤ 2 := by
    have hs : K.edge (Sum.inl a) ∩ K.edge (Sum.inr u) ⊆
        ({Sum.inl v, Sum.inr x1} : Finset (V ⊕ Fin (3 - 1))) := by
      intro x hx
      obtain ⟨ha, hn⟩ := Finset.mem_inter.mp hx
      cases x with
      | inl w =>
        have hw : w = v := by simpa [K, KUniformSplitEdgeHypergraph] using hn
        simp [hw]
      | inr y =>
        by_cases hag : a = g
        · subst a
          have hy : y = x1 := by simpa [K, KUniformSplitEdgeHypergraph] using ha
          simp [hy]
        · simp [K, KUniformSplitEdgeHypergraph, hag] at ha
    exact le_trans (Finset.card_le_card hs) (by simp)
  intro e f hef
  change (K.edge e ∩ K.edge f).card ≤ 2
  cases e with
  | inl a =>
    cases f with
    | inl b =>
      have hab : a ≠ b := fun h => hef (congrArg Sum.inl h)
      by_cases hb : b = g
      · subst b
        simpa only [Finset.inter_comm] using hold g a hab.symm hab
      · exact hold a b hab hb
    | inr u => exact hfresh a u
  | inr u =>
    cases f with
    | inl b => simpa only [Finset.inter_comm] using hfresh b u
    | inr w => exact False.elim (hef (by congr))
