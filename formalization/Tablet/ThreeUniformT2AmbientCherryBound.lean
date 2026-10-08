import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.TriangleCountTripartiteCherries

open scoped BigOperators

-- [TABLET NODE: ThreeUniformT2AmbientCherryBound]
theorem ThreeUniformT2AmbientCherryBound
    (D : ℕ) {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E) (S : ThreeUniformThreeSimpleLocalSetup D F f) :
    let N := (Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
    let q := fun g => ((N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card : ℝ)
    S.T2 ≤ (1 / 12 : ℝ) * ∑ g ∈ S.V2, q g ^ 2 := by
-- BODY
  classical
  dsimp only
  let N := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  have hsub : S.V2 ⊆ N := by
    intro g hg
    rw [S.V2_eq] at hg
    exact (Finset.mem_sdiff.mp hg).1
  let U := {g // g ∈ S.V2}
  let G : SimpleGraph U := {
    Adj := fun g h => Disjoint (F.edge g.val) (F.edge h.val)
    symm := fun _ _ h => h.symm
    loopless := by
      constructor
      intro g h
      have he : F.edge g.val = ∅ := disjoint_self.mp h
      have hc := S.class_mem.1 g.val
      rw [he] at hc
      simp at hc }
  letI : DecidableRel G.Adj := Classical.decRel _
  have hchoose (g : U) : ∃ v : V, v ∈ F.edge g.val ∧ v ∈ F.edge f := by
    have hc := (S.V2_edge_shape g.val g.property).1
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (F.edge g.val ∩ F.edge f).card by omega)
    exact ⟨v, Finset.mem_inter.mp hv⟩
  let vertex (g : U) : {v // v ∈ F.edge f} :=
    ⟨(hchoose g).choose, (hchoose g).choose_spec.2⟩
  have hv (g : U) : (vertex g).val ∈ F.edge g.val := (hchoose g).choose_spec.1
  have hfcard : Fintype.card {v // v ∈ F.edge f} = 3 := by
    simpa using S.class_mem.1 f
  let label := Fintype.equivFinOfCardEq hfcard
  have htrip : ∃ part : U → Fin 3, ∀ ⦃g h⦄, G.Adj g h → part g ≠ part h := by
    refine ⟨fun g => label (vertex g), ?_⟩
    intro g h hgh heq
    have he := congrArg Subtype.val (label.injective heq)
    exact Finset.disjoint_left.mp hgh (hv g) (he ▸ hv h)
  let A := (Finset.univ : Finset (Finset U)).filter (fun t =>
    t.card = 3 ∧ ∀ ⦃g⦄, g ∈ t → ∀ ⦃h⦄, h ∈ t → g ≠ h → G.Adj g h)
  let B := (Finset.univ : Finset (Finset E)).filter (fun t =>
    t.card = 3 ∧ t ⊆ N ∧
      (∀ ⦃g⦄, g ∈ t → ∀ ⦃h⦄, h ∈ t → g ≠ h →
        ¬ (g ≠ h ∧ (F.edge g ∩ F.edge h).Nonempty)) ∧ t ⊆ S.V2)
  have hdis (g h : E) : Disjoint (F.edge g) (F.edge h) ↔
      ¬ (F.edge g ∩ F.edge h).Nonempty := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.not_nonempty_iff_eq_empty]
  have hcard : A.card = B.card := by
    apply Finset.card_bij (fun t _ => t.image (Subtype.val : U → E))
    · intro t ht
      obtain ⟨htc, htadj⟩ := (Finset.mem_filter.mp ht).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
      · simpa [Finset.card_image_of_injective _ Subtype.val_injective] using htc
      · intro g hg
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg
        exact hsub g.property
      · intro g hg h hh hne hn
        obtain ⟨gg, hgg, eg⟩ := Finset.mem_image.mp hg
        obtain ⟨hh', hhh, eh⟩ := Finset.mem_image.mp hh
        subst g h
        exact (hdis _ _).mp (htadj hgg hhh (fun he => hne (congrArg Subtype.val he))) hn.2
      · intro g hg
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg
        exact g.property
    · intro t ht u hu he
      exact Finset.image_injective Subtype.val_injective he
    · intro t ht
      obtain ⟨htc, htn, htadj, htv⟩ := (Finset.mem_filter.mp ht).2
      let u : Finset U := Finset.univ.filter (fun g => g.val ∈ t)
      have himage : u.image (Subtype.val : U → E) = t := by
        ext g
        simp only [Finset.mem_image, u, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact hg
        · intro hg
          exact ⟨⟨g, htv hg⟩, hg, rfl⟩
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, himage⟩
      · rw [← htc, ← himage, Finset.card_image_of_injective _ Subtype.val_injective]
      · intro g hg h hh hne
        apply (hdis _ _).mpr
        intro hn
        exact htadj (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hh).2
          (fun he => hne (Subtype.ext he)) ⟨(fun he => hne (Subtype.ext he)), hn⟩
  have hT : S.T2 = (A.card : ℝ) := by
    rw [hcard]
    exact S.T2_is_triangle_count_inside_V2
  have hdeg (g : U) : G.degree g ≤
      (N.filter (fun h => Disjoint (F.edge g.val) (F.edge h))).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card_of_injOn (fun h : U => h.val)
    · intro h hh
      exact Finset.mem_filter.mpr ⟨hsub h.property,
        (SimpleGraph.mem_neighborFinset G g h).mp hh⟩
    · intro h hh i hi he
      exact Subtype.ext he
  have hsum : (∑ g : U, (G.degree g : ℝ) ^ 2) ≤
      ∑ g ∈ S.V2, ((N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card : ℝ) ^ 2 := by
    rw [← Finset.sum_attach S.V2]
    change (∑ g ∈ S.V2.attach, (G.degree g : ℝ) ^ 2) ≤ _
    apply Finset.sum_le_sum
    intro g hg
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast hdeg g
  rw [hT]
  exact (TriangleCountTripartiteCherries G htrip).trans
    (mul_le_mul_of_nonneg_left hsum (by norm_num))
