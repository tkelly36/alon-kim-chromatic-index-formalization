import Tablet.LocalBParameter

-- [TABLET NODE: NibbleInducedBParameterComparison]
theorem NibbleInducedBParameterComparison {E : Type*} [Fintype E] [DecidableEq E]
    (G : SimpleGraph E) [DecidableRel G.Adj] (Delta : ℕ)
    (hDelta : 0 < Delta) (s : Finset E) (r : s)
    (hd : G.degree r.val ≤ Delta) :
    letI : DecidableRel (G.induce (s : Set E)).Adj := Classical.decRel _
    LocalBParameter (G.induce (s : Set E)) Delta r ≤ LocalBParameter G Delta r.val := by
-- BODY
  classical
  let H := G.induce (s : Set E)
  letI : DecidableRel H.Adj := Classical.decRel _
  let emb : s ↪ E := Function.Embedding.subtype _
  let N := G.neighborFinset r.val
  let R := N \ s
  let A (n : ℕ) := (Finset.univ : Finset (Finset E)).filter (fun t =>
    t.card = n ∧ t ⊆ N ∧
      ∀ ⦃x⦄, x ∈ t → ∀ ⦃y⦄, y ∈ t → x ≠ y → ¬ G.Adj x y)
  let B (n : ℕ) := (Finset.univ : Finset (Finset s)).filter (fun t =>
    t.card = n ∧ t ⊆ H.neighborFinset r ∧
      ∀ ⦃x⦄, x ∈ t → ∀ ⦃y⦄, y ∈ t → x ≠ y → ¬ H.Adj x y)
  have transport (n : ℕ) (t : Finset s) :
      t ∈ B n ↔ t.map emb ∈ A n := by
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.card_map]
    constructor
    · rintro ⟨hc, hn, hi⟩
      refine ⟨hc, ?_, ?_⟩
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        exact (SimpleGraph.mem_neighborFinset G r.val a.val).mpr
          ((SimpleGraph.mem_neighborFinset H r a).mp (hn ha))
      · intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
        exact hi ha hb (fun h => hxy (congrArg emb h))
    · rintro ⟨hc, hn, hi⟩
      refine ⟨hc, ?_, ?_⟩
      · intro x hx
        exact (SimpleGraph.mem_neighborFinset H r x).mpr
          ((SimpleGraph.mem_neighborFinset G r.val x.val).mp
            (hn (Finset.mem_map.mpr ⟨x, hx, rfl⟩)))
      · intro x hx y hy hxy
        exact hi (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
          (Finset.mem_map.mpr ⟨y, hy, rfl⟩) (fun h => hxy (emb.injective h))
  have retained (n : ℕ) :
      (B n).image (Finset.map emb) = (A n).filter (fun t => t ⊆ s) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(transport n u).mp hu, ?_⟩
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      exact a.property
    · rintro ⟨ht, hs⟩
      let u := t.subtype (fun x => x ∈ s)
      have hu : u.map emb = t := Finset.subtype_map_of_mem hs
      exact ⟨u, (transport n u).mpr (hu.symm ▸ ht), hu⟩
  have retained_card (n : ℕ) :
      ((A n).filter (fun t => t ⊆ s)).card = (B n).card := by
    rw [← retained n, Finset.card_image_of_injective _ (Finset.map_injective emb)]
  have triples : (B 3).card ≤ (A 3).card := by
    rw [← retained_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have degree_map : (H.neighborFinset r).map emb = N ∩ s := by
    ext x
    simp only [N, Finset.mem_map, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.property⟩
    · rintro ⟨ha, hs⟩
      exact ⟨⟨x, hs⟩, ha, rfl⟩
  have degrees : H.degree r + R.card = G.degree r.val := by
    have hc := Finset.card_sdiff_add_card_inter N s
    have hm := congrArg Finset.card degree_map
    simp only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at hm
    change H.degree r + (N \ s).card = N.card
    omega
  let lost := (A 2).filter (fun t => ¬ t ⊆ s)
  have lost_cover : lost ⊆ (R.product N).image (fun p : E × E => {p.1, p.2}) := by
    intro t ht
    obtain ⟨ht, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨hc, hn, hi⟩ := (Finset.mem_filter.mp ht).2
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have hx : x ∈ N := hn (by simp)
    have hy : y ∈ N := hn (by simp)
    by_cases hxs : x ∈ s
    · have hys : y ∉ s := by
        intro hys
        exact hs (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                     rcases hz with rfl | rfl <;> assumption)
      apply Finset.mem_image.mpr
      refine ⟨(y, x), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hy, hys⟩, hx⟩, ?_⟩
      exact Finset.pair_comm y x
    · exact Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, hxs⟩, hy⟩, rfl⟩
  have lost_bound : lost.card ≤ R.card * Delta := by
    calc
      lost.card ≤ ((R.product N).image (fun p : E × E => {p.1, p.2})).card :=
        Finset.card_le_card lost_cover
      _ ≤ (R.product N).card := Finset.card_image_le
      _ = R.card * N.card := Finset.card_product _ _
      _ ≤ R.card * Delta := Nat.mul_le_mul_left _ hd
  have pairs : (A 2).card ≤ (B 2).card + R.card * Delta := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card
      (s := A 2) (p := fun t => t ⊆ s)
    rw [retained_card] at hc
    change (B 2).card + lost.card = (A 2).card at hc
    omega
  have hp : (IndependentPairCount G r.val : ℝ) ≤
      (IndependentPairCount H r : ℝ) + (R.card : ℝ) * Delta := by
    exact_mod_cast pairs
  have ht : (IndependentTripleCount H r : ℝ) ≤
      (IndependentTripleCount G r.val : ℝ) := by exact_mod_cast triples
  have hdeg : (H.degree r : ℝ) + (R.card : ℝ) = G.degree r.val := by
    exact_mod_cast degrees
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  change LocalBParameter H Delta r ≤ LocalBParameter G Delta r.val
  unfold LocalBParameter
  rw [← hdeg]
  apply (mul_le_mul_iff_left₀ (pow_pos hD 3)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hp hD.le]
