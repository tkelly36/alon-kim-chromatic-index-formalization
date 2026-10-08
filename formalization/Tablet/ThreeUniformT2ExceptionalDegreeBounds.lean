import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.SaturatedLineGraphEdgeCount

open scoped BigOperators

-- [TABLET NODE: ThreeUniformT2ExceptionalDegreeBounds]
theorem ThreeUniformT2ExceptionalDegreeBounds
    (D : ℕ) {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E) (S : ThreeUniformThreeSimpleLocalSetup D F f) :
    let N := (Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
    let q := fun g => ((N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card : ℝ)
    let y := fun g => ((N.filter (fun h =>
      F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
      (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card : ℝ)
    (∀ g ∈ S.V2, 0 ≤ q g ∧ q g ≤ 2 * (D : ℝ) ∧
      q g ≤ 2 * (D : ℝ) - S.crossDegree g + y g) ∧
    (∀ g ∈ S.V2, 0 ≤ y g) ∧ (∑ g ∈ S.V2, y g) ≤ 2 * S.Y := by
-- BODY
  classical
  dsimp only
  let N := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  let C := fun v : V => (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ v ∈ F.edge g)
  have hu : UniformHypergraph F 3 := S.class_mem.1
  obtain ⟨hC, hdisj, hcover, hone⟩ :=
    SaturatedNeighborClassPartition F f 3 D hu S.class_mem.2.2 S.saturated_neighbors
  have hrows (g : E) (hg : g ∈ S.V2) : (F.edge f \ F.edge g).card = 2 := by
    rw [Finset.card_sdiff, hu f, (S.V2_edge_shape g hg).1]
  have hq (g : E) (hg : g ∈ S.V2) :
      ((N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card : ℝ) ≤
        2 * (D : ℝ) := by
    have hsub : N.filter (fun h => Disjoint (F.edge g) (F.edge h)) ⊆
        (F.edge f \ F.edge g).biUnion C := by
      intro h hh
      obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hh
      obtain ⟨hne, v, hv⟩ := (Finset.mem_filter.mp hn).2
      obtain ⟨hvh, hvf⟩ := Finset.mem_inter.mp hv
      have hvg : v ∉ F.edge g := fun hvg => Finset.disjoint_left.mp hd hvg hvh
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvf, hvg⟩,
        by simp [C, hne, hvh]⟩
    have hcount : (N.filter (fun h => Disjoint (F.edge g) (F.edge h))).card ≤
        2 * (D - 1) := calc
      _ ≤ ((F.edge f \ F.edge g).biUnion C).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ F.edge f \ F.edge g, (C v).card := Finset.card_biUnion_le
      _ = ∑ v ∈ F.edge f \ F.edge g, (D - 1) :=
        Finset.sum_congr rfl (fun v hv => hC v (Finset.mem_sdiff.mp hv).1)
      _ = 2 * (D - 1) := by simp [hrows g hg]
    exact_mod_cast hcount.trans (Nat.mul_le_mul_left 2 (Nat.sub_le D 1))
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    refine ⟨Nat.cast_nonneg _, hq g hg, ?_⟩
    let R := (F.edge f \ F.edge g).biUnion C
    have hRcard : R.card = 2 * (D - 1) := by
      rw [Finset.card_biUnion]
      · calc
          _ = ∑ v ∈ F.edge f \ F.edge g, (D - 1) :=
            Finset.sum_congr rfl (fun v hv => hC v (Finset.mem_sdiff.mp hv).1)
          _ = _ := by simp [hrows g hg]
      · intro v hv w hw hvw
        exact hdisj v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1 hvw
    have hR (h : E) (hh : h ∈ R) :
        h ∈ N ∧ Disjoint (F.edge h ∩ F.edge f) (F.edge g) := by
      obtain ⟨v, hv, hvh⟩ := Finset.mem_biUnion.mp hh
      obtain ⟨hvf, hvg⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hne, hvh⟩ := (Finset.mem_filter.mp hvh).2
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne,
        v, Finset.mem_inter.mpr ⟨hvh, hvf⟩⟩, Finset.disjoint_left.mpr ?_⟩
      intro u hu hug
      have huv := Finset.card_le_one.mp (hone h hne) u hu v
        (Finset.mem_inter.mpr ⟨hvh, hvf⟩)
      exact hvg (huv ▸ hug)
    have hout : (F.edge g \ F.edge f).card = 2 := by
      rw [Finset.card_sdiff, hu g, Finset.inter_comm, (S.V2_edge_shape g hg).1]
    obtain ⟨x, z, hxz, hxzeq⟩ := Finset.card_eq_two.mp hout
    have hx : x ∈ F.edge g ∧ x ∉ F.edge f := by
      exact Finset.mem_sdiff.mp (hxzeq.symm ▸ (Finset.mem_insert_self x {z}))
    have hz : z ∈ F.edge g ∧ z ∉ F.edge f := by
      apply Finset.mem_sdiff.mp
      rw [hxzeq]
      simp
    have hxbsub : F.edge g ∩ S.Xb ⊆ F.edge g \ F.edge f := by
      intro v hv
      obtain ⟨hvg, hvb⟩ := Finset.mem_inter.mp hv
      have hvX : v ∈ S.X := by rw [← S.X_partition]; exact Finset.mem_union_right _ hvb
      exact Finset.mem_sdiff.mpr ⟨hvg, (Finset.mem_filter.mp (S.X_eq ▸ hvX)).2.1⟩
    have hxb : F.edge g ∩ S.Xb = F.edge g \ F.edge f :=
      Finset.eq_of_subset_of_card_le hxbsub (by rw [hout, (S.V2_edge_shape g hg).2])
    let A := R.filter (fun h => x ∈ F.edge h)
    let B := R.filter (fun h => z ∈ F.edge h)
    have hinc (t : V) (ht : t ∉ F.edge f) :
        (∑ v ∈ F.edge f \ F.edge g,
          (((Finset.univ : Finset E).filter (fun h => v ∈ F.edge h ∧ t ∈ F.edge h)).card : ℝ)) =
        ((R.filter (fun h => t ∈ F.edge h)).card : ℝ) := by
      have heq : R.filter (fun h => t ∈ F.edge h) =
          (F.edge f \ F.edge g).biUnion (fun v => (C v).filter (fun h => t ∈ F.edge h)) := by
        ext h
        simp only [R, Finset.mem_filter, Finset.mem_biUnion]
        aesop
      rw [heq, Finset.card_biUnion]
      · push_cast
        apply Finset.sum_congr rfl
        intro v hv
        congr 2
        ext h
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hv, ht'⟩
          exact ⟨⟨fun he => ht (he ▸ ht'), hv⟩, ht'⟩
        · exact fun hh => ⟨hh.1.2, hh.2⟩
      · intro v hv w hw hvw
        exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
            (hdisj v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1 hvw))
    have hcross : S.crossDegree g = (A.card : ℝ) + (B.card : ℝ) := by
      rw [S.crossDegree_eq, hxzeq, Finset.sum_pair hxz, hinc x hx.2, hinc z hz.2]
    have hqeq : N.filter (fun h => Disjoint (F.edge g) (F.edge h)) = R \ (A ∪ B) := by
      ext h
      constructor
      · intro hh
        obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hh
        obtain ⟨hne, v, hv⟩ := (Finset.mem_filter.mp hn).2
        obtain ⟨hvh, hvf⟩ := Finset.mem_inter.mp hv
        have hr : h ∈ R := Finset.mem_biUnion.mpr ⟨v,
          Finset.mem_sdiff.mpr ⟨hvf, fun hvg => Finset.disjoint_left.mp hd hvg hvh⟩,
          by simp [C, hne, hvh]⟩
        apply Finset.mem_sdiff.mpr
        refine ⟨hr, ?_⟩
        simp only [A, B, Finset.mem_union, Finset.mem_filter, not_or]
        exact ⟨fun hh => Finset.disjoint_left.mp hd hx.1 hh.2,
          fun hh => Finset.disjoint_left.mp hd hz.1 hh.2⟩
      · intro hh
        obtain ⟨hr, hab⟩ := Finset.mem_sdiff.mp hh
        refine Finset.mem_filter.mpr ⟨(hR h hr).1, Finset.disjoint_left.mpr ?_⟩
        intro v hvg hvh
        by_cases hvf : v ∈ F.edge f
        · exact Finset.disjoint_left.mp (hR h hr).2 (Finset.mem_inter.mpr ⟨hvh, hvf⟩) hvg
        · have hv : v = x ∨ v = z := by
            have := Finset.mem_sdiff.mpr ⟨hvg, hvf⟩
            rw [hxzeq] at this
            simpa using this
          rcases hv with rfl | rfl
          · exact hab (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hvh⟩))
          · exact hab (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, hvh⟩))
    have hy : (A ∩ B).card ≤ (N.filter (fun h =>
        F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
        (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card := by
      apply Finset.card_le_card
      intro h hh
      obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hh
      obtain ⟨hr, hxh⟩ := Finset.mem_filter.mp ha
      have hzh := (Finset.mem_filter.mp hb).2
      refine Finset.mem_filter.mpr ⟨(hR h hr).1, ?_, ?_⟩
      · intro heq
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [(S.V2_edge_shape g hg).1]; omega)
        exact Finset.disjoint_left.mp (hR h hr).2 (heq ▸ hv) (Finset.mem_inter.mp hv).1
      · have heq : F.edge g ∩ F.edge h ∩ S.Xb = F.edge g ∩ S.Xb := by
          apply Finset.Subset.antisymm
          · intro v hv
            simp only [Finset.mem_inter] at hv ⊢
            exact ⟨hv.1.1, hv.2⟩
          · intro v hv
            have hv' := hv
            rw [hxb, hxzeq] at hv'
            have hvh : v ∈ F.edge h := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
              rcases hv' with rfl | rfl <;> assumption
            exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hvh⟩,
              (Finset.mem_inter.mp hv).2⟩
        rw [heq, (S.V2_edge_shape g hg).2]
    have habsub : A ∪ B ⊆ R := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_sdiff_add_card_eq_card habsub
    have hi := Finset.card_union_add_card_inter A B
    have hc' : ((R \ (A ∪ B)).card : ℝ) + ((A ∪ B).card : ℝ) = (R.card : ℝ) := by exact_mod_cast hc
    have hi' : ((A ∪ B).card : ℝ) + ((A ∩ B).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hi
    have hy' : ((A ∩ B).card : ℝ) ≤ ((N.filter (fun h =>
        F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
        (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card : ℝ) := by exact_mod_cast hy
    change ((N.filter _).card : ℝ) ≤ _
    rw [hqeq, hcross]
    have hrle : (R.card : ℝ) ≤ 2 * (D : ℝ) := by
      rw [hRcard]
      exact_mod_cast Nat.mul_le_mul_left 2 (Nat.sub_le D 1)
    linarith
  · intro g hg
    exact Nat.cast_nonneg _
  · letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
    letI : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
    have hY :
      S.Y = ((∑ v ∈ F.edge f, ∑ w ∈ (F.edge f).filter (fun u => v < u),
        ∑ g ∈ (Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ F.edge g),
        ∑ h ∈ (Finset.univ : Finset E).filter (fun h => h ≠ f ∧ w ∈ F.edge h),
          max (0 : ℤ) (((F.edge g ∩ F.edge h).card : ℤ) - 1)) : ℤ) := by
      classical
      let N := (Finset.univ : Finset E).filter
        (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
      let A := (Finset.univ : Finset (Finset E)).filter (fun s =>
        s.card = 2 ∧ s ⊆ N ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
          (F.edge a ∩ F.edge b).Nonempty)
      let I := (Finset.univ : Finset (Finset E)).filter (fun s =>
        s.card = 2 ∧ s ⊆ N ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
          ¬ (a ≠ b ∧ (F.edge a ∩ F.edge b).Nonempty))
      have hneighbor : (LineGraphOfHypergraph F).neighborFinset f = N := by
        ext g
        simp only [SimpleGraph.mem_neighborFinset, N, Finset.mem_filter, Finset.mem_univ,
          true_and, LineGraphOfHypergraph]
        rw [Finset.inter_comm]
        exact and_congr_left (fun _ => ne_comm)
      have hP : S.P = (I.card : ℝ) := by
        rw [S.P_is_independent_pair_count]
        congr 1
        apply congrArg Finset.card
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (s.card = 2 ∧ s ⊆ (LineGraphOfHypergraph F).neighborFinset f ∧ _) ↔ _
        rw [hneighbor]
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, LineGraphOfHypergraph]
      have hpartition : A = (N.powersetCard 2).filter (fun s => s ∉ I) := by
        ext s
        simp only [A, I, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨hc, hs, hi⟩
          refine ⟨⟨hs, hc⟩, ?_⟩
          rintro ⟨_, _, hn⟩
          obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
          exact hn a (by simp) b (by simp) hab ⟨hab, hi a (by simp) b (by simp) hab⟩
        · rintro ⟨⟨hs, hc⟩, hn⟩
          refine ⟨hc, hs, ?_⟩
          have hex : ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ (F.edge a ∩ F.edge b).Nonempty := by
            by_contra hh
            apply hn
            refine ⟨hc, hs, ?_⟩
            intro a ha b hb hab hi
            exact hh ⟨a, ha, b, hb, hi⟩
          obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
          have hiab : (F.edge a ∩ F.edge b).Nonempty := by
            obtain ⟨c,hc,d,hd,hcd,hi⟩ := hex
            simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
            rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
            · exact (hcd rfl).elim
            · exact hi
            · simpa only [Finset.inter_comm] using hi
            · exact (hcd rfl).elim
          intro c hc d hd hcd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · exact (hcd rfl).elim
          · exact hiab
          · simpa only [Finset.inter_comm] using hiab
          · exact (hcd rfl).elim
      have hIfilter : (N.powersetCard 2).filter (fun s => s ∈ I) = I := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · exact fun h => h.2
        · intro hs
          have hh := (Finset.mem_filter.mp hs).2
          exact ⟨⟨hh.2.1, hh.1⟩, hs⟩
      have hcount : I.card + A.card = Nat.choose (3 * (D - 1)) 2 := by
        have hc := Finset.card_filter_add_card_filter_not (s := N.powersetCard 2) (fun s => s ∈ I)
        rw [hIfilter, ← hpartition, Finset.card_powersetCard] at hc
        exact hc.trans (congrArg (fun n => Nat.choose n 2) S.saturated_neighbors)
      have hX : (Finset.univ.filter (fun x => x ∉ F.edge f ∧
          (Finset.univ.filter (fun h => (F.edge h ∩ F.edge f).Nonempty ∧ x ∈ F.edge h)).Nonempty)) = S.X := by
        rw [S.X_eq]
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.nonempty_def]
        constructor
        · rintro ⟨hx, g, hi, hg⟩
          exact ⟨hx, g, (fun he => hx (he ▸ hg)), hg, hi⟩
        · rintro ⟨hx, g, _, hg, hi⟩
          exact ⟨hx, g, hi, hg⟩
      have hW : S.W = ∑ x ∈ S.X,
          ∑ p ∈ (Finset.univ : Finset (Finset V)).filter (fun p => p.card = 2 ∧ p ⊆ F.edge f),
            ∏ v ∈ p, (((Finset.univ : Finset E).filter
              (fun g => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ) := by
        rw [← S.X_partition, Finset.sum_union S.Xs_disjoint_Xb,
          ← S.WXs_is_weight_of_Xs, ← S.WXb_is_weight_of_Xb, S.W_split]
      have he := (SaturatedLineGraphEdgeCount D F f S.class_mem.1
        S.class_mem.2.2 S.saturated_neighbors).2
      rw [hX] at he
      have heR := congrArg (fun z : ℤ => (z : ℝ)) he
      push_cast at heR
      rw [← hW] at heR
      have hcR : (I.card : ℝ) + (A.card : ℝ) =
          ((Nat.choose (3 * (D - 1)) 2 : ℕ) : ℝ) := by exact_mod_cast hcount
      rw [Nat.cast_choose_two] at hcR
      rw [Nat.cast_choose_two] at heR
      have hD : 1 ≤ D := le_trans (by decide) S.D_large
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hD, Nat.cast_one] at hcR heR
      change (A.card : ℝ) = _ at heR
      rw [← hP] at hcR
      have hp := S.pair_identity
      push_cast
      linarith
    let t := fun g h : E => ((max (0 : ℤ) (((F.edge g ∩ F.edge h).card : ℤ) - 1) : ℤ) : ℝ)
    let Q := fun g h : E => if F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f then t g h else 0
    have ht (g h : E) : 0 ≤ t g h := by
      dsimp only [t]
      exact_mod_cast le_max_left (0 : ℤ) (((F.edge g ∩ F.edge h).card : ℤ) - 1)
    have hQ (g h : E) : 0 ≤ Q g h := by
      dsimp only [Q]
      split_ifs <;> first | exact ht g h | exact le_rfl
    have hcharge (g : E) :
        ((N.filter (fun h => F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
          (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card : ℝ) ≤ ∑ h ∈ N, Q g h := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro h hh
      split_ifs with he
      · rw [show Q g h = t g h from if_pos he.1]
        have hc : 2 ≤ (F.edge g ∩ F.edge h).card := by
          rw [← he.2]
          exact Finset.card_le_card Finset.inter_subset_left
        have hz : (1 : ℤ) ≤ max 0 (((F.edge g ∩ F.edge h).card : ℤ) - 1) := by
          have : (2 : ℤ) ≤ (F.edge g ∩ F.edge h).card := by exact_mod_cast hc
          omega
        dsimp only [t]
        exact_mod_cast hz
      · exact hQ g h
    have hVsub : S.V2 ⊆ N := by
      rw [S.V2_eq]
      exact Finset.sdiff_subset
    have htotal : (∑ g ∈ S.V2,
        ((N.filter (fun h => F.edge h ∩ F.edge f ≠ F.edge g ∩ F.edge f ∧
          (F.edge g ∩ F.edge h ∩ S.Xb).card = 2)).card : ℝ)) ≤
        ∑ g ∈ N, ∑ h ∈ N, Q g h := by
      exact (Finset.sum_le_sum (fun g _ => hcharge g)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hVsub
          (fun g _ _ => Finset.sum_nonneg (fun h _ => hQ g h)))
    have hroot (v : V) (hv : v ∈ F.edge f) (g : E) (hg : g ∈ C v) :
        F.edge g ∩ F.edge f = {v} := by
      have hgg := (Finset.mem_filter.mp hg).2
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_inter.mpr ⟨hgg.2, hv⟩, ?_⟩
      intro w hw
      exact Finset.card_le_one.mp (hone g hgg.1) w hw v (Finset.mem_inter.mpr ⟨hgg.2, hv⟩)
    let K := fun v w : V => ∑ g ∈ C v, ∑ h ∈ C w, t g h
    have hKs (v w : V) : K v w = K w v := by
      dsimp only [K]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro h hh
      simp only [t, Finset.inter_comm]
    have hrowsum : (∑ g ∈ N, ∑ h ∈ N, Q g h) =
        ∑ v ∈ F.edge f, ∑ w ∈ F.edge f, if v ≠ w then K v w else 0 := by
      have hN : N = (F.edge f).biUnion C := hcover.symm
      rw [hN, Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
      rw [Finset.sum_biUnion (show (F.edge f : Set V).PairwiseDisjoint C from hdisj)]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_comm]
      by_cases hvw : v = w
      · subst w
        simp only [ne_eq, not_true_eq_false, if_false]
        apply Finset.sum_eq_zero
        intro g hg
        apply Finset.sum_eq_zero
        intro h hh
        simp only [Q, hroot v hv g hg, hroot v hv h hh, ne_eq, not_true_eq_false, if_false]
      · rw [if_pos hvw]
        apply Finset.sum_congr rfl
        intro g hg
        apply Finset.sum_congr rfl
        intro h hh
        simp only [Q, hroot v hv g hg, hroot w hw h hh,
          ne_eq, Finset.singleton_inj, Ne.symm hvw, not_false_eq_true, if_true]
    have horient : (∑ v ∈ F.edge f, ∑ w ∈ F.edge f, if v ≠ w then K v w else 0) =
        2 * ∑ v ∈ F.edge f, ∑ w ∈ (F.edge f).filter (fun w => v < w), K v w := by
      have hsplit (v w : V) : (if v ≠ w then K v w else 0) =
          (if v < w then K v w else 0) + (if w < v then K v w else 0) := by
        rcases lt_trichotomy v w with h | rfl | h
        · simp [h, ne_of_lt h, not_lt_of_ge h.le]
        · simp
        · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le]
      simp_rw [hsplit, Finset.sum_add_distrib]
      have hswap : (∑ v ∈ F.edge f, ∑ w ∈ F.edge f, if w < v then K v w else 0) =
          ∑ v ∈ F.edge f, ∑ w ∈ F.edge f, if v < w then K v w else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro w hw
        rw [hKs w v]
      rw [hswap]
      simp_rw [Finset.sum_filter]
      ring
    have hY' : S.Y = ∑ v ∈ F.edge f,
        ∑ w ∈ (F.edge f).filter (fun w => v < w), K v w := by
      rw [hY]
      simp only [K, C, t, Int.cast_sum]
    change (∑ g ∈ S.V2, _) ≤ _
    rw [hY']
    exact htotal.trans_eq (hrowsum.trans horient)
