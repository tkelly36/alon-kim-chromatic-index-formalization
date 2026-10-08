import Tablet.IndependentPairCount
import Tablet.KUniformSplitEdgeHypergraph
import Tablet.LineGraphOfHypergraph

set_option maxHeartbeats 1600000

-- [TABLET NODE: KUniformSplitEdgeIndependentPairUpperBound]
theorem KUniformSplitEdgeIndependentPairUpperBound :
    ∀ k : ℕ, ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E, ∀ f g : E, ∀ u v : V,
        [DecidableRel (LineGraphOfHypergraph H).Adj] →
        g ≠ f → u ≠ v → u ∈ H.edge f → v ∈ H.edge f → u ∈ H.edge g →
          ∀ hv : v ∈ H.edge g, ∀ x1 : Fin (k - 1),
            [DecidableRel
              (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1)).Adj] →
            IndependentPairCount
                (LineGraphOfHypergraph (KUniformSplitEdgeHypergraph k H g v hv x1))
                (Sum.inl f) ≤
              IndependentPairCount (LineGraphOfHypergraph H) f +
                (((Finset.univ : Finset E).filter
                  (fun e => (LineGraphOfHypergraph H).Adj f e)).erase g).card := by
-- BODY
  classical
  intro k V E _ _ _ H f g u v _ hgf huv huf hvf hug hv x1 _
  let Hsplit : MultiHypergraph (V ⊕ Fin (k - 1)) (E ⊕ Unit) :=
    KUniformSplitEdgeHypergraph k H g v hv x1
  let G := LineGraphOfHypergraph H
  let Gsplit := LineGraphOfHypergraph Hsplit
  let fresh : E ⊕ Unit := Sum.inr ()
  let oldOf : Finset (E ⊕ Unit) → Finset E := fun S =>
    S.preimage Sum.inl (by
      intro x _ y _ hxy
      exact Sum.inl.inj hxy)
  let oldPairs : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter (fun S =>
      S.card = 2 ∧ S ⊆ G.neighborFinset f ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ G.Adj x y)
  let splitPairs : Finset (Finset (E ⊕ Unit)) :=
    (Finset.univ : Finset (Finset (E ⊕ Unit))).filter (fun S =>
      S.card = 2 ∧ S ⊆ Gsplit.neighborFinset (Sum.inl f) ∧
        ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ Gsplit.Adj x y)
  let oldNeighbors : Finset E :=
    (Finset.univ : Finset E).filter (fun e => G.Adj f e)
  let A := splitPairs.filter (fun S => fresh ∉ S)
  let B := splitPairs.filter (fun S => fresh ∈ S)
  let C := A.filter (fun S => oldOf S ∈ oldPairs)
  let X := A.filter (fun S => oldOf S ∉ oldPairs)
  let throughV : Finset E := (oldNeighbors.erase g).filter (fun e => v ∈ H.edge e)
  let notThroughV : Finset E := (oldNeighbors.erase g).filter (fun e => v ∉ H.edge e)
  have hfg : f ≠ g := hgf.symm
  have hf_edge :
      Hsplit.edge (Sum.inl f) = Finset.image Sum.inl (H.edge f) := by
    simp [Hsplit, KUniformSplitEdgeHypergraph, hfg]
  have hg_split_meets_f :
      (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge (Sum.inl g)).Nonempty := by
    refine ⟨Sum.inl u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [hf_edge]
      exact Finset.mem_image.mpr ⟨u, huf, rfl⟩
    · simp [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase, hug, huv]
  have hf_fresh_meets :
      (Hsplit.edge (Sum.inl f) ∩ Hsplit.edge fresh).Nonempty := by
    refine ⟨Sum.inl v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [hf_edge]
      exact Finset.mem_image.mpr ⟨v, hvf, rfl⟩
    · simp [fresh, Hsplit, KUniformSplitEdgeHypergraph]
  have himage_nonempty_old (a b : E) (ha : a ≠ g) (hb : b ≠ g) :
      (Hsplit.edge (Sum.inl a) ∩ Hsplit.edge (Sum.inl b)).Nonempty ↔
        (H.edge a ∩ H.edge b).Nonempty := by
    constructor
    · intro h
      rcases h with ⟨x, hx⟩
      rcases Finset.mem_inter.mp hx with ⟨hxa, hxb⟩
      have ha_edge :
          Hsplit.edge (Sum.inl a) = Finset.image Sum.inl (H.edge a) := by
        simp [Hsplit, KUniformSplitEdgeHypergraph, ha]
      have hb_edge :
          Hsplit.edge (Sum.inl b) = Finset.image Sum.inl (H.edge b) := by
        simp [Hsplit, KUniformSplitEdgeHypergraph, hb]
      rw [ha_edge] at hxa
      rw [hb_edge] at hxb
      rcases Finset.mem_image.mp hxa with ⟨w, hwa, rfl⟩
      rcases Finset.mem_image.mp hxb with ⟨z, hzb, hz⟩
      cases hz
      exact ⟨w, Finset.mem_inter.mpr ⟨hwa, hzb⟩⟩
    · intro h
      rcases h with ⟨w, hw⟩
      rcases Finset.mem_inter.mp hw with ⟨hwa, hwb⟩
      refine ⟨Sum.inl w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [Hsplit, KUniformSplitEdgeHypergraph, ha, hwa]
      · simp [Hsplit, KUniformSplitEdgeHypergraph, hb, hwb]
  have hsplit_adj_imp_old_neighbor (a : E) :
      Gsplit.Adj (Sum.inl f) (Sum.inl a) → G.Adj f a := by
    intro h
    rcases h with ⟨hne, hmeet⟩
    refine ⟨?_, ?_⟩
    · intro hfa
      exact hne (by simp [hfa])
    · by_cases hag : a = g
      · subst a
        exact ⟨u, Finset.mem_inter.mpr ⟨huf, hug⟩⟩
      · exact (himage_nonempty_old f a hfg hag).mp hmeet
  have hold_neighbor_to_split (a : E) :
      G.Adj f a → Gsplit.Adj (Sum.inl f) (Sum.inl a) := by
    intro h
    rcases h with ⟨hne, hmeet⟩
    refine ⟨?_, ?_⟩
    · intro hsum
      exact hne (Sum.inl.inj hsum)
    · by_cases hag : a = g
      · subst a
        exact hg_split_meets_f
      · exact (himage_nonempty_old f a hfg hag).mpr hmeet
  have hnon_g_preserve (a b : E) (ha : a ≠ g) (hb : b ≠ g) :
      Gsplit.Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
    constructor
    · intro h
      rcases h with ⟨hne, hmeet⟩
      exact ⟨fun hab => hne (by simp [hab]), (himage_nonempty_old a b ha hb).mp hmeet⟩
    · intro h
      rcases h with ⟨hne, hmeet⟩
      exact ⟨fun hab => hne (Sum.inl.inj hab), (himage_nonempty_old a b ha hb).mpr hmeet⟩
  have hfresh_adj_old (a : E) (ha : a ≠ g) :
      Gsplit.Adj fresh (Sum.inl a) ↔ v ∈ H.edge a := by
    constructor
    · intro h
      rcases h.2 with ⟨z, hz⟩
      rcases Finset.mem_inter.mp hz with ⟨hzfresh, hza⟩
      have ha_edge :
          Hsplit.edge (Sum.inl a) = Finset.image Sum.inl (H.edge a) := by
        simp [Hsplit, KUniformSplitEdgeHypergraph, ha]
      rw [ha_edge] at hza
      rcases Finset.mem_image.mp hza with ⟨w, hwa, hzw⟩
      have hz_cases : z = Sum.inl v ∨ ∃ y : Fin (k - 1), z = Sum.inr y := by
        have hz_cases' : z = Sum.inl v ∨ ∃ y : Fin (k - 1), Sum.inr y = z := by
          simpa [fresh, Hsplit, KUniformSplitEdgeHypergraph] using hzfresh
        rcases hz_cases' with hzv | ⟨y, hzy⟩
        · exact Or.inl hzv
        · exact Or.inr ⟨y, hzy.symm⟩
      rcases hz_cases with hzv | ⟨y, hzy⟩
      · rw [hzv] at hzw
        cases hzw
        exact hwa
      · rw [hzy] at hzw
        cases hzw
    · intro hva
      refine ⟨by simp [fresh], ?_⟩
      refine ⟨Sum.inl v, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [fresh, Hsplit, KUniformSplitEdgeHypergraph]
      · simp [Hsplit, KUniformSplitEdgeHypergraph, ha, hva]
  have holdOf_inj_on_A : Set.InjOn (fun S : Finset (E ⊕ Unit) => oldOf S)
      (↑A : Set (Finset (E ⊕ Unit))) := by
    intro S hS T hT heq
    have hSfresh : fresh ∉ S := (Finset.mem_filter.mp hS).2
    have hTfresh : fresh ∉ T := (Finset.mem_filter.mp hT).2
    ext x
    cases x with
    | inl e =>
        have := congrArg (fun U : Finset E => e ∈ U) heq
        simpa [oldOf] using this
    | inr unitLabel =>
        cases unitLabel
        exact ⟨fun hx => (hSfresh hx).elim, fun hx => (hTfresh hx).elim⟩
  have hCcard : C.card ≤ oldPairs.card := by
    exact Finset.card_le_card_of_injOn (fun S : Finset (E ⊕ Unit) => oldOf S)
      (by
        intro S hS
        exact (Finset.mem_filter.mp hS).2)
      (by
        intro S hS T hT heq
        exact holdOf_inj_on_A
          (by exact (Finset.mem_filter.mp hS).1)
          (by exact (Finset.mem_filter.mp hT).1) heq)
  have hX_to_through (S : Finset (E ⊕ Unit)) (hS : S ∈ X) :
      (oldOf S).erase g ∈ throughV.image (fun e => ({e} : Finset E)) := by
    simp only [X, A, splitPairs, Finset.mem_filter] at hS
    rcases hS with ⟨⟨⟨_, hcardS, hsubS, hindS⟩, hfreshS⟩, hnotOld⟩
    have h_range : ∀ x ∈ S, x ∈ Set.range (Sum.inl : E → E ⊕ Unit) := by
      intro x hx
      cases x with
      | inl e => exact ⟨e, rfl⟩
      | inr unitLabel =>
          cases unitLabel
          exact (hfreshS hx).elim
    have hcardOld : (oldOf S).card = 2 := by
      have himage : (oldOf S).image (Sum.inl : E → E ⊕ Unit) = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
          simpa [oldOf] using he
        · intro hx
          rcases h_range x hx with ⟨e, rfl⟩
          exact Finset.mem_image.mpr ⟨e, by simpa [oldOf], rfl⟩
      have hcard_image : ((oldOf S).image (Sum.inl : E → E ⊕ Unit)).card =
          (oldOf S).card := Finset.card_image_of_injective _ Sum.inl_injective
      rw [← hcard_image, himage, hcardS]
    have hsubOld : oldOf S ⊆ G.neighborFinset f := by
      intro a ha
      have hSa : Sum.inl a ∈ S := by simpa [oldOf] using ha
      have hneigh := hsubS hSa
      simpa [SimpleGraph.mem_neighborFinset, G] using
        hsplit_adj_imp_old_neighbor a
          (by simpa [SimpleGraph.mem_neighborFinset, Gsplit] using hneigh)
    have hnotInd :
        ¬ (∀ ⦃x⦄, x ∈ oldOf S → ∀ ⦃y⦄, y ∈ oldOf S → x ≠ y → ¬ G.Adj x y) := by
      intro hindOld
      apply hnotOld
      simp only [oldPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcardOld, hsubOld, by
        intro x hx y hy hxy
        exact hindOld hx hy hxy⟩
    push_neg at hnotInd
    rcases hnotInd with ⟨a, haS, b, hbS, hab, habAdj⟩
    have hSa : Sum.inl a ∈ S := by simpa [oldOf] using haS
    have hSb : Sum.inl b ∈ S := by simpa [oldOf] using hbS
    have hnotSplit : ¬ Gsplit.Adj (Sum.inl a) (Sum.inl b) :=
      hindS hSa hSb (by simp [hab])
    have hg_mem_old : g ∈ oldOf S := by
      by_contra hgm
      have ha_ne_g : a ≠ g := fun h => hgm (by simpa [h] using haS)
      have hb_ne_g : b ≠ g := fun h => hgm (by simpa [h] using hbS)
      exact hnotSplit ((hnon_g_preserve a b ha_ne_g hb_ne_g).mpr habAdj)
    have hcard_erase : ((oldOf S).erase g).card = 1 := by
      rw [Finset.card_erase_of_mem hg_mem_old]
      omega
    rcases Finset.card_eq_one.mp hcard_erase with ⟨h, hh⟩
    have h_old_eq : oldOf S = {g, h} := by
      have h_erase : (oldOf S).erase g = {h} := hh
      ext z
      by_cases hzg : z = g
      · subst z
        simp [hg_mem_old]
      · have := congrArg (fun T : Finset E => z ∈ T) h_erase
        constructor
        · intro hzold
          have hzerase : z ∈ (oldOf S).erase g := Finset.mem_erase.mpr ⟨hzg, hzold⟩
          rw [h_erase] at hzerase
          have hzh : z = h := by simpa using hzerase
          simp [hzh]
        · intro hzpair
          have hzh : z = h := by simpa [hzg] using hzpair
          subst z
          exact Finset.mem_of_mem_erase (by rw [h_erase]; simp)
    have hh_mem_old : h ∈ oldOf S := by
      rw [h_old_eq]
      simp
    have hSh : Sum.inl h ∈ S := by simpa [oldOf] using hh_mem_old
    have h_ne_g : h ≠ g := by
      intro heq
      have : (oldOf S).card = 1 := by
        rw [h_old_eq, heq]
        simp
      omega
    have h_neigh_h : h ∈ oldNeighbors.erase g := by
      have hneigh := hsubOld hh_mem_old
      have hGold : G.Adj f h := by simpa [SimpleGraph.mem_neighborFinset, G] using hneigh
      simp [oldNeighbors, h_ne_g, hGold]
    have hvh : v ∈ H.edge h := by
      have hOldAdj_g_h : G.Adj g h := by
        by_cases hag : a = g
        · subst a
          have hb_eq_h : b = h := by
            have hb_in_pair : b ∈ ({g, h} : Finset E) := by simpa [← h_old_eq] using hbS
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb_in_pair
            rcases hb_in_pair with hbg | hbh
            · exact (hab hbg.symm).elim
            · exact hbh
          simpa [hb_eq_h] using habAdj
        · have ha_eq_h : a = h := by
            have ha_in_pair : a ∈ ({g, h} : Finset E) := by simpa [← h_old_eq] using haS
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha_in_pair
            rcases ha_in_pair with hag' | hah
            · exact (hag hag').elim
            · exact hah
          have hb_eq_g : b = g := by
            have hb_in_pair : b ∈ ({g, h} : Finset E) := by simpa [← h_old_eq] using hbS
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb_in_pair
            rcases hb_in_pair with hbg | hbh
            · exact hbg
            · exfalso
              exact hab (by rw [ha_eq_h, hbh])
          subst b
          simpa [ha_eq_h] using G.symm habAdj
      by_contra hvh_not
      have hg_h_split : Gsplit.Adj (Sum.inl g) (Sum.inl h) := by
        rcases hOldAdj_g_h with ⟨hgh_ne, hmeet⟩
        refine ⟨by intro h; exact hgh_ne (Sum.inl.inj h), ?_⟩
        rcases hmeet with ⟨w, hw⟩
        rcases Finset.mem_inter.mp hw with ⟨hwg, hwh⟩
        have hw_ne_v : w ≠ v := by
          intro hwv
          exact hvh_not (by simpa [hwv] using hwh)
        refine ⟨Sum.inl w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · simp [Hsplit, KUniformSplitEdgeHypergraph, Finset.mem_erase, hw_ne_v, hwg]
        · simp [Hsplit, KUniformSplitEdgeHypergraph, h_ne_g, hwh]
      have hSg : Sum.inl g ∈ S := by simpa [oldOf] using hg_mem_old
      exact hindS hSg hSh (by
        intro hsum
        exact h_ne_g (Sum.inl.inj hsum).symm) hg_h_split
    exact Finset.mem_image.mpr ⟨h, by simp [throughV, h_neigh_h, hvh], hh.symm⟩
  have hXinj : Set.InjOn (fun S : Finset (E ⊕ Unit) => (oldOf S).erase g)
      (↑X : Set (Finset (E ⊕ Unit))) := by
    intro S hS T hT heq
    have hSx := hX_to_through S hS
    have hTx := hX_to_through T hT
    simp only [Finset.mem_image] at hSx hTx
    rcases hSx with ⟨s, hs, hSe⟩
    rcases hTx with ⟨t, ht, hTe⟩
    have hgS : g ∈ oldOf S := by
      have hcard : ((oldOf S).erase g).card = 1 := by rw [← hSe]; simp
      by_contra hg
      have : (oldOf S).erase g = oldOf S := Finset.erase_eq_self.mpr hg
      have hSfin : S ∈ X := hS
      simp only [X, A, splitPairs, Finset.mem_filter] at hSfin
      rcases hSfin with ⟨⟨⟨_, hcardS, _, _⟩, hfreshS⟩, _⟩
      have h_range : ∀ x ∈ S, x ∈ Set.range (Sum.inl : E → E ⊕ Unit) := by
        intro x hx
        cases x with
        | inl e => exact ⟨e, rfl⟩
        | inr unitLabel =>
            cases unitLabel
            exact (hfreshS hx).elim
      have himage : (oldOf S).image (Sum.inl : E → E ⊕ Unit) = S := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
          simpa [oldOf] using he
        · intro hx
          rcases h_range x hx with ⟨e, rfl⟩
          exact Finset.mem_image.mpr ⟨e, by simpa [oldOf], rfl⟩
      have hcardOld : (oldOf S).card = 2 := by
        have hcard_image : ((oldOf S).image (Sum.inl : E → E ⊕ Unit)).card =
            (oldOf S).card := Finset.card_image_of_injective _ Sum.inl_injective
        rw [← hcard_image, himage, hcardS]
      rw [this] at hcard
      omega
    have hgT : g ∈ oldOf T := by
      have hcard : ((oldOf T).erase g).card = 1 := by rw [← hTe]; simp
      by_contra hg
      have : (oldOf T).erase g = oldOf T := Finset.erase_eq_self.mpr hg
      have hTfin : T ∈ X := hT
      simp only [X, A, splitPairs, Finset.mem_filter] at hTfin
      rcases hTfin with ⟨⟨⟨_, hcardT, _, _⟩, hfreshT⟩, _⟩
      have h_range : ∀ x ∈ T, x ∈ Set.range (Sum.inl : E → E ⊕ Unit) := by
        intro x hx
        cases x with
        | inl e => exact ⟨e, rfl⟩
        | inr unitLabel =>
            cases unitLabel
            exact (hfreshT hx).elim
      have himage : (oldOf T).image (Sum.inl : E → E ⊕ Unit) = T := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
          simpa [oldOf] using he
        · intro hx
          rcases h_range x hx with ⟨e, rfl⟩
          exact Finset.mem_image.mpr ⟨e, by simpa [oldOf], rfl⟩
      have hcardOld : (oldOf T).card = 2 := by
        have hcard_image : ((oldOf T).image (Sum.inl : E → E ⊕ Unit)).card =
            (oldOf T).card := Finset.card_image_of_injective _ Sum.inl_injective
        rw [← hcard_image, himage, hcardT]
      rw [this] at hcard
      omega
    apply holdOf_inj_on_A (by exact (Finset.mem_filter.mp hS).1)
      (by exact (Finset.mem_filter.mp hT).1)
    ext z
    by_cases hzg : z = g
    · subst z
      simp [hgS, hgT]
    · have hz_erase_eq := congrArg (fun T : Finset E => z ∈ T) heq
      simp [hzg] at hz_erase_eq
      exact hz_erase_eq
  have hXcard : X.card ≤ throughV.card := by
    have htarget_card :
        (throughV.image (fun e => ({e} : Finset E))).card = throughV.card := by
      rw [Finset.card_image_of_injective]
      intro a b hab
      have hmem : a ∈ ({b} : Finset E) := by
        change ({a} : Finset E) = {b} at hab
        rw [← hab]
        simp
      simpa using hmem
    calc
      X.card ≤ (throughV.image (fun e => ({e} : Finset E))).card :=
        Finset.card_le_card_of_injOn (fun S : Finset (E ⊕ Unit) => (oldOf S).erase g)
          hX_to_through hXinj
      _ = throughV.card := htarget_card
  have hB_to_notThrough (S : Finset (E ⊕ Unit)) (hS : S ∈ B) :
      ∃ h ∈ notThroughV, S = {fresh, Sum.inl h} := by
    simp only [B, splitPairs, Finset.mem_filter] at hS
    rcases hS with ⟨⟨_, hcardS, hsubS, hindS⟩, hfreshS⟩
    rcases Finset.card_eq_two.mp hcardS with ⟨a, b, hab, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfreshS
    rcases hfreshS with ha | hb
    · subst a
      cases b with
      | inl h =>
          have hSinlh : Sum.inl h ∈ ({fresh, Sum.inl h} : Finset (E ⊕ Unit)) := by simp
          have hneigh := hsubS hSinlh
          have hGold : G.Adj f h :=
            hsplit_adj_imp_old_neighbor h
              (by simpa [SimpleGraph.mem_neighborFinset, Gsplit] using hneigh)
          have h_ne_g : h ≠ g := by
            intro hhg
            subst h
            have hadj_fresh_g : Gsplit.Adj fresh (Sum.inl g) := by
              refine ⟨by simp [fresh], ?_⟩
              refine ⟨Sum.inr x1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
              · simp [fresh, Hsplit, KUniformSplitEdgeHypergraph]
              · simp [Hsplit, KUniformSplitEdgeHypergraph]
            exact hindS (by simp) (by simp) (by simp [fresh]) hadj_fresh_g
          have hv_not : v ∉ H.edge h := by
            intro hvh
            have hadj := (hfresh_adj_old h h_ne_g).mpr hvh
            exact hindS (by simp) (by simp) (by simp [fresh]) hadj
          exact ⟨h, by simp [notThroughV, oldNeighbors, hGold, h_ne_g, hv_not], rfl⟩
      | inr unitLabel =>
          cases unitLabel
          simp [fresh] at hab
    · subst b
      cases a with
      | inl h =>
          have hSinlh : Sum.inl h ∈ ({Sum.inl h, fresh} : Finset (E ⊕ Unit)) := by simp
          have hneigh := hsubS hSinlh
          have hGold : G.Adj f h :=
            hsplit_adj_imp_old_neighbor h
              (by simpa [SimpleGraph.mem_neighborFinset, Gsplit] using hneigh)
          have h_ne_g : h ≠ g := by
            intro hhg
            subst h
            have hadj_fresh_g : Gsplit.Adj (Sum.inl g) fresh := by
              exact Gsplit.symm (by
                refine ⟨by simp [fresh], ?_⟩
                refine ⟨Sum.inr x1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
                · simp [fresh, Hsplit, KUniformSplitEdgeHypergraph]
                · simp [Hsplit, KUniformSplitEdgeHypergraph])
            exact hindS (by simp) (by simp) (by simp [fresh]) hadj_fresh_g
          have hv_not : v ∉ H.edge h := by
            intro hvh
            have hadj := Gsplit.symm ((hfresh_adj_old h h_ne_g).mpr hvh)
            exact hindS (by simp) (by simp) (by simp [fresh]) hadj
          exact ⟨h, by simp [notThroughV, oldNeighbors, hGold, h_ne_g, hv_not],
            by ext z <;> simp [fresh, or_comm]⟩
      | inr unitLabel =>
          cases unitLabel
          simp [fresh] at hab
  have hBcard : B.card ≤ notThroughV.card := by
    let toPair : Finset (Finset (E ⊕ Unit)) :=
      notThroughV.image (fun h => ({fresh, Sum.inl h} : Finset (E ⊕ Unit)))
    have hsub : B ⊆ toPair := by
      intro S hS
      rcases hB_to_notThrough S hS with ⟨h, hh, hSeq⟩
      exact Finset.mem_image.mpr ⟨h, hh, hSeq.symm⟩
    have hcard_to : toPair.card = notThroughV.card := by
      dsimp [toPair]
      rw [Finset.card_image_of_injective]
      intro a b hab
      have hmem : (Sum.inl a : E ⊕ Unit) ∈ ({fresh, Sum.inl b} : Finset (E ⊕ Unit)) := by
        change ({fresh, Sum.inl a} : Finset (E ⊕ Unit)) = {fresh, Sum.inl b} at hab
        rw [← hab]
        simp
      simpa [fresh] using hmem
    exact le_trans (Finset.card_le_card hsub) (by rw [hcard_to])
  have hA_part : X.card + C.card = A.card := by
    rw [add_comm]
    simpa [X, C] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := A)
        (fun S => oldOf S ∈ oldPairs))
  have hsplit_part : B.card + A.card = splitPairs.card := by
    simpa [B, A] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := splitPairs)
        (fun S => fresh ∈ S))
  have hthrough_part : throughV.card + notThroughV.card = (oldNeighbors.erase g).card := by
    simpa [throughV, notThroughV] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := oldNeighbors.erase g)
        (fun e => v ∈ H.edge e))
  have htotal :
      splitPairs.card ≤ oldPairs.card + (oldNeighbors.erase g).card := by
    omega
  simpa [IndependentPairCount, G, Gsplit, Hsplit, oldPairs, splitPairs, oldNeighbors]
    using htotal
