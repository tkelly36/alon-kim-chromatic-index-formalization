import Tablet.RandomIndependentSetSampling
import Tablet.RandomIndependentSetSamplingGammaLeDelta
import Tablet.FiniteSimpleRegularCompletion
import Tablet.SamplingRegularGraphSamplingLawExists
import Tablet.SamplingSplitOutsideBlockerEventMonotonicity

open BigOperators

universe u

-- [TABLET NODE: SamplingRegularEnlargementReduction]
theorem SamplingRegularEnlargementReduction :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, ∀ gamma : ℝ,
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              ∃ (V' : Type u) (instF : Fintype V') (instD : DecidableEq V')
                  (G' : SimpleGraph V') (instAdj : DecidableRel G'.Adj),
                letI : Fintype V' := instF
                letI : DecidableEq V' := instD
                letI : DecidableRel G'.Adj := instAdj
                ∃ (φ : V → V') (r' : V') (X' : Finset V') (μ' : Finset V' → ℝ),
                  Function.Injective φ ∧ r' = φ r ∧ X' = X.image φ ∧
                    (∀ v' : V', G'.degree v' = Delta) ∧
                    (∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
                      (G.Adj a b ↔ G'.Adj (φ a) (φ b))) ∧
                    (∀ u : V, u ∈ X → ∀ v : V, v ∈ X → u ≠ v →
                      ¬ ∃ w' : V', G'.Adj (φ u) w' ∧ G'.Adj (φ v) w' ∧
                        w' ≠ r' ∧ ¬ G'.Adj r' w') ∧
                    RandomIndependentSetSampling G' Delta gamma μ' ∧
                    (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
                      (∑ S' : Finset V', if (S' ∩ X').Nonempty then μ' S' else 0) := by
-- BODY
  intro V _instFintype _instDecEq G _instDecRel Delta gamma hregular μ hsampling r X hX
  classical
  by_cases hDelta : Delta = 0
  · have hX_empty : X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx_neigh : x ∈ G.neighborFinset r := by
        simpa [SimpleGraph.mem_neighborFinset] using hX x hx
      have hcard_zero : (G.neighborFinset r).card = 0 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree, hDelta] using hregular r
      have hneigh_empty : G.neighborFinset r = ∅ := Finset.card_eq_zero.mp hcard_zero
      rw [hneigh_empty] at hx_neigh
      simp at hx_neigh
    refine ⟨V, inferInstance, inferInstance, G, inferInstance, ?_⟩
    refine ⟨id, r, X.image id, μ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact hab
    · rfl
    · rfl
    · intro v
      exact hregular v
    · intro a b _ _
      rfl
    · intro u hu
      rw [hX_empty] at hu
      simp at hu
    · exact hsampling
    · simp [hX_empty]
  ·
    have hDelta_pos : 0 < Delta := Nat.pos_of_ne_zero hDelta
    have hX_card_le_Delta : X.card ≤ Delta := by
      rw [← hregular r, ← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by
        intro x hx
        simpa [SimpleGraph.mem_neighborFinset] using hX x hx)
    let L : Finset V := insert r X
    let Blocker : Type u :=
      Σ x : {x : V // x ∈ X},
        {z : V // z ∉ L ∧ G.Adj x.1 z}
    let W : Type u := V ⊕ Blocker ⊕ Fin (Delta - X.card)
    let old : V → W := fun v => Sum.inl v
    let rootFiller : Fin (Delta - X.card) → W := fun i => Sum.inr (Sum.inr i)
    let H : SimpleGraph W :=
      { Adj := fun a b =>
          (∃ u v : V, a = old u ∧ b = old v ∧ u ∈ L ∧ v ∈ L ∧ G.Adj u v) ∨
          (∃ (x : {x : V // x ∈ X}) (z : {z : V // z ∉ L ∧ G.Adj x.1 z}),
            (a = old x.1 ∧ b = Sum.inr (Sum.inl ⟨x, z⟩)) ∨
              (a = Sum.inr (Sum.inl ⟨x, z⟩) ∧ b = old x.1)) ∨
          (∃ i : Fin (Delta - X.card),
            (a = old r ∧ b = rootFiller i) ∨
              (a = rootFiller i ∧ b = old r))
        symm := by
          rintro a b (hlocal | hblock | hfiller)
          · rcases hlocal with ⟨u, v, rfl, rfl, huL, hvL, huv⟩
            exact Or.inl ⟨v, u, rfl, rfl, hvL, huL, G.symm huv⟩
          · rcases hblock with ⟨x, z, h | h⟩
            · exact Or.inr (Or.inl ⟨x, z, Or.inr ⟨h.2, h.1⟩⟩)
            · exact Or.inr (Or.inl ⟨x, z, Or.inl ⟨h.2, h.1⟩⟩)
          · rcases hfiller with ⟨i, h | h⟩
            · exact Or.inr (Or.inr ⟨i, Or.inr ⟨h.2, h.1⟩⟩)
            · exact Or.inr (Or.inr ⟨i, Or.inl ⟨h.2, h.1⟩⟩)
        loopless := ⟨by
          rintro (a | b)
          · intro h
            rcases h with hlocal | hblock | hfiller
            · rcases hlocal with ⟨u, v, hu, hv, _huL, _hvL, huv⟩
              cases hu
              cases hv
              exact G.loopless.irrefl _ huv
            · rcases hblock with ⟨x, z, h | h⟩
              · simpa [old] using h.2
              · simpa [old] using h.1
            · rcases hfiller with ⟨i, h | h⟩
              · simpa [old, rootFiller] using h.2
              · simpa [old, rootFiller] using h.1
          · intro h
            rcases b with b | i
            · rcases h with hlocal | hblock | hfiller
              · rcases hlocal with ⟨u, v, hu, hv, _huL, _hvL, huv⟩
                cases hu
              · rcases hblock with ⟨x, z, h | h⟩
                · simpa [old] using h.1
                · simpa [old] using h.2
              · rcases hfiller with ⟨i, h | h⟩
                · simpa [old, rootFiller] using h.1
                · cases h.1
            · rcases h with hlocal | hblock | hfiller
              · rcases hlocal with ⟨u, v, hu, hv, _huL, _hvL, huv⟩
                cases hu
              · rcases hblock with ⟨x, z, h | h⟩
                · simpa [old] using h.1
                · cases h.1
              · rcases hfiller with ⟨j, h | h⟩
                · simpa [old, rootFiller] using h.1
                · simpa [old, rootFiller] using h.2⟩ }
    have hold_injective : Function.Injective old := by
      intro a b h
      exact Sum.inl.inj h
    have hlocal_preserved :
        ∀ a b : V, (a ∈ X ∨ a = r) → (b ∈ X ∨ b = r) →
          (G.Adj a b ↔ H.Adj (old a) (old b)) := by
      intro a b ha hb
      have haL : a ∈ L := by
        rcases ha with ha | rfl
        · simp [L, ha]
        · simp [L]
      have hbL : b ∈ L := by
        rcases hb with hb | rfl
        · simp [L, hb]
        · simp [L]
      constructor
      · intro hab
        exact Or.inl ⟨a, b, rfl, rfl, haL, hbL, hab⟩
      · intro hab
        rcases hab with hlocal | hblock | hfiller
        · rcases hlocal with ⟨u, v, hu, hv, _huL, _hvL, huv⟩
          cases hu
          cases hv
          exact huv
        · rcases hblock with ⟨x, z, h | h⟩
          · cases h.2
          · cases h.1
        · rcases hfiller with ⟨i, h | h⟩
          · cases h.2
          · cases h.1
    have hH_degree_le : ∀ w : W, H.degree w ≤ Delta := by
      intro w
      have hr_not_mem_X : r ∉ X := by
        intro hrX
        exact G.loopless.irrefl r (hX r hrX)
      have hNeighborSubtypeDegree :
          ∀ w : W, Nat.card {y : W // H.Adj w y} = H.degree w := by
        intro w
        let e :
            {y : W // H.Adj w y} ≃ {y : W // y ∈ H.neighborFinset w} :=
          { toFun := fun y => ⟨y.1, (H.mem_neighborFinset w y.1).mpr y.2⟩
            invFun := fun y => ⟨y.1, (H.mem_neighborFinset w y.1).mp y.2⟩
            left_inv := by
              intro y
              rfl
            right_inv := by
              intro y
              rfl }
        calc
          Nat.card {y : W // H.Adj w y}
              = Nat.card {y : W // y ∈ H.neighborFinset w} := Nat.card_congr e
          _ = Fintype.card {y : W // y ∈ H.neighborFinset w} :=
                Nat.card_eq_fintype_card
          _ = (H.neighborFinset w).card := Fintype.card_coe (H.neighborFinset w)
          _ = H.degree w := SimpleGraph.card_neighborFinset_eq_degree H w
      cases w with
      | inl v =>
          by_cases hvX : v ∈ X
          · let embedNeighbor :
                {z : V // z ∈ G.neighborFinset v} → W := fun z =>
                  if hzL : z.1 ∈ L then
                    old z.1
                  else
                    Sum.inr (Sum.inl
                      ⟨⟨v, hvX⟩, ⟨z.1, hzL, (G.mem_neighborFinset v z.1).mp z.2⟩⟩)
            have hsubset :
                H.neighborFinset (old v) ⊆
                  Finset.univ.image embedNeighbor := by
              intro y hy
              have hadj : H.Adj (old v) y := (H.mem_neighborFinset (old v) y).mp hy
              rcases hadj with hlocal | hblock | hfiller
              · rcases hlocal with ⟨a, b, ha, hyb, _haL, hbL, hab⟩
                cases ha
                subst y
                refine Finset.mem_image.mpr ?_
                refine ⟨⟨b, (G.mem_neighborFinset v b).mpr hab⟩, Finset.mem_univ _, ?_⟩
                simp [embedNeighbor, hbL]
              · rcases hblock with ⟨x, z, h | h⟩
                · have hxv : x.1 = v := by
                    exact (Sum.inl.inj h.1).symm
                  refine Finset.mem_image.mpr ?_
                  refine
                    ⟨⟨z.1, (G.mem_neighborFinset v z.1).mpr ?_⟩,
                      Finset.mem_univ _, ?_⟩
                  · simpa [hxv] using z.2.2
                  · calc
                      embedNeighbor ⟨z.1, (G.mem_neighborFinset v z.1).mpr
                          (by simpa [hxv] using z.2.2)⟩
                          = Sum.inr (Sum.inl ⟨x, z⟩) := by
                            have hxsub : (⟨v, hvX⟩ : {x : V // x ∈ X}) = x :=
                              Subtype.ext hxv.symm
                            have hzsub :
                                (⟨z.1, z.2.1, by simpa [hxv] using z.2.2⟩ :
                                  {z : V // z ∉ L ∧ G.Adj (↑x) z}) = z :=
                              Subtype.ext rfl
                            have hpair :
                                (⟨⟨v, hvX⟩,
                                  ⟨z.1, z.2.1, by simpa [hxv] using z.2.2⟩⟩ :
                                  Blocker) = ⟨x, z⟩ := by
                              cases hxsub
                              cases hzsub
                              rfl
                            simpa [embedNeighbor, z.2.1, hpair]
                      _ = y := h.2.symm
                · cases h.1
              · rcases hfiller with ⟨i, h | h⟩
                · have hvr : v = r := by
                    exact Sum.inl.inj h.1
                  exact (hr_not_mem_X (by simpa [hvr] using hvX)).elim
                · cases h.1
            calc
              H.degree (old v)
                  = (H.neighborFinset (old v)).card := by
                    rw [SimpleGraph.card_neighborFinset_eq_degree]
              _ ≤ (Finset.univ.image embedNeighbor).card := Finset.card_le_card hsubset
              _ ≤ Fintype.card {z : V // z ∈ G.neighborFinset v} :=
                    Finset.card_image_le
              _ = (G.neighborFinset v).card := Fintype.card_coe (G.neighborFinset v)
              _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
              _ = Delta := hregular v
          · by_cases hvr : v = r
            · subst v
              let rootContainer : Finset W :=
                (X.attach.image (fun x : {x : V // x ∈ X} => old x.1)) ∪
                  (Finset.univ.image rootFiller)
              have hsubset :
                  H.neighborFinset (old r) ⊆ rootContainer := by
                intro y hy
                have hadj : H.Adj (old r) y := (H.mem_neighborFinset (old r) y).mp hy
                rcases hadj with hlocal | hblock | hfiller
                · rcases hlocal with ⟨a, b, ha, hyb, _haL, hbL, hab⟩
                  cases ha
                  have hbX : b ∈ X := by
                    rw [Finset.mem_insert] at hbL
                    rcases hbL with hbr | hbX
                    · subst b
                      exact (G.loopless.irrefl r hab).elim
                    · exact hbX
                  subst y
                  refine Finset.mem_union_left _ ?_
                  exact Finset.mem_image.mpr ⟨⟨b, hbX⟩, by simp, rfl⟩
                · rcases hblock with ⟨x, z, h | h⟩
                  · have hr_eq_x : r = x.1 := by
                      exact Sum.inl.inj h.1
                    exact (hr_not_mem_X (by simpa [← hr_eq_x] using x.2)).elim
                  · cases h.1
                · rcases hfiller with ⟨i, h | h⟩
                  · refine Finset.mem_union_right _ ?_
                    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.2.symm⟩
                  · cases h.1
              have hroot_card :
                  rootContainer.card ≤ X.card + (Delta - X.card) := by
                calc
                  rootContainer.card
                      ≤ (X.attach.image (fun x : {x : V // x ∈ X} => old x.1)).card +
                          (Finset.univ.image rootFiller).card := Finset.card_union_le _ _
                  _ ≤ X.card + (Delta - X.card) := by
                    gcongr
                    · calc
                        (X.attach.image (fun x : {x : V // x ∈ X} => old x.1)).card
                            ≤ Fintype.card {x : V // x ∈ X} := Finset.card_image_le
                        _ = X.card := Fintype.card_coe X
                    · calc
                        (Finset.univ.image rootFiller).card
                            ≤ Fintype.card (Fin (Delta - X.card)) := Finset.card_image_le
                        _ = Delta - X.card := Fintype.card_fin (Delta - X.card)
              calc
                H.degree (old r)
                    = (H.neighborFinset (old r)).card := by
                      rw [SimpleGraph.card_neighborFinset_eq_degree]
                _ ≤ rootContainer.card := Finset.card_le_card hsubset
                _ ≤ X.card + (Delta - X.card) := hroot_card
                _ = Delta := Nat.add_sub_cancel' hX_card_le_Delta
            · have hempty : H.neighborFinset (old v) = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro y hy
                have hadj : H.Adj (old v) y := (H.mem_neighborFinset (old v) y).mp hy
                rcases hadj with hlocal | hblock | hfiller
                · rcases hlocal with ⟨a, b, ha, _hyb, haL, _hbL, _hab⟩
                  cases ha
                  rw [Finset.mem_insert] at haL
                  rcases haL with hvr' | hvX'
                  · exact hvr hvr'
                  · exact hvX hvX'
                · rcases hblock with ⟨x, z, h | h⟩
                  · have hv_eq_x : v = x.1 := by
                      exact Sum.inl.inj h.1
                    exact hvX (by simpa [← hv_eq_x] using x.2)
                  · cases h.1
                · rcases hfiller with ⟨i, h | h⟩
                  · have hvr' : v = r := by
                      exact Sum.inl.inj h.1
                    exact hvr hvr'
                  · cases h.1
              calc
                H.degree (old v)
                    = (H.neighborFinset (old v)).card := by
                      rw [SimpleGraph.card_neighborFinset_eq_degree]
                _ = 0 := by rw [hempty, Finset.card_empty]
                _ ≤ Delta := Nat.zero_le Delta
      | inr rest =>
          cases rest with
          | inl blocker =>
              rcases blocker with ⟨x, z⟩
              have hsingle : H.neighborFinset (Sum.inr (Sum.inl ⟨x, z⟩)) ⊆ {old x.1} := by
                intro y hy
                have hadj :
                    H.Adj (Sum.inr (Sum.inl ⟨x, z⟩)) y :=
                  (H.mem_neighborFinset (Sum.inr (Sum.inl ⟨x, z⟩)) y).mp hy
                rcases hadj with hlocal | hblock | hfiller
                · rcases hlocal with ⟨a, b, ha, _hyb, _haL, _hbL, _hab⟩
                  cases ha
                · rcases hblock with ⟨x', z', h | h⟩
                  · cases h.1
                  · have hblock_eq : (⟨x', z'⟩ : Blocker) = ⟨x, z⟩ := by
                      exact (Sum.inl.inj (Sum.inr.inj h.1)).symm
                    have hx'_eq : x' = x := congrArg Sigma.fst hblock_eq
                    simpa [h.2, hx'_eq]
                · rcases hfiller with ⟨i, h | h⟩
                  · cases h.1
                  · cases h.1
              calc
                H.degree (Sum.inr (Sum.inl ⟨x, z⟩))
                    = (H.neighborFinset (Sum.inr (Sum.inl ⟨x, z⟩))).card := by
                      rw [SimpleGraph.card_neighborFinset_eq_degree]
                _ ≤ ({old x.1} : Finset W).card := Finset.card_le_card hsingle
                _ = 1 := Finset.card_singleton _
                _ ≤ Delta := hDelta_pos
          | inr i =>
              have hsingle : H.neighborFinset (rootFiller i) ⊆ {old r} := by
                intro y hy
                have hadj : H.Adj (rootFiller i) y :=
                  (H.mem_neighborFinset (rootFiller i) y).mp hy
                rcases hadj with hlocal | hblock | hfiller
                · rcases hlocal with ⟨a, b, ha, _hyb, _haL, _hbL, _hab⟩
                  cases ha
                · rcases hblock with ⟨x, z, h | h⟩
                  · cases h.1
                  · cases h.1
                · rcases hfiller with ⟨j, h | h⟩
                  · cases h.1
                  · simpa [h.2]
              calc
                H.degree (rootFiller i)
                    = (H.neighborFinset (rootFiller i)).card := by
                      rw [SimpleGraph.card_neighborFinset_eq_degree]
                _ ≤ ({old r} : Finset W).card := Finset.card_le_card hsingle
                _ = 1 := Finset.card_singleton _
                _ ≤ Delta := hDelta_pos
    have hcompletion :
        ∃ (V' : Type u) (instF : Fintype V') (instD : DecidableEq V')
            (G' : SimpleGraph V') (instAdj : DecidableRel G'.Adj),
          letI : Fintype V' := instF
          letI : DecidableEq V' := instD
          letI : DecidableRel G'.Adj := instAdj
          ∃ φ : W → V',
            Function.Injective φ ∧
              (∀ a b : W, G'.Adj (φ a) (φ b) ↔ H.Adj a b) ∧
              (∀ v' : V', G'.degree v' = Delta) :=
      FiniteSimpleRegularCompletion H Delta hH_degree_le
    obtain
      ⟨V', instF, instD, G', instAdj, φW, hφW_inj, hφW_adj, hG'_regular⟩ :=
        hcompletion
    letI : Fintype V' := instF
    letI : DecidableEq V' := instD
    letI : DecidableRel G'.Adj := instAdj
    let φ : V → V' := fun v => φW (old v)
    have hgamma_pos : 0 < gamma := hsampling.1
    have hgamma_le_Delta : gamma ≤ (Delta : ℝ) :=
      RandomIndependentSetSamplingGammaLeDelta (G := G) (Delta := Delta)
        (gamma := gamma) (μ := μ) ⟨r⟩ hDelta_pos hsampling
    obtain ⟨μ', hsampling'⟩ :=
      SamplingRegularGraphSamplingLawExists (G := G') (Delta := Delta)
        (gamma := gamma) hG'_regular hgamma_pos hgamma_le_Delta
    have hH_degree_old_root : H.degree (old r) = Delta := by
      apply le_antisymm
      · exact hH_degree_le (old r)
      · let rootNeighbor : ({x : V // x ∈ X} ⊕ Fin (Delta - X.card)) → W := fun y =>
          match y with
          | Sum.inl x => old x.1
          | Sum.inr i => rootFiller i
        have hrootNeighbor_inj : Function.Injective rootNeighbor := by
          intro a b h
          cases a with
          | inl a =>
              cases b with
              | inl b =>
                  exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
              | inr j =>
                  cases h
          | inr i =>
              cases b with
              | inl b =>
                  cases h
              | inr j =>
                  have hij : i = j := Sum.inr.inj (Sum.inr.inj h)
                  subst j
                  rfl
        have hrootNeighbor_subset :
            (Finset.univ.image rootNeighbor) ⊆ H.neighborFinset (old r) := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
          cases a with
          | inl x =>
              apply (H.mem_neighborFinset (old r) (old x.1)).mpr
              exact Or.inl ⟨r, x.1, rfl, rfl, by simp [L], by simp [L, x.2], hX x.1 x.2⟩
          | inr i =>
              apply (H.mem_neighborFinset (old r) (rootFiller i)).mpr
              exact Or.inr (Or.inr ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
        calc
          Delta = X.card + (Delta - X.card) := (Nat.add_sub_cancel' hX_card_le_Delta).symm
          _ = Fintype.card ({x : V // x ∈ X} ⊕ Fin (Delta - X.card)) := by
                simp [Fintype.card_coe]
          _ = (Finset.univ.image rootNeighbor).card := by
                rw [Finset.card_image_of_injective _ hrootNeighbor_inj]
                simp
          _ ≤ (H.neighborFinset (old r)).card := Finset.card_le_card hrootNeighbor_subset
          _ = H.degree (old r) := SimpleGraph.card_neighborFinset_eq_degree H (old r)
    have hH_degree_old_X : ∀ x : V, x ∈ X → H.degree (old x) = Delta := by
      intro x hx
      apply le_antisymm
      · exact hH_degree_le (old x)
      · let embedNeighbor :
            {z : V // z ∈ G.neighborFinset x} → W := fun z =>
              if hzL : z.1 ∈ L then
                old z.1
              else
                Sum.inr (Sum.inl
                  ⟨⟨x, hx⟩, ⟨z.1, hzL, (G.mem_neighborFinset x z.1).mp z.2⟩⟩)
        have hxL : x ∈ L := by simp [L, hx]
        have hembed_mem :
            ∀ z : {z : V // z ∈ G.neighborFinset x},
              embedNeighbor z ∈ H.neighborFinset (old x) := by
          intro z
          have hxz : G.Adj x z.1 := (G.mem_neighborFinset x z.1).mp z.2
          by_cases hzL : z.1 ∈ L
          · apply (H.mem_neighborFinset (old x) (embedNeighbor z)).mpr
            simp only [embedNeighbor, hzL, dite_true]
            exact Or.inl ⟨x, z.1, rfl, rfl, hxL, hzL, hxz⟩
          · apply (H.mem_neighborFinset (old x) (embedNeighbor z)).mpr
            simp only [embedNeighbor, hzL, dite_false]
            exact Or.inr (Or.inl
              ⟨⟨x, hx⟩, ⟨z.1, hzL, hxz⟩, Or.inl ⟨rfl, rfl⟩⟩)
        have hembed_inj : Function.Injective embedNeighbor := by
          intro a b h
          by_cases haL : a.1 ∈ L
          · by_cases hbL : b.1 ∈ L
            · simp only [embedNeighbor, haL, hbL, dite_true] at h
              exact Subtype.ext (Sum.inl.inj h)
            · simp only [embedNeighbor, haL, hbL, dite_true, dite_false] at h
              cases h
          · by_cases hbL : b.1 ∈ L
            · simp only [embedNeighbor, haL, hbL, dite_false, dite_true] at h
              cases h
            · simp only [embedNeighbor, haL, hbL, dite_false] at h
              have hblock :
                  (⟨⟨x, hx⟩,
                    ⟨a.1, haL, (G.mem_neighborFinset x a.1).mp a.2⟩⟩ : Blocker) =
                    ⟨⟨x, hx⟩,
                      ⟨b.1, hbL, (G.mem_neighborFinset x b.1).mp b.2⟩⟩ := by
                exact Sum.inl.inj (Sum.inr.inj h)
              have hz : a.1 = b.1 := congrArg (fun q : Blocker => q.2.1) hblock
              exact Subtype.ext hz
        have himage_subset :
            (Finset.univ.image embedNeighbor) ⊆ H.neighborFinset (old x) := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨z, _hz, rfl⟩
          exact hembed_mem z
        calc
          Delta = G.degree x := (hregular x).symm
          _ = (G.neighborFinset x).card := (SimpleGraph.card_neighborFinset_eq_degree G x).symm
          _ = Fintype.card {z : V // G.Adj x z} := by
                let e : {z : V // z ∈ G.neighborFinset x} ≃ {z : V // G.Adj x z} :=
                  { toFun := fun z => ⟨z.1, (G.mem_neighborFinset x z.1).mp z.2⟩
                    invFun := fun z => ⟨z.1, (G.mem_neighborFinset x z.1).mpr z.2⟩
                    left_inv := by
                      intro z
                      rfl
                    right_inv := by
                      intro z
                      rfl }
                calc
                  (G.neighborFinset x).card =
                      Fintype.card {z : V // z ∈ G.neighborFinset x} :=
                    (Fintype.card_coe (G.neighborFinset x)).symm
                  _ = Fintype.card {z : V // G.Adj x z} := Fintype.card_congr e
          _ = (Finset.univ.image embedNeighbor).card := by
                rw [Finset.card_image_of_injective _ hembed_inj]
                simp only [Finset.card_univ, SimpleGraph.mem_neighborFinset]
          _ ≤ (H.neighborFinset (old x)).card := Finset.card_le_card himage_subset
          _ = H.degree (old x) := SimpleGraph.card_neighborFinset_eq_degree H (old x)
    have hcompleted_neighbor_from_H :
        ∀ x : V, x ∈ X → ∀ {w' : V'},
          G'.Adj (φW (old x)) w' → ∃ y : W, w' = φW y ∧ H.Adj (old x) y := by
      intro x hx w' hxw'
      let imageNeighbors : Finset V' := (H.neighborFinset (old x)).image φW
      have himage_subset : imageNeighbors ⊆ G'.neighborFinset (φW (old x)) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
        apply (G'.mem_neighborFinset (φW (old x)) (φW z)).mpr
        exact (hφW_adj (old x) z).mpr ((H.mem_neighborFinset (old x) z).mp hz)
      have himage_card : imageNeighbors.card = Delta := by
        calc
          imageNeighbors.card = (H.neighborFinset (old x)).card := by
              rw [Finset.card_image_of_injOn]
              intro a _ha b _hb hab
              exact hφW_inj hab
          _ = H.degree (old x) := SimpleGraph.card_neighborFinset_eq_degree H (old x)
          _ = Delta := hH_degree_old_X x hx
      have htarget_card : (G'.neighborFinset (φW (old x))).card = Delta := by
        calc
          (G'.neighborFinset (φW (old x))).card = G'.degree (φW (old x)) :=
            SimpleGraph.card_neighborFinset_eq_degree G' (φW (old x))
          _ = Delta := hG'_regular (φW (old x))
      have heq : imageNeighbors = G'.neighborFinset (φW (old x)) := by
        apply Finset.eq_of_subset_of_card_le himage_subset
        rw [himage_card, htarget_card]
      have hwmem : w' ∈ imageNeighbors := by
        rw [heq]
        exact (G'.mem_neighborFinset (φW (old x)) w').mpr hxw'
      rcases Finset.mem_image.mp hwmem with ⟨y, hy, hyw⟩
      exact ⟨y, hyw.symm, (H.mem_neighborFinset (old x) y).mp hy⟩
    refine ⟨V', instF, instD, G', instAdj, ?_⟩
    refine ⟨φ, φ r, X.image φ, μ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact hold_injective (hφW_inj hab)
    · rfl
    · rfl
    · intro v'
      exact hG'_regular v'
    · intro a b ha hb
      exact (hlocal_preserved a b ha hb).trans (hφW_adj (old a) (old b)).symm
    · intro u hu v hv huv hcommon
      rcases hcommon with ⟨w', huw', hvw', hw_ne_root, hw_not_adj_root⟩
      rcases hcompleted_neighbor_from_H u hu huw' with ⟨yu, hyu_image, hyu_adj⟩
      rcases hcompleted_neighbor_from_H v hv hvw' with ⟨yv, hyv_image, hyv_adj⟩
      have hy_eq : yu = yv := hφW_inj (by rw [← hyu_image, ← hyv_image])
      subst yv
      have hroot_adj_or_eq : φW yu = φW (old r) ∨ G'.Adj (φW (old r)) (φW yu) := by
        rcases hyu_adj with hlocal | hblock | hfiller
        · rcases hlocal with ⟨a, b, ha, hyb, _haL, hbL, hub⟩
          cases ha
          subst yu
          rw [Finset.mem_insert] at hbL
          rcases hbL with hbr | hbX
          · left
            subst b
            rfl
          · right
            exact (hφW_adj (old r) (old b)).mpr
              (Or.inl ⟨r, b, rfl, rfl, by simp [L], by simp [L, hbX], hX b hbX⟩)
        · rcases hblock with ⟨x, z, h | h⟩
          · have hxu : x.1 = u := (Sum.inl.inj h.1).symm
            rw [h.2] at hyv_adj ⊢
            rcases hyv_adj with hlocal_v | hblock_v | hfiller_v
            · rcases hlocal_v with ⟨a, b, ha, hb, _haL, _hbL, _hab⟩
              cases hb
            · rcases hblock_v with ⟨xv, zv, hvcase | hvcase⟩
              · have hblock_eq : (⟨xv, zv⟩ : Blocker) = ⟨x, z⟩ := by
                  exact (Sum.inl.inj (Sum.inr.inj hvcase.2)).symm
                have hxv_eq_x : xv = x := congrArg Sigma.fst hblock_eq
                have hv_eq_u : v = u := by
                  calc
                    v = xv.1 := Sum.inl.inj hvcase.1
                    _ = x.1 := congrArg Subtype.val hxv_eq_x
                    _ = u := hxu
                exact (huv hv_eq_u.symm).elim
              · cases hvcase.1
            · rcases hfiller_v with ⟨i, hvcase | hvcase⟩
              · cases hvcase.2
              · cases hvcase.1
          · cases h.1
        · rcases hfiller with ⟨i, h | h⟩
          · have hur : u = r := Sum.inl.inj h.1
            exact (G.loopless.irrefl r (by simpa [hur] using hX u hu)).elim
          · cases h.1
      rcases hroot_adj_or_eq with hroot_eq | hroot_adj
      · exact hw_ne_root (by simpa [hyu_image, φ] using hroot_eq)
      · exact hw_not_adj_root (by simpa [hyu_image, φ] using hroot_adj)
    · exact hsampling'
    · exact
        SamplingSplitOutsideBlockerEventMonotonicity (G := G) (G' := G')
          (Delta := Delta) (gamma := gamma) hregular hG'_regular μ μ'
          hsampling hsampling' φ r X
          (by
            intro a b hab
            exact hold_injective (hφW_inj hab))
          hX
          (by
            intro a b ha hb
            exact (hlocal_preserved a b ha hb).trans (hφW_adj (old a) (old b)).symm)
          (by
            intro blocker
            exact φW (Sum.inr (Sum.inl blocker)))
            (by
              intro blocker₁ blocker₂ h
              have hW :
                  Sum.inr (Sum.inl blocker₁) = Sum.inr (Sum.inl blocker₂) :=
                hφW_inj h
              exact Sum.inl.inj (Sum.inr.inj hW))
            (by
              intro x hx z hz y hy h_eq
              have hW :
                  Sum.inr (Sum.inl (⟨⟨x, hx⟩, ⟨z, hz⟩⟩ : Blocker)) = old y :=
                hφW_inj h_eq
              cases hW)
            (by
              intro x hx z hz
              exact (hφW_adj (old x)
              (Sum.inr (Sum.inl ⟨⟨x, hx⟩, ⟨z, hz⟩⟩))).mpr
                (Or.inr (Or.inl
                  ⟨⟨x, hx⟩, ⟨z, hz⟩, Or.inl ⟨rfl, rfl⟩⟩)))
          (by
            intro x hx z hz y hy hy_adj
            have hr_not_mem_X : r ∉ X := by
              intro hrX
              exact G.loopless.irrefl r (hX r hrX)
            have hH :
                H.Adj (old y) (Sum.inr (Sum.inl ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) :=
              (hφW_adj (old y)
                (Sum.inr (Sum.inl ⟨⟨x, hx⟩, ⟨z, hz⟩⟩))).mp hy_adj
            rcases hH with hlocal | hblock | hfiller
            · rcases hlocal with ⟨a, b, ha, hb, _haL, _hbL, _hab⟩
              cases hb
            · rcases hblock with ⟨x', z', h | h⟩
              · have hblock_eq :
                    (⟨x', z'⟩ : Blocker) = ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ := by
                  exact (Sum.inl.inj (Sum.inr.inj h.2)).symm
                have hx'_eq : x' = ⟨x, hx⟩ := congrArg Sigma.fst hblock_eq
                calc
                  y = x'.1 := Sum.inl.inj h.1
                  _ = x := congrArg Subtype.val hx'_eq
              · cases h.1
            · rcases hfiller with ⟨i, h | h⟩
              · have hyr : y = r := Sum.inl.inj h.1
                exact (hr_not_mem_X (by simpa [hyr] using hy)).elim
              · cases h.1)
          (by
            intro x hx z hz hr_adj
            have hr_not_mem_X : r ∉ X := by
              intro hrX
              exact G.loopless.irrefl r (hX r hrX)
            have hH :
                H.Adj (old r) (Sum.inr (Sum.inl ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) :=
              (hφW_adj (old r)
                (Sum.inr (Sum.inl ⟨⟨x, hx⟩, ⟨z, hz⟩⟩))).mp hr_adj
            rcases hH with hlocal | hblock | hfiller
            · rcases hlocal with ⟨a, b, ha, hb, _haL, _hbL, _hab⟩
              cases hb
            · rcases hblock with ⟨x', z', h | h⟩
              · have hrx : r = x'.1 := Sum.inl.inj h.1
                exact hr_not_mem_X (by simpa [← hrx] using x'.2)
              · cases h.1
            · rcases hfiller with ⟨i, h | h⟩
              · cases h.2
              · cases h.1)
          (by
            intro x hx w' hxw'
            have hr_not_mem_X : r ∉ X := by
              intro hrX
              exact G.loopless.irrefl r (hX r hrX)
            rcases hcompleted_neighbor_from_H x hx hxw' with ⟨y, hy_image, hy_adj⟩
            rcases hy_adj with hlocal | hblock | hfiller
            · rcases hlocal with ⟨a, b, ha, hyb, _haL, hbL, hab⟩
              cases ha
              subst y
              exact Or.inl ⟨b, by simpa [L] using hbL, by simpa [φ] using hy_image, hab⟩
            · rcases hblock with ⟨x', z', h | h⟩
              · have hxx' : x = x'.1 := Sum.inl.inj h.1
                have hz : z'.1 ∉ insert r X ∧ G.Adj x z'.1 := by
                  simpa [L, hxx'] using z'.2
                refine Or.inr ⟨z'.1, hz, ?_⟩
                have hxsub : (⟨x, hx⟩ : {x : V // x ∈ X}) = x' :=
                  Subtype.ext hxx'
                have hblocker :
                    (⟨⟨x, hx⟩, ⟨z'.1, hz⟩⟩ : Blocker) = ⟨x', z'⟩ := by
                  cases hxsub
                  have hzsub :
                      (⟨z'.1, hz⟩ : {z : V // z ∉ L ∧ G.Adj x z}) = z' :=
                    Subtype.ext rfl
                  cases hzsub
                  rfl
                calc
                  w' = φW y := hy_image
                  _ = φW (Sum.inr (Sum.inl ⟨x', z'⟩)) := by rw [h.2]
                  _ = φW (Sum.inr (Sum.inl
                        (⟨⟨x, hx⟩, ⟨z'.1, hz⟩⟩ : Blocker))) := by
                      rw [hblocker]
              · cases h.1
            · rcases hfiller with ⟨i, h | h⟩
              · have hxr : x = r := Sum.inl.inj h.1
                exact (hr_not_mem_X (by simpa [hxr] using hx)).elim
              · cases h.1)
