import Tablet.FiniteEvenTypePairing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

universe u

-- [TABLET NODE: FiniteSimpleRegularCompletion]
theorem FiniteSimpleRegularCompletion :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ,
          (∀ v : V, G.degree v ≤ Delta) →
          ∃ (V' : Type u) (instF : Fintype V') (instD : DecidableEq V')
              (G' : SimpleGraph V') (instAdj : DecidableRel G'.Adj),
            letI : Fintype V' := instF
            letI : DecidableEq V' := instD
            letI : DecidableRel G'.Adj := instAdj
            ∃ φ : V → V',
              Function.Injective φ ∧
                (∀ a b : V, G'.Adj (φ a) (φ b) ↔ G.Adj a b) ∧
                (∀ v' : V', G'.degree v' = Delta) := by
-- BODY
  intro V instFintype instDecEq G instDecRel Delta hmax
  classical
  by_cases hDelta : Delta = 0
  · subst Delta
    refine ⟨V, instFintype, instDecEq, G, instDecRel, ?_⟩
    refine ⟨id, ?_, ?_, ?_⟩
    · intro a b h
      exact h
    · intro a b
      rfl
    · intro v
      exact Nat.eq_zero_of_le_zero (hmax v)
  · have hDelta_pos : 0 < Delta := Nat.pos_of_ne_zero hDelta
    let OldStub := Sigma (fun v : V => Fin (Delta - G.degree v))
    have oldStubOwner : OldStub → V := fun s => s.1
    have hOldStubCard :
        Fintype.card OldStub =
          Finset.univ.sum (fun v : V => Delta - G.degree v) := by
      simp [OldStub]
    have hDeltaOdd_of_oldStubOdd : Odd (Fintype.card OldStub) → Odd Delta := by
      intro hOldOdd
      have hsum_add :
          (Finset.univ.sum (fun v : V => Delta - G.degree v)) +
              (Finset.univ.sum fun v : V => G.degree v) =
            Delta * Fintype.card V := by
        rw [← Finset.sum_add_distrib]
        trans Finset.univ.sum (fun _v : V => Delta)
        · apply Finset.sum_congr rfl
          intro v _hv
          exact Nat.sub_add_cancel (hmax v)
        · simp [mul_comm]
      have hdegree_even : Even (Finset.univ.sum fun v : V => G.degree v) := by
        rw [G.sum_degrees_eq_twice_card_edges]
        exact even_two_mul G.edgeFinset.card
      have hprod_odd : Odd (Delta * Fintype.card V) := by
        rw [← hsum_add, ← hOldStubCard]
        exact hOldOdd.add_even hdegree_even
      exact Nat.Odd.of_mul_left hprod_odd
    have hAdjustedStubPairing :
        ∃ (AdjustedStub : Type u) (_ : Fintype AdjustedStub)
            (BaseOwner : Type u) (_ : Fintype BaseOwner)
            (oldBase : V → BaseOwner) (parityBase : Option BaseOwner)
            (stubOwner : AdjustedStub → BaseOwner)
            (P : Type u) (_ : Fintype P) (pair : P → Fin 2 → AdjustedStub),
          Function.Bijective (fun x : P × Fin 2 => pair x.1 x.2) ∧
            Function.Injective oldBase ∧
            (∀ b : BaseOwner, (∃ v : V, b = oldBase v) ∨ parityBase = some b) ∧
            (∀ p : BaseOwner, parityBase = some p → ∀ v : V, p ≠ oldBase v) ∧
            (∀ v : V,
              Nat.card {s : AdjustedStub // stubOwner s = oldBase v} =
                Delta - G.degree v) ∧
            (match parityBase with
              | none => True
              | some p =>
                  Nat.card {s : AdjustedStub // stubOwner s = p} = Delta) := by
      by_cases hOldEven : Even (Fintype.card OldStub)
      · let AdjustedStub : Type u := OldStub
        let BaseOwner : Type u := V
        let oldBase : V → BaseOwner := id
        let parityBase : Option BaseOwner := none
        let stubOwner : AdjustedStub → BaseOwner := fun s => s.1
        have hOldOwnerCount :
            ∀ v : V,
              Nat.card {s : AdjustedStub // stubOwner s = oldBase v} =
                Delta - G.degree v := by
          intro v
          let e :
              {s : AdjustedStub // stubOwner s = oldBase v} ≃
                Fin (Delta - G.degree v) :=
            { toFun := fun s => by
                rcases s with ⟨⟨w, i⟩, h⟩
                dsimp [AdjustedStub, stubOwner, oldBase] at h
                subst w
                exact i
              invFun := fun i => ⟨⟨v, i⟩, rfl⟩
              left_inv := by
                rintro ⟨⟨w, i⟩, h⟩
                dsimp [AdjustedStub, stubOwner, oldBase] at h
                subst w
                rfl
              right_inv := by
                intro i
                rfl }
          simpa using (Nat.card_congr e)
        obtain ⟨P, instP, pair, hpair⟩ :=
          FiniteEvenTypePairing (α := AdjustedStub) hOldEven
        refine
          ⟨AdjustedStub, inferInstance, BaseOwner, inferInstance, oldBase, parityBase,
            stubOwner, P, instP, pair, hpair, ?_, ?_, ?_, ?_, trivial⟩
        · intro a b h
          simpa [oldBase] using h
        · intro b
          exact Or.inl ⟨b, rfl⟩
        · intro p hp
          simp [parityBase] at hp
        · intro v
          simpa using hOldOwnerCount v
      · have hOldOdd : Odd (Fintype.card OldStub) := Nat.not_even_iff_odd.mp hOldEven
        have hDeltaOdd : Odd Delta := hDeltaOdd_of_oldStubOdd hOldOdd
        let AdjustedStub : Type u := OldStub ⊕ Fin Delta
        let BaseOwner : Type u := Option V
        let oldBase : V → BaseOwner := some
        let parityBase : Option BaseOwner := some none
        let stubOwner : AdjustedStub → BaseOwner := fun s =>
          match s with
          | Sum.inl t => some t.1
          | Sum.inr _ => none
        have hOldOwnerCount :
            ∀ v : V,
              Nat.card {s : AdjustedStub // stubOwner s = oldBase v} =
                Delta - G.degree v := by
          intro v
          let e :
              {s : AdjustedStub // stubOwner s = oldBase v} ≃
                Fin (Delta - G.degree v) :=
            { toFun := fun s => by
                rcases s with ⟨s, h⟩
                cases s with
                | inl t =>
                    rcases t with ⟨w, i⟩
                    dsimp [stubOwner, oldBase] at h
                    injection h with hw
                    subst w
                    exact i
                | inr j =>
                    dsimp [stubOwner, oldBase] at h
                    contradiction
              invFun := fun i => ⟨Sum.inl ⟨v, i⟩, rfl⟩
              left_inv := by
                rintro ⟨s, h⟩
                cases s with
                | inl t =>
                    rcases t with ⟨w, i⟩
                    dsimp [stubOwner, oldBase] at h
                    injection h with hw
                    subst w
                    rfl
                | inr j =>
                    dsimp [stubOwner, oldBase] at h
                    contradiction
              right_inv := by
                intro i
                rfl }
          simpa using (Nat.card_congr e)
        have hParityOwnerCount :
            Nat.card {s : AdjustedStub // stubOwner s = (none : BaseOwner)} = Delta := by
          let e : {s : AdjustedStub // stubOwner s = (none : BaseOwner)} ≃ Fin Delta :=
            { toFun := fun s => by
                rcases s with ⟨s, h⟩
                cases s with
                | inl t =>
                    rcases t with ⟨w, i⟩
                    dsimp [stubOwner] at h
                    contradiction
                | inr j => exact j
              invFun := fun i => ⟨Sum.inr i, rfl⟩
              left_inv := by
                rintro ⟨s, h⟩
                cases s with
                | inl t =>
                    rcases t with ⟨w, i⟩
                    dsimp [stubOwner] at h
                    contradiction
                | inr j => rfl
              right_inv := by
                intro i
                rfl }
          simpa using (Nat.card_congr e)
        have hAdjustedEven : Even (Fintype.card AdjustedStub) := by
          have hcard : Fintype.card AdjustedStub = Fintype.card OldStub + Delta := by
            simp [AdjustedStub]
          rw [hcard]
          exact hOldOdd.add_odd hDeltaOdd
        obtain ⟨P, instP, pair, hpair⟩ :=
          FiniteEvenTypePairing (α := AdjustedStub) hAdjustedEven
        refine
          ⟨AdjustedStub, inferInstance, BaseOwner, inferInstance, oldBase, parityBase,
            stubOwner, P, instP, pair, hpair, ?_, ?_, ?_, ?_, ?_⟩
        · intro a b h
          exact Option.some.inj h
        · intro b
          cases b with
          | none =>
              exact Or.inr rfl
          | some v =>
              exact Or.inl ⟨v, rfl⟩
        · intro p hp v hpold
          dsimp [parityBase, oldBase] at hp hpold
          injection hp with hpnone
          subst p
          contradiction
        · intro v
          simpa using hOldOwnerCount v
        · simpa using hParityOwnerCount
    obtain
      ⟨AdjustedStub, instAdjustedStub, BaseOwner, instBaseOwner, oldBase, parityBase,
        stubOwner, P, instP, pair, hpair, hOldBaseInjective, hBaseOwnerExhaustive,
        hParityBaseDisjoint, hOldOwnerCount, hParityOwnerCount⟩ :=
      hAdjustedStubPairing
    letI : Fintype AdjustedStub := instAdjustedStub
    letI : Fintype BaseOwner := instBaseOwner
    letI : Fintype P := instP
    let BlockVertex : Type u := P × Fin (Delta + 1)
    let FinalVertex : Type u := BaseOwner ⊕ BlockVertex
    have instFinalVertex : Fintype FinalVertex := inferInstance
    let oldEmbedding : V → FinalVertex := fun v => Sum.inl (oldBase v)
    let G' : SimpleGraph FinalVertex :=
      { Adj := fun x y =>
          (∃ a b : V,
              x = Sum.inl (oldBase a) ∧ y = Sum.inl (oldBase b) ∧ G.Adj a b) ∨
            (∃ p : P, ∃ i j : Fin (Delta + 1),
              x = Sum.inr (p, i) ∧ y = Sum.inr (p, j) ∧ i ≠ j ∧
                ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))) ∨
            (∃ p : P,
              (x = Sum.inl (stubOwner (pair p 0)) ∧ y = Sum.inr (p, 0)) ∨
                (x = Sum.inr (p, 0) ∧ y = Sum.inl (stubOwner (pair p 0))) ∨
                (x = Sum.inl (stubOwner (pair p 1)) ∧ y = Sum.inr (p, 1)) ∨
                (x = Sum.inr (p, 1) ∧ y = Sum.inl (stubOwner (pair p 1))))
        symm := by
          intro x y hxy
          rcases hxy with hOld | hBlock | hExternal
          · rcases hOld with ⟨a, b, hx, hy, hab⟩
            exact Or.inl ⟨b, a, hy, hx, hab.symm⟩
          · rcases hBlock with ⟨p, i, j, hx, hy, hij, hdeleted⟩
            refine Or.inr (Or.inl ⟨p, j, i, hy, hx, hij.symm, ?_⟩)
            intro h
            apply hdeleted
            rcases h with h | h
            · exact Or.inr ⟨h.2, h.1⟩
            · exact Or.inl ⟨h.2, h.1⟩
          · rcases hExternal with ⟨p, h | h | h | h⟩
            · exact Or.inr (Or.inr ⟨p, Or.inr (Or.inl ⟨h.2, h.1⟩)⟩)
            · exact Or.inr (Or.inr ⟨p, Or.inl ⟨h.2, h.1⟩⟩)
            · exact Or.inr (Or.inr ⟨p, Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))⟩)
            · exact Or.inr (Or.inr ⟨p, Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))⟩)
        loopless := ⟨by
          intro x hxx
          rcases hxx with hOld | hBlock | hExternal
          · rcases hOld with ⟨a, b, hx, hy, hab⟩
            have hbase : oldBase a = oldBase b := by
              exact Sum.inl.inj (hx.symm.trans hy)
            have hab' : a = b := hOldBaseInjective hbase
            exact G.loopless.irrefl a (by simpa [hab'] using hab)
          · rcases hBlock with ⟨p, i, j, hx, hy, hij, _hdeleted⟩
            have hprod : (p, i) = (p, j) := by
              exact Sum.inr.inj (hx.symm.trans hy)
            exact hij (congrArg Prod.snd hprod)
          · rcases hExternal with ⟨p, h | h | h | h⟩
            · exact Sum.inl_ne_inr (h.1.symm.trans h.2)
            · exact Sum.inr_ne_inl (h.1.symm.trans h.2)
            · exact Sum.inl_ne_inr (h.1.symm.trans h.2)
            · exact Sum.inr_ne_inl (h.1.symm.trans h.2)⟩ }
    have instFinalDecEq : DecidableEq FinalVertex := Classical.decEq _
    have instFinalAdj : DecidableRel G'.Adj := Classical.decRel _
    have hOldEmbeddingInjective : Function.Injective oldEmbedding := by
      intro a b h
      exact hOldBaseInjective (Sum.inl.inj h)
    have hOldOldAdj :
        ∀ a b : V, G'.Adj (oldEmbedding a) (oldEmbedding b) ↔ G.Adj a b := by
      intro a b
      constructor
      · intro h
        rcases h with hOld | hBlock | hExternal
        · rcases hOld with ⟨c, d, hac, hbd, hcd⟩
          have hca : c = a := by
            apply hOldBaseInjective
            exact (Sum.inl.inj hac).symm
          have hdb : d = b := by
            apply hOldBaseInjective
            exact (Sum.inl.inj hbd).symm
          simpa [hca, hdb] using hcd
        · rcases hBlock with ⟨p, i, j, hx, _hy, _hij, _hdeleted⟩
          exact False.elim (Sum.inl_ne_inr hx)
        · rcases hExternal with ⟨p, h | h | h | h⟩
          · have hright := h.2
            change Sum.inl (oldBase b) = Sum.inr (p, 0) at hright
            exact False.elim (Sum.inl_ne_inr hright)
          · exact False.elim (Sum.inl_ne_inr h.1)
          · have hright := h.2
            change Sum.inl (oldBase b) = Sum.inr (p, 1) at hright
            exact False.elim (Sum.inl_ne_inr hright)
          · exact False.elim (Sum.inl_ne_inr h.1)
      · intro hab
        exact Or.inl ⟨a, b, rfl, rfl, hab⟩
    have hBlockBaseAdj :
        ∀ (p : P) (i : Fin (Delta + 1)) (b : BaseOwner),
          G'.Adj (Sum.inr (p, i)) (Sum.inl b) ↔
            (i = 0 ∧ b = stubOwner (pair p 0)) ∨
              (i = 1 ∧ b = stubOwner (pair p 1)) := by
      intro p i b
      constructor
      · intro h
        rcases h with hOld | hBlock | hExternal
        · rcases hOld with ⟨a, c, hx, _hy, _hac⟩
          exact False.elim (Sum.inr_ne_inl hx)
        · rcases hBlock with ⟨q, j, k, _hx, hy, _hjk, _hdeleted⟩
          exact False.elim (Sum.inl_ne_inr hy)
        · rcases hExternal with ⟨q, h | h | h | h⟩
          · exact False.elim (Sum.inr_ne_inl h.1)
          · have hp0 : (p, i) = (q, 0) := Sum.inr.inj h.1
            have hp : p = q := congrArg Prod.fst hp0
            have hi : i = 0 := congrArg Prod.snd hp0
            subst q
            exact Or.inl ⟨hi, Sum.inl.inj h.2⟩
          · exact False.elim (Sum.inr_ne_inl h.1)
          · have hp1 : (p, i) = (q, 1) := Sum.inr.inj h.1
            have hp : p = q := congrArg Prod.fst hp1
            have hi : i = 1 := congrArg Prod.snd hp1
            subst q
            exact Or.inr ⟨hi, Sum.inl.inj h.2⟩
      · intro h
        rcases h with ⟨hi, hb⟩ | ⟨hi, hb⟩
        · subst i
          subst b
          exact Or.inr (Or.inr ⟨p, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
        · subst i
          subst b
          exact Or.inr (Or.inr ⟨p, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)
    have hBlockBlockAdj :
        ∀ (p q : P) (i j : Fin (Delta + 1)),
          G'.Adj (Sum.inr (p, i)) (Sum.inr (q, j)) ↔
            p = q ∧ i ≠ j ∧
              ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
      intro p q i j
      constructor
      · intro h
        rcases h with hOld | hBlock | hExternal
        · rcases hOld with ⟨a, b, hx, _hy, _hab⟩
          exact False.elim (Sum.inr_ne_inl hx)
        · rcases hBlock with ⟨r, k, l, hx, hy, hkl, hdeleted⟩
          have hleft : (p, i) = (r, k) := Sum.inr.inj hx
          have hright : (q, j) = (r, l) := Sum.inr.inj hy
          have hpr : p = r := congrArg Prod.fst hleft
          have hqr : q = r := congrArg Prod.fst hright
          have hik : i = k := congrArg Prod.snd hleft
          have hjl : j = l := congrArg Prod.snd hright
          subst r
          subst q
          subst k
          subst l
          exact ⟨rfl, hkl, hdeleted⟩
        · rcases hExternal with ⟨r, h | h | h | h⟩
          · exact False.elim (Sum.inr_ne_inl h.1)
          · exact False.elim (Sum.inr_ne_inl h.2)
          · exact False.elim (Sum.inr_ne_inl h.1)
          · exact False.elim (Sum.inr_ne_inl h.2)
      · rintro ⟨hpq, hij, hdeleted⟩
        subst q
        exact Or.inr (Or.inl ⟨p, i, j, rfl, rfl, hij, hdeleted⟩)
    have hBaseBaseAdj :
        ∀ b c : BaseOwner,
          G'.Adj (Sum.inl b) (Sum.inl c) ↔
            ∃ a d : V, b = oldBase a ∧ c = oldBase d ∧ G.Adj a d := by
      intro b c
      constructor
      · intro h
        rcases h with hOld | hBlock | hExternal
        · rcases hOld with ⟨a, d, hb, hc, had⟩
          exact ⟨a, d, Sum.inl.inj hb, Sum.inl.inj hc, had⟩
        · rcases hBlock with ⟨p, i, j, hx, _hy, _hij, _hdeleted⟩
          exact False.elim (Sum.inl_ne_inr hx)
        · rcases hExternal with ⟨p, h | h | h | h⟩
          · exact False.elim (Sum.inl_ne_inr h.2)
          · exact False.elim (Sum.inl_ne_inr h.1)
          · exact False.elim (Sum.inl_ne_inr h.2)
          · exact False.elim (Sum.inl_ne_inr h.1)
      · rintro ⟨a, d, hb, hc, had⟩
        subst b
        subst c
        exact Or.inl ⟨a, d, rfl, rfl, had⟩
    have hBaseBlockAdj :
        ∀ (b : BaseOwner) (p : P) (i : Fin (Delta + 1)),
          G'.Adj (Sum.inl b) (Sum.inr (p, i)) ↔
            (i = 0 ∧ b = stubOwner (pair p 0)) ∨
              (i = 1 ∧ b = stubOwner (pair p 1)) := by
      intro b p i
      rw [G'.adj_comm]
      exact hBlockBaseAdj p i b
    have hParityBaseNoBaseAdj :
        ∀ p : BaseOwner, parityBase = some p →
          ∀ b : BaseOwner, ¬ G'.Adj (Sum.inl p) (Sum.inl b) := by
      intro p hp b hpb
      rw [hBaseBaseAdj] at hpb
      rcases hpb with ⟨a, d, hpa, _hbd, _had⟩
      exact hParityBaseDisjoint p hp a hpa
    have hPairSlotOwnerCount :
        ∀ b : BaseOwner,
          Nat.card {x : P × Fin 2 // stubOwner (pair x.1 x.2) = b} =
            Nat.card {s : AdjustedStub // stubOwner s = b} := by
      intro b
      let ePair : P × Fin 2 ≃ AdjustedStub :=
        Equiv.ofBijective (fun x : P × Fin 2 => pair x.1 x.2) hpair
      let e :
          {x : P × Fin 2 // stubOwner (pair x.1 x.2) = b} ≃
            {s : AdjustedStub // stubOwner s = b} :=
        { toFun := fun x => ⟨ePair x.1, by
              dsimp [ePair]
              simpa using x.2⟩
          invFun := fun s => ⟨ePair.symm s.1, by
              change stubOwner (ePair (ePair.symm s.1)) = b
              simpa using s.2⟩
          left_inv := by
            rintro ⟨x, hx⟩
            apply Subtype.ext
            exact ePair.symm_apply_apply x
          right_inv := by
            rintro ⟨s, hs⟩
            apply Subtype.ext
            exact ePair.apply_symm_apply s }
      exact Nat.card_congr e
    have hOldPairSlotOwnerCount :
        ∀ v : V,
          Nat.card {x : P × Fin 2 // stubOwner (pair x.1 x.2) = oldBase v} =
            Delta - G.degree v := by
      intro v
      rw [hPairSlotOwnerCount, hOldOwnerCount]
    have hParityPairSlotOwnerCount :
        ∀ p : BaseOwner, parityBase = some p →
          Nat.card {x : P × Fin 2 // stubOwner (pair x.1 x.2) = p} = Delta := by
      intro p hp
      rw [hPairSlotOwnerCount]
      simpa [hp] using hParityOwnerCount
    have hBaseBlockNeighborCount :
        ∀ b : BaseOwner,
          Nat.card {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)} =
            Nat.card {x : P × Fin 2 // stubOwner (pair x.1 x.2) = b} := by
      intro b
      let fin2ToBlock : Fin 2 → Fin (Delta + 1) := fun k =>
        ⟨k.1, by
          have hk : k.1 < 2 := k.2
          omega⟩
      have hfin2_zero : fin2ToBlock 0 = (0 : Fin (Delta + 1)) := by
        rfl
      have hfin2_one : fin2ToBlock 1 = (1 : Fin (Delta + 1)) := by
        ext
        simp [fin2ToBlock]
        rw [Nat.mod_eq_of_lt]
        omega
      let e :
          {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)} ≃
            {x : P × Fin 2 // stubOwner (pair x.1 x.2) = b} :=
        { toFun := fun z => by
            rcases z with ⟨⟨p, i⟩, hz⟩
            by_cases hi0 : i = 0
            · refine ⟨(p, 0), ?_⟩
              have h := (hBaseBlockAdj b p i).mp hz
              rcases h with ⟨_hi, hb⟩ | ⟨hi, hb⟩
              · exact hb.symm
              · have h01 : (0 : Fin (Delta + 1)) = 1 := by
                  simpa [hi0] using hi
                have hval := congrArg (fun t : Fin (Delta + 1) => (t : ℕ)) h01
                norm_num at hval
                exact False.elim (hDelta hval)
            · refine ⟨(p, 1), ?_⟩
              have h := (hBaseBlockAdj b p i).mp hz
              rcases h with ⟨hi, hb⟩ | ⟨_hi, hb⟩
              · exact False.elim (hi0 hi)
              · exact hb.symm
          invFun := fun x => by
            rcases x with ⟨⟨p, k⟩, hx⟩
            refine ⟨(p, fin2ToBlock k), ?_⟩
            fin_cases k
            · simpa [fin2ToBlock] using
                (hBaseBlockAdj b p 0).mpr (Or.inl ⟨rfl, hx.symm⟩)
            · have hk :
                  fin2ToBlock ((fun i => i) ⟨1, by decide⟩) =
                    (1 : Fin (Delta + 1)) := by
                ext
                simp [fin2ToBlock]
                rw [Nat.mod_eq_of_lt]
                omega
              rw [hk]
              exact (hBaseBlockAdj b p 1).mpr (Or.inr ⟨rfl, hx.symm⟩)
          left_inv := by
            rintro ⟨⟨p, i⟩, hz⟩
            apply Subtype.ext
            by_cases hi0 : i = 0
            · subst i
              simp [hfin2_zero]
            · have h := (hBaseBlockAdj b p i).mp hz
              have hi1 : i = 1 := by
                rcases h with ⟨hi, _hb⟩ | ⟨hi, _hb⟩
                · exact False.elim (hi0 hi)
                · exact hi
              subst i
              simp [hDelta, hfin2_one]
          right_inv := by
            rintro ⟨⟨p, k⟩, hx⟩
            apply Subtype.ext
            fin_cases k <;> simp [hDelta, hfin2_zero, hfin2_one] }
      exact Nat.card_congr e
    have hOldBaseBlockNeighborCount :
        ∀ v : V,
          Nat.card {z : BlockVertex // G'.Adj (Sum.inl (oldBase v)) (Sum.inr z)} =
            Delta - G.degree v := by
      intro v
      rw [hBaseBlockNeighborCount, hOldPairSlotOwnerCount]
    have hParityBaseBlockNeighborCount :
        ∀ p : BaseOwner, parityBase = some p →
          Nat.card {z : BlockVertex // G'.Adj (Sum.inl p) (Sum.inr z)} = Delta := by
      intro p hp
      rw [hBaseBlockNeighborCount, hParityPairSlotOwnerCount p hp]
    have hOldBaseBaseNeighborCount :
        ∀ v : V,
          Nat.card {b : BaseOwner // G'.Adj (Sum.inl (oldBase v)) (Sum.inl b)} =
            G.degree v := by
      intro v
      let e :
          {b : BaseOwner // G'.Adj (Sum.inl (oldBase v)) (Sum.inl b)} ≃
            {w : V // G.Adj v w} :=
        { toFun := fun b => by
            let h1 := (hBaseBaseAdj (oldBase v) b.1).mp b.2
            let a := Classical.choose h1
            let h2 := Classical.choose_spec h1
            let w := Classical.choose h2
            have hw := Classical.choose_spec h2
            have hva : v = a := hOldBaseInjective hw.1
            have hAdj : G.Adj a w := by
              change G.Adj (Classical.choose h1) (Classical.choose h2)
              exact hw.2.2
            exact ⟨w, by
              rw [hva]
              exact hAdj⟩
          invFun := fun w =>
            ⟨oldBase w.1, (hBaseBaseAdj (oldBase v) (oldBase w.1)).mpr
              ⟨v, w.1, rfl, rfl, w.2⟩⟩
          left_inv := by
            intro b
            apply Subtype.ext
            let h1 := (hBaseBaseAdj (oldBase v) b.1).mp b.2
            let a := Classical.choose h1
            let h2 := Classical.choose_spec h1
            let w := Classical.choose h2
            have hw := Classical.choose_spec h2
            exact hw.2.1.symm
          right_inv := by
            intro w
            apply Subtype.ext
            let h1 := (hBaseBaseAdj (oldBase v) (oldBase w.1)).mp
              ((hBaseBaseAdj (oldBase v) (oldBase w.1)).mpr
                ⟨v, w.1, rfl, rfl, w.2⟩)
            let a := Classical.choose h1
            let h2 := Classical.choose_spec h1
            let d := Classical.choose h2
            have hd := Classical.choose_spec h2
            change d = w.1
            exact (hOldBaseInjective hd.2.1).symm }
      calc
        Nat.card {b : BaseOwner // G'.Adj (Sum.inl (oldBase v)) (Sum.inl b)}
            = Nat.card {w : V // G.Adj v w} := Nat.card_congr e
        _ = G.degree v := by
          let eNeighbor :
              {w : V // G.Adj v w} ≃ {w : V // w ∈ G.neighborFinset v} :=
            { toFun := fun w => ⟨w.1, (G.mem_neighborFinset v w.1).mpr w.2⟩
              invFun := fun w => ⟨w.1, (G.mem_neighborFinset v w.1).mp w.2⟩
              left_inv := by
                intro w
                rfl
              right_inv := by
                intro w
                rfl }
          calc
            Nat.card {w : V // G.Adj v w}
                = Nat.card {w : V // w ∈ G.neighborFinset v} := Nat.card_congr eNeighbor
            _ = Fintype.card {w : V // w ∈ G.neighborFinset v} := Nat.card_eq_fintype_card
            _ = (G.neighborFinset v).card := Fintype.card_coe (G.neighborFinset v)
            _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
    have hNeighborSubtypeDegree :
        ∀ x : FinalVertex,
          Nat.card {y : FinalVertex // G'.Adj x y} = G'.degree x := by
      intro x
      let eNeighbor :
          {y : FinalVertex // G'.Adj x y} ≃
            {y : FinalVertex // y ∈ G'.neighborFinset x} :=
        { toFun := fun y => ⟨y.1, (G'.mem_neighborFinset x y.1).mpr y.2⟩
          invFun := fun y => ⟨y.1, (G'.mem_neighborFinset x y.1).mp y.2⟩
          left_inv := by
            intro y
            rfl
          right_inv := by
            intro y
            rfl }
      calc
        Nat.card {y : FinalVertex // G'.Adj x y}
            = Nat.card {y : FinalVertex // y ∈ G'.neighborFinset x} :=
              Nat.card_congr eNeighbor
        _ = Fintype.card {y : FinalVertex // y ∈ G'.neighborFinset x} :=
              Nat.card_eq_fintype_card
        _ = (G'.neighborFinset x).card := Fintype.card_coe (G'.neighborFinset x)
        _ = G'.degree x := SimpleGraph.card_neighborFinset_eq_degree G' x
    have hBaseNeighborSplitCount :
        ∀ b : BaseOwner,
          Nat.card {y : FinalVertex // G'.Adj (Sum.inl b) y} =
            Nat.card {c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} +
              Nat.card {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)} := by
      intro b
      let e :
          {y : FinalVertex // G'.Adj (Sum.inl b) y} ≃
            ({c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} ⊕
              {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)}) :=
        { toFun := fun y => by
            rcases y with ⟨y, hy⟩
            cases y with
            | inl c => exact Sum.inl ⟨c, hy⟩
            | inr z => exact Sum.inr ⟨z, hy⟩
          invFun := fun y => by
            cases y with
            | inl c => exact ⟨Sum.inl c.1, c.2⟩
            | inr z => exact ⟨Sum.inr z.1, z.2⟩
          left_inv := by
            rintro ⟨(_ | _), hy⟩ <;> rfl
          right_inv := by
            rintro (⟨c, hc⟩ | ⟨z, hz⟩) <;> rfl }
      calc
        Nat.card {y : FinalVertex // G'.Adj (Sum.inl b) y}
            =
              Nat.card
                ({c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} ⊕
                  {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)}) :=
              Nat.card_congr e
        _ =
              Fintype.card
                ({c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} ⊕
                  {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)}) :=
              Nat.card_eq_fintype_card
        _ =
              Fintype.card {c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} +
                Fintype.card {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)} :=
              Fintype.card_sum
        _ =
              Nat.card {c : BaseOwner // G'.Adj (Sum.inl b) (Sum.inl c)} +
                Nat.card {z : BlockVertex // G'.Adj (Sum.inl b) (Sum.inr z)} := by
              rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hParityBaseBaseNeighborCount :
        ∀ p : BaseOwner, parityBase = some p →
          Nat.card {b : BaseOwner // G'.Adj (Sum.inl p) (Sum.inl b)} = 0 := by
      intro p hp
      let e : {b : BaseOwner // G'.Adj (Sum.inl p) (Sum.inl b)} ≃ Empty :=
        { toFun := fun b => False.elim (hParityBaseNoBaseAdj p hp b.1 b.2)
          invFun := fun e => Empty.elim e
          left_inv := by
            intro b
            exact False.elim (hParityBaseNoBaseAdj p hp b.1 b.2)
          right_inv := by
            intro e
            cases e }
      calc
        Nat.card {b : BaseOwner // G'.Adj (Sum.inl p) (Sum.inl b)}
            = Nat.card Empty := Nat.card_congr e
        _ = 0 := by simp
    have hBaseVertexDegree :
        ∀ b : BaseOwner, G'.degree (Sum.inl b) = Delta := by
      intro b
      rw [← hNeighborSubtypeDegree (Sum.inl b), hBaseNeighborSplitCount b]
      rcases hBaseOwnerExhaustive b with ⟨v, hb⟩ | hp
      · subst b
        rw [hOldBaseBaseNeighborCount, hOldBaseBlockNeighborCount]
        rw [Nat.add_comm, Nat.sub_add_cancel (hmax v)]
      · rw [hParityBaseBaseNeighborCount b hp, hParityBaseBlockNeighborCount b hp]
        exact Nat.zero_add Delta
    have hFinZeroNeOne : (0 : Fin (Delta + 1)) ≠ 1 := by
      intro h01
      have hv := congrArg (fun t : Fin (Delta + 1) => (t : ℕ)) h01
      norm_num at hv
      omega
    have hFinTwoDeletedCount :
        Nat.card {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} =
          Delta - 1 := by
      rw [Nat.card_eq_fintype_card]
      have hcompl :
          Fintype.card {j : Fin (Delta + 1) // ¬ (j = 0 ∨ j = 1)} =
            Fintype.card (Fin (Delta + 1)) -
              Fintype.card {j : Fin (Delta + 1) // j = 0 ∨ j = 1} := by
        simpa using
          Fintype.card_subtype_compl
            (fun j : Fin (Delta + 1) => j = 0 ∨ j = 1)
      have htwo :
          Fintype.card {j : Fin (Delta + 1) // j = 0 ∨ j = 1} = 2 :=
        Fintype.card_subtype_eq_or_eq_of_ne hFinZeroNeOne
      have hcongr :
          Fintype.card {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} =
            Fintype.card {j : Fin (Delta + 1) // ¬ (j = 0 ∨ j = 1)} := by
        apply Fintype.card_congr
        exact
          { toFun := fun j => ⟨j.1, by
              intro hbad
              rcases hbad with hbad | hbad
              · exact j.2.1 hbad
              · exact j.2.2 hbad⟩
            invFun := fun j => ⟨j.1, by
              constructor
              · intro h0
                exact j.2 (Or.inl h0)
              · intro h1
                exact j.2 (Or.inr h1)⟩
            left_inv := by
              intro j
              rfl
            right_inv := by
              intro j
              rfl }
      rw [hcongr, hcompl, htwo]
      simp
    have hFinOneDeletedCount :
        ∀ i : Fin (Delta + 1),
          Nat.card {j : Fin (Delta + 1) // j ≠ i} = Delta := by
      intro i
      let e : Fin Delta ≃ {j : Fin (Delta + 1) // j ≠ i} :=
        { toFun := fun k => ⟨i.succAbove k, Fin.succAbove_ne i k⟩
          invFun := fun j => Classical.choose (Fin.exists_succAbove_eq j.2)
          left_inv := by
            intro k
            apply Fin.succAbove_right_injective
            exact Classical.choose_spec (Fin.exists_succAbove_eq (Fin.succAbove_ne i k))
          right_inv := by
            intro j
            apply Subtype.ext
            exact Classical.choose_spec (Fin.exists_succAbove_eq j.2) }
      calc
        Nat.card {j : Fin (Delta + 1) // j ≠ i} = Nat.card (Fin Delta) :=
          Nat.card_congr e.symm
        _ = Delta := by simp
    have hBlockNeighborSplitCount :
        ∀ z : BlockVertex,
          Nat.card {y : FinalVertex // G'.Adj (Sum.inr z) y} =
            Nat.card {b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} +
              Nat.card {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)} := by
      intro z
      let e :
          {y : FinalVertex // G'.Adj (Sum.inr z) y} ≃
            ({b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} ⊕
              {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)}) :=
        { toFun := fun y => by
            rcases y with ⟨y, hy⟩
            cases y with
            | inl b => exact Sum.inl ⟨b, hy⟩
            | inr w => exact Sum.inr ⟨w, hy⟩
          invFun := fun y => by
            cases y with
            | inl b => exact ⟨Sum.inl b.1, b.2⟩
            | inr w => exact ⟨Sum.inr w.1, w.2⟩
          left_inv := by
            rintro ⟨(_ | _), hy⟩ <;> rfl
          right_inv := by
            rintro (⟨b, hb⟩ | ⟨w, hw⟩) <;> rfl }
      calc
        Nat.card {y : FinalVertex // G'.Adj (Sum.inr z) y}
            =
              Nat.card
                ({b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} ⊕
                  {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)}) :=
              Nat.card_congr e
        _ =
              Fintype.card
                ({b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} ⊕
                  {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)}) :=
              Nat.card_eq_fintype_card
        _ =
              Fintype.card {b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} +
                Fintype.card {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)} :=
              Fintype.card_sum
        _ =
              Nat.card {b : BaseOwner // G'.Adj (Sum.inr z) (Sum.inl b)} +
                Nat.card {w : BlockVertex // G'.Adj (Sum.inr z) (Sum.inr w)} := by
              rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hBlockBaseNeighborCountZero :
        ∀ p : P,
          Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, (0 : Fin (Delta + 1)))) (Sum.inl b)} =
            1 := by
      intro p
      let e :
          {b : BaseOwner // G'.Adj (Sum.inr (p, (0 : Fin (Delta + 1)))) (Sum.inl b)} ≃
            {b : BaseOwner // b = stubOwner (pair p 0)} :=
        { toFun := fun b => by
            have h := (hBlockBaseAdj p 0 b.1).mp b.2
            refine ⟨b.1, ?_⟩
            rcases h with ⟨_hi, hb⟩ | ⟨hi, _hb⟩
            · exact hb
            · exact False.elim (hFinZeroNeOne hi)
          invFun := fun b =>
            ⟨b.1, (hBlockBaseAdj p 0 b.1).mpr (Or.inl ⟨rfl, b.2⟩)⟩
          left_inv := by
            intro b
            rfl
          right_inv := by
            intro b
            rfl }
      calc
        Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, (0 : Fin (Delta + 1)))) (Sum.inl b)}
            = Nat.card {b : BaseOwner // b = stubOwner (pair p 0)} := Nat.card_congr e
        _ = 1 := by
          rw [Nat.card_eq_fintype_card]
          simpa using Fintype.card_subtype_eq (stubOwner (pair p 0))
    have hBlockBaseNeighborCountOne :
        ∀ p : P,
          Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, (1 : Fin (Delta + 1)))) (Sum.inl b)} =
            1 := by
      intro p
      let e :
          {b : BaseOwner // G'.Adj (Sum.inr (p, (1 : Fin (Delta + 1)))) (Sum.inl b)} ≃
            {b : BaseOwner // b = stubOwner (pair p 1)} :=
        { toFun := fun b => by
            have h := (hBlockBaseAdj p 1 b.1).mp b.2
            refine ⟨b.1, ?_⟩
            rcases h with ⟨hi, _hb⟩ | ⟨_hi, hb⟩
            · exact False.elim (hFinZeroNeOne hi.symm)
            · exact hb
          invFun := fun b =>
            ⟨b.1, (hBlockBaseAdj p 1 b.1).mpr (Or.inr ⟨rfl, b.2⟩)⟩
          left_inv := by
            intro b
            rfl
          right_inv := by
            intro b
            rfl }
      calc
        Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, (1 : Fin (Delta + 1)))) (Sum.inl b)}
            = Nat.card {b : BaseOwner // b = stubOwner (pair p 1)} := Nat.card_congr e
        _ = 1 := by
          rw [Nat.card_eq_fintype_card]
          simpa using Fintype.card_subtype_eq (stubOwner (pair p 1))
    have hBlockBaseNeighborCountOther :
        ∀ (p : P) (i : Fin (Delta + 1)), i ≠ 0 → i ≠ 1 →
          Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, i)) (Sum.inl b)} = 0 := by
      intro p i hi0 hi1
      let e : {b : BaseOwner // G'.Adj (Sum.inr (p, i)) (Sum.inl b)} ≃ Empty :=
        { toFun := fun b => False.elim (by
            have h := (hBlockBaseAdj p i b.1).mp b.2
            rcases h with ⟨hizero, _hb⟩ | ⟨hione, _hb⟩
            · exact hi0 hizero
            · exact hi1 hione)
          invFun := fun e => Empty.elim e
          left_inv := by
            intro b
            have h := (hBlockBaseAdj p i b.1).mp b.2
            rcases h with ⟨hizero, _hb⟩ | ⟨hione, _hb⟩
            · exact False.elim (hi0 hizero)
            · exact False.elim (hi1 hione)
          right_inv := by
            intro e
            cases e }
      calc
        Nat.card {b : BaseOwner // G'.Adj (Sum.inr (p, i)) (Sum.inl b)}
            = Nat.card Empty := Nat.card_congr e
        _ = 0 := by simp
    have hBlockBlockNeighborCountAsSlots :
        ∀ (p : P) (i : Fin (Delta + 1)),
          Nat.card {w : BlockVertex // G'.Adj (Sum.inr (p, i)) (Sum.inr w)} =
            Nat.card {j : Fin (Delta + 1) //
              i ≠ j ∧ ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))} := by
      intro p i
      let e :
          {w : BlockVertex // G'.Adj (Sum.inr (p, i)) (Sum.inr w)} ≃
            {j : Fin (Delta + 1) //
              i ≠ j ∧ ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))} :=
        { toFun := fun w => by
            rcases w with ⟨⟨q, j⟩, hw⟩
            have h := (hBlockBlockAdj p q i j).mp hw
            exact ⟨j, h.2⟩
          invFun := fun j =>
            ⟨(p, j.1), (hBlockBlockAdj p p i j.1).mpr ⟨rfl, j.2⟩⟩
          left_inv := by
            rintro ⟨⟨q, j⟩, hw⟩
            apply Subtype.ext
            have h := (hBlockBlockAdj p q i j).mp hw
            exact Prod.ext h.1 rfl
          right_inv := by
            intro j
            rfl }
      exact Nat.card_congr e
    have hBlockBlockNeighborCountZero :
        ∀ p : P,
          Nat.card {w : BlockVertex // G'.Adj (Sum.inr (p, (0 : Fin (Delta + 1)))) (Sum.inr w)} =
            Delta - 1 := by
      intro p
      rw [hBlockBlockNeighborCountAsSlots]
      let e :
          {j : Fin (Delta + 1) //
            (0 : Fin (Delta + 1)) ≠ j ∧
              ¬ (((0 : Fin (Delta + 1)) = 0 ∧ j = 1) ∨
                ((0 : Fin (Delta + 1)) = 1 ∧ j = 0))} ≃
            {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} :=
        { toFun := fun j => ⟨j.1, by
            constructor
            · exact j.2.1.symm
            · intro hj1
              exact j.2.2 (Or.inl ⟨rfl, hj1⟩)⟩
          invFun := fun j => ⟨j.1, by
            constructor
            · exact j.2.1.symm
            · intro hdel
              rcases hdel with ⟨_h0, hj1⟩ | ⟨h01, _hj0⟩
              · exact j.2.2 hj1
              · exact hFinZeroNeOne h01⟩
          left_inv := by
            intro j
            rfl
          right_inv := by
            intro j
            rfl }
      calc
        Nat.card {j : Fin (Delta + 1) //
            (0 : Fin (Delta + 1)) ≠ j ∧
              ¬ (((0 : Fin (Delta + 1)) = 0 ∧ j = 1) ∨
                ((0 : Fin (Delta + 1)) = 1 ∧ j = 0))}
            = Nat.card {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} :=
          Nat.card_congr e
        _ = Delta - 1 := hFinTwoDeletedCount
    have hBlockBlockNeighborCountOne :
        ∀ p : P,
          Nat.card {w : BlockVertex // G'.Adj (Sum.inr (p, (1 : Fin (Delta + 1)))) (Sum.inr w)} =
            Delta - 1 := by
      intro p
      rw [hBlockBlockNeighborCountAsSlots]
      let e :
          {j : Fin (Delta + 1) //
            (1 : Fin (Delta + 1)) ≠ j ∧
              ¬ (((1 : Fin (Delta + 1)) = 0 ∧ j = 1) ∨
                ((1 : Fin (Delta + 1)) = 1 ∧ j = 0))} ≃
            {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} :=
        { toFun := fun j => ⟨j.1, by
            constructor
            · intro hj0
              exact j.2.2 (Or.inr ⟨rfl, hj0⟩)
            · exact j.2.1.symm⟩
          invFun := fun j => ⟨j.1, by
            constructor
            · exact j.2.2.symm
            · intro hdel
              rcases hdel with ⟨h10, _hj1⟩ | ⟨_h1, hj0⟩
              · exact hFinZeroNeOne h10.symm
              · exact j.2.1 hj0⟩
          left_inv := by
            intro j
            rfl
          right_inv := by
            intro j
            rfl }
      calc
        Nat.card {j : Fin (Delta + 1) //
            (1 : Fin (Delta + 1)) ≠ j ∧
              ¬ (((1 : Fin (Delta + 1)) = 0 ∧ j = 1) ∨
                ((1 : Fin (Delta + 1)) = 1 ∧ j = 0))}
            = Nat.card {j : Fin (Delta + 1) // j ≠ (0 : Fin (Delta + 1)) ∧ j ≠ 1} :=
          Nat.card_congr e
        _ = Delta - 1 := hFinTwoDeletedCount
    have hBlockBlockNeighborCountOther :
        ∀ (p : P) (i : Fin (Delta + 1)), i ≠ 0 → i ≠ 1 →
          Nat.card {w : BlockVertex // G'.Adj (Sum.inr (p, i)) (Sum.inr w)} =
            Delta := by
      intro p i hi0 hi1
      rw [hBlockBlockNeighborCountAsSlots]
      let e :
          {j : Fin (Delta + 1) //
            i ≠ j ∧ ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))} ≃
            {j : Fin (Delta + 1) // j ≠ i} :=
        { toFun := fun j => ⟨j.1, j.2.1.symm⟩
          invFun := fun j => ⟨j.1, by
            constructor
            · exact j.2.symm
            · intro hdel
              rcases hdel with ⟨hizero, _hj1⟩ | ⟨hione, _hj0⟩
              · exact hi0 hizero
              · exact hi1 hione⟩
          left_inv := by
            intro j
            rfl
          right_inv := by
            intro j
            rfl }
      calc
        Nat.card {j : Fin (Delta + 1) //
            i ≠ j ∧ ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))}
            = Nat.card {j : Fin (Delta + 1) // j ≠ i} := Nat.card_congr e
        _ = Delta := hFinOneDeletedCount i
    have hBlockVertexDegree :
        ∀ z : BlockVertex, G'.degree (Sum.inr z) = Delta := by
      intro z
      rcases z with ⟨p, i⟩
      rw [← hNeighborSubtypeDegree (Sum.inr (p, i)), hBlockNeighborSplitCount (p, i)]
      by_cases hi0 : i = 0
      · subst i
        rw [hBlockBaseNeighborCountZero, hBlockBlockNeighborCountZero]
        omega
      · by_cases hi1 : i = 1
        · subst i
          rw [hBlockBaseNeighborCountOne, hBlockBlockNeighborCountOne]
          omega
        · rw [hBlockBaseNeighborCountOther p i hi0 hi1,
            hBlockBlockNeighborCountOther p i hi0 hi1]
          exact Nat.zero_add Delta
    refine ⟨FinalVertex, instFinalVertex, instFinalDecEq, G', instFinalAdj, ?_⟩
    refine ⟨oldEmbedding, hOldEmbeddingInjective, hOldOldAdj, ?_⟩
    intro v'
    cases v' with
    | inl b =>
        exact hBaseVertexDegree b
    | inr z =>
        exact hBlockVertexDegree z
