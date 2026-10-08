import Tablet.OneNibblePartialColoring
import Tablet.CanonicalResidualEmbedding
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport

-- [TABLET NODE: GeneralColoringScheduledNibbleIteration]
theorem GeneralColoringScheduledNibbleIteration (eps : ℝ) (A k : ℕ)
    (heps : 0 < eps) :
    ∃ gamma0 : ℕ, ∀ gamma : ℕ, gamma0 ≤ gamma → 0 < gamma →
      ∃ Dn : ℕ, ∀ (D theta : ℝ) (s : ℕ) (N K : ℕ → ℕ),
        Nat.ceil ((k : ℝ) * N 0 / gamma) ≤ K 0 →
        (∀ i, i < s →
          Dn ≤ N i ∧ eps * D / 3 ≤ (N i : ℝ) ∧
          K i ≤ A * N i ∧ K i ≤ K (i + 1) ∧
          (1 - (1 - eps / 6) / gamma) * N i ≤ (N (i + 1) : ℝ) ∧
          (1 - theta - eps / 6) * (Nat.ceil ((k : ℝ) * N i / gamma) : ℝ) +
            ((K (i + 1) : ℝ) - K i) ≥
              (Nat.ceil ((k : ℝ) * N (i + 1) / gamma) : ℝ)) →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            UniformHypergraph H k → MaxDegreeAtMost H (N 0) →
            (∀ {F : Type*} [Fintype F] [DecidableEq F], ∀ n : ℕ,
              eps * D / 3 ≤ (n : ℝ) → ∀ H' : MultiHypergraph V F,
                SubhypergraphOf H' H → MaxDegreeAtMost H' n → ∀ e : F,
                  @LocalBParameter F _ _ (LineGraphOfHypergraph H')
                    (Classical.decRel (LineGraphOfHypergraph H').Adj) (k * n) e ≤ theta) →
            ∃ (C : Finset E) (c : {e : E // e ∈ C} → Fin (K s)),
              (∀ e f, e ≠ f → (H.edge e.val ∩ H.edge f.val).Nonempty → c e ≠ c f) ∧
              MaxDegreeAtMost
                (⟨fun e : {e : E // e ∉ C} => H.edge e.val⟩ :
                  MultiHypergraph V {e : E // e ∉ C}) (N s) := by
-- BODY
  classical
  obtain ⟨gamma0, hg0⟩ := OneNibblePartialColoring.{_, _, 0} A k (eps / 6) (by positivity)
  refine ⟨gamma0, ?_⟩
  intro gamma hg hgamma
  obtain ⟨Dn, hn⟩ := hg0 gamma hg
  refine ⟨Dn, ?_⟩
  intro D theta s N K hstart hstep V E _ _ _ H hu hd hb
  let available := fun (m : ℕ) (C : Finset E) (c : {e // e ∈ C} → Fin m) (e : E) =>
    Finset.univ.filter fun a => ∀ f, c f = a → ¬ (H.edge f.val ∩ H.edge e).Nonempty
  have hav (m : ℕ) (C : Finset E) (c : {e // e ∈ C} → Fin m) (e : E) (a : Fin m) :
      a ∈ available m C c e ↔
        ∀ f, c f = a → ¬ (H.edge f.val ∩ H.edge e).Nonempty := by
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and]
  have hind : ∀ i, i ≤ s → ∃ (C : Finset E) (c : {e // e ∈ C} → Fin (K i)),
      (∀ e f, e ≠ f → (H.edge e.val ∩ H.edge f.val).Nonempty → c e ≠ c f) ∧
      MaxDegreeAtMost (⟨fun e : {e : E // e ∉ C} => H.edge e.val⟩ :
        MultiHypergraph V {e : E // e ∉ C}) (N i) ∧
      (∀ e, e ∉ C → Nat.ceil ((k : ℝ) * N i / gamma) ≤
        (available (K i) C c e).card) := by
    intro i
    induction i with
    | zero =>
        intro _
        let c : {e : E // e ∈ (∅ : Finset E)} → Fin (K 0) := fun e =>
          False.elim (Finset.notMem_empty e.val e.property)
        refine ⟨∅, c, ?_, ?_, ?_⟩
        · intro e
          exact False.elim (Finset.notMem_empty e.val e.property)
        · have hs : SubhypergraphOf
              (⟨fun e : {e : E // e ∉ (∅ : Finset E)} => H.edge e.val⟩) H :=
            ⟨Subtype.val, Subtype.val_injective, fun _ => rfl⟩
          exact fun v => ((SubhypergraphInheritance _ H hs).2.2 v).trans (hd v)
        · intro e _
          simpa [available] using hstart
    | succ i ih =>
        intro his
        obtain ⟨C, c, hc, hdC, hlist⟩ := ih (by omega)
        obtain ⟨hDn, hscale, hpalette, hKK, hNN, hLL⟩ := hstep i (by omega)
        let R := {e : E // e ∉ C}
        let Hr : MultiHypergraph V R := ⟨fun e => H.edge e.val⟩
        have hsub : SubhypergraphOf Hr H := ⟨Subtype.val, Subtype.val_injective, fun _ => rfl⟩
        let inc : Fin (K i) ↪ Fin (A * N i) :=
          ⟨Fin.castLE hpalette, Fin.castLE_injective hpalette⟩
        let L : R → Finset (Fin (A * N i)) := fun e =>
          (available (K i) C c e.val).map inc
        have hceil : (Nat.ceil ((k : ℝ) * N i / gamma) : ℤ) =
            Int.ceil ((k : ℝ) * N i / gamma) :=
          Int.natCast_ceil_eq_ceil (by positivity)
        have hinput (e : R) : Int.ceil ((k : ℝ) * N i / gamma) ≤ ((L e).card : ℤ) := by
          rw [← hceil]
          dsimp only [L]
          rw [Finset.card_map]
          exact_mod_cast hlist e.val e.property
        have hbound : ∀ e : R, @LocalBParameter R _ _ (LineGraphOfHypergraph Hr)
            (Classical.decRel (LineGraphOfHypergraph Hr).Adj) (k * N i) e ≤ theta := by
          let eqv := (Fintype.equivFin R).trans Equiv.ulift.symm
          let H' : MultiHypergraph V (ULift (Fin (Fintype.card R))) :=
            ⟨fun e => Hr.edge (eqv.symm e)⟩
          have hs' : SubhypergraphOf H' Hr := ⟨eqv.symm, eqv.symm.injective, fun _ => rfl⟩
          have hsH : SubhypergraphOf H' H :=
            ⟨fun e => (eqv.symm e).val, Subtype.val_injective.comp eqv.symm.injective,
              fun _ => rfl⟩
          have hd' : MaxDegreeAtMost H' (N i) := fun v =>
            ((SubhypergraphInheritance H' Hr hs').2.2 v).trans (hdC v)
          have hb' := hb (N i) hscale H' hsH hd'
          have hadj (e f : R) : (LineGraphOfHypergraph Hr).Adj e f ↔
              (LineGraphOfHypergraph H').Adj (eqv e) (eqv f) := by
            change (e ≠ f ∧ _) ↔ (eqv e ≠ eqv f ∧ _)
            simp only [H', eqv.symm_apply_apply, ne_eq, eqv.injective.eq_iff]
          intro e
          have heq : @LocalBParameter R _ _ (LineGraphOfHypergraph Hr)
              (Classical.decRel _) (k * N i) e =
              @LocalBParameter _ _ _ (LineGraphOfHypergraph H')
                (Classical.decRel _) (k * N i) (eqv e) := by
            apply LocalBParameterNeighborhoodEmbeddingTransport _ _ _ _ _ eqv.toEmbedding
            · intro f hf
              rw [SimpleGraph.mem_neighborFinset] at hf ⊢
              exact (hadj e f).mp hf
            · intro f hf
              refine ⟨eqv.symm f, ?_, eqv.apply_symm_apply f⟩
              rw [SimpleGraph.mem_neighborFinset] at hf ⊢
              apply (hadj e (eqv.symm f)).mpr
              simpa using hf
            · intro f _ g _
              exact hadj f g
          rw [heq]
          exact hb' (eqv e)
        obtain ⟨B, b, hbL, hbproper, F, instF, instDF, embed, Hc, Lc,
            hedge, hcover, hLc, hdegree, hsize⟩ :=
          hn (N i) hDn Hr ((SubhypergraphInheritance Hr H hsub).1 k hu) hdC L
            hinput theta hbound
        letI := instF
        letI := instDF
        have hdecode (e : {e : R // e ∈ B}) :
            ∃ a ∈ available (K i) C c e.val.val, inc a = b e := by
          exact Finset.mem_map.mp (hbL e)
        choose bOld hbOldList hbOld using hdecode
        have hbOldProper (e f : {e : R // e ∈ B}) (hef : e ≠ f)
            (hadj : (H.edge e.val.val ∩ H.edge f.val.val).Nonempty) : bOld e ≠ bOld f := by
          intro heq
          apply hbproper e f hef hadj
          rw [← hbOld e, ← hbOld f, heq]
        obtain ⟨⟨j, hjinj, hj⟩, _, _, hjdegree⟩ :=
          CanonicalResidualEmbedding Hr B embed Hc hedge hcover
        have hresdegree (v : V) :
            HypergraphDegree (⟨fun e : {e : R // e ∉ B} => Hr.edge e.val⟩ :
              MultiHypergraph V {e : R // e ∉ B}) v ≤ N (i + 1) := by
          have hh := (Nat.cast_le (α := ℝ)).mpr (hjdegree v)
          exact_mod_cast hh.trans ((hdegree v).trans hNN)
        let oldList : {e : R // e ∉ B} → Finset (Fin (K i)) := fun e =>
          Finset.univ.filter fun a => inc a ∈ Lc (j e)
        have holdMap (e : {e : R // e ∉ B}) : (oldList e).map inc = Lc (j e) := by
          ext a
          constructor
          · rintro ha
            obtain ⟨a', ha', heq⟩ := Finset.mem_map.mp ha
            rw [← heq]
            exact (Finset.mem_filter.mp ha').2
          · intro ha
            have hmem := ((hLc (j e) a).mp ha).1
            obtain ⟨a', _, heq⟩ := Finset.mem_map.mp hmem
            refine Finset.mem_map.mpr ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
            rwa [heq]
        have holdSize (e : {e : R // e ∉ B}) :
            (1 - theta - eps / 6) * (Nat.ceil ((k : ℝ) * N i / gamma) : ℝ) ≤
              ((oldList e).card : ℝ) := by
          have hh := hsize (j e)
          rw [← holdMap e, Finset.card_map, ← hceil] at hh
          exact_mod_cast hh
        have holdMem (e : {e : R // e ∉ B}) (a : Fin (K i)) :
            a ∈ oldList e ↔ a ∈ available (K i) C c e.val.val ∧
              ∀ f : {f : R // f ∈ B}, bOld f = a →
                ¬ (H.edge f.val.val ∩ H.edge e.val.val).Nonempty := by
          simp only [oldList, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hLc, hj]
          have hmem : inc a ∈ L e.val ↔ a ∈ available (K i) C c e.val.val := by
            exact Finset.mem_map' inc
          rw [hmem]
          constructor
          · rintro ⟨ha, hh⟩
            refine ⟨ha, fun f hf => hh f ?_⟩
            rw [← hbOld f, hf]
          · rintro ⟨ha, hh⟩
            refine ⟨ha, fun f hf => hh f ?_⟩
            apply inc.injective
            rw [hbOld f, hf]
        let Cnext := C ∪ B.image Subtype.val
        have hnew (e : E) (he : e ∈ Cnext) (heC : e ∉ C) : (⟨e, heC⟩ : R) ∈ B := by
          obtain h | h := Finset.mem_union.mp he
          · exact False.elim (heC h)
          · obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
            have heq : f = (⟨e, heC⟩ : R) := Subtype.ext hfe
            rwa [← heq]
        let combined : {e : E // e ∈ Cnext} → Fin (K i) := fun e =>
          if he : e.val ∈ C then c ⟨e.val, he⟩
          else bOld ⟨⟨e.val, he⟩, hnew e.val e.property he⟩
        have hcombined : ∀ e f, e ≠ f → (H.edge e.val ∩ H.edge f.val).Nonempty →
            combined e ≠ combined f := by
          intro e f hef hadj
          dsimp only [combined]
          split_ifs with he hf hf
          · exact hc _ _ (fun h => hef (Subtype.ext
              (congrArg (fun a : {e : E // e ∈ C} => a.val) h))) hadj
          · intro heq
            exact (hav _ _ _ _ _).mp (hbOldList ⟨⟨f.val, hf⟩, hnew _ f.property hf⟩)
              ⟨e.val, he⟩ heq hadj
          · intro heq
            exact (hav _ _ _ _ _).mp (hbOldList ⟨⟨e.val, he⟩, hnew _ e.property he⟩)
              ⟨f.val, hf⟩ heq.symm (by simpa [Finset.inter_comm] using hadj)
          · exact hbOldProper _ _
              (fun h => hef (Subtype.ext (congrArg (fun a => a.val.val) h))) hadj
        let up : Fin (K i) ↪ Fin (K (i + 1)) :=
          ⟨Fin.castLE hKK, Fin.castLE_injective hKK⟩
        let cnext : {e : E // e ∈ Cnext} → Fin (K (i + 1)) := fun e => up (combined e)
        have hremaining (e : {e : E // e ∉ Cnext}) : e.val ∉ C ∧
            ∀ he : e.val ∉ C, (⟨e.val, he⟩ : R) ∉ B := by
          constructor
          · exact fun h => e.property (Finset.mem_union_left _ h)
          · intro he hB
            exact e.property (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨e.val, he⟩, hB, rfl⟩))
        let rem : {e : E // e ∉ Cnext} → {e : R // e ∉ B} := fun e =>
          ⟨⟨e.val, (hremaining e).1⟩, (hremaining e).2 _⟩
        have hremInj : Function.Injective rem := by
          intro e f h
          exact Subtype.ext (congrArg (fun a => a.val.val) h)
        refine ⟨Cnext, cnext, ?_, ?_, ?_⟩
        · intro e f hef hadj heq
          exact hcombined e f hef hadj (up.injective heq)
        · have hs : SubhypergraphOf
              (⟨fun e : {e : E // e ∉ Cnext} => H.edge e.val⟩ :
                MultiHypergraph V {e : E // e ∉ Cnext})
              (⟨fun e : {e : R // e ∉ B} => Hr.edge e.val⟩ :
                MultiHypergraph V {e : R // e ∉ B}) := ⟨rem, hremInj, fun _ => rfl⟩
          exact fun v => ((SubhypergraphInheritance _ _ hs).2.2 v).trans (hresdegree v)
        · intro e he
          let r := rem ⟨e, he⟩
          let fresh : Finset (Fin (K (i + 1))) := Finset.univ.filter fun a => K i ≤ a.val
          have hdisjoint : Disjoint ((oldList r).map up) fresh := by
            apply Finset.disjoint_left.mpr
            intro a ha hf
            obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
            have hh := (Finset.mem_filter.mp hf).2
            exact (Nat.not_le_of_lt a'.isLt) hh
          have hsubset : (oldList r).map up ∪ fresh ⊆ available (K (i + 1)) Cnext cnext e := by
            intro a ha
            apply (hav _ _ _ _ _).mpr
            intro f hf
            obtain ha | ha := Finset.mem_union.mp ha
            · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
              have hf' : combined f = a' := up.injective hf
              obtain ⟨hold, hnewavoid⟩ := (holdMem r a').mp ha'
              dsimp only [combined] at hf'
              split_ifs at hf' with hfC
              · exact (hav _ _ _ _ _).mp hold ⟨f.val, hfC⟩ hf'
              · exact hnewavoid ⟨⟨f.val, hfC⟩, hnew _ f.property hfC⟩ hf'
            · have hlarge := (Finset.mem_filter.mp ha).2
              have hsmall : (cnext f).val < K i := (combined f).isLt
              rw [hf] at hsmall
              exact False.elim ((Nat.not_le_of_lt hsmall) hlarge)
          have hfresh : fresh.card = K (i + 1) - K i := by
            have hpartition : (Finset.univ.map up) ∪ fresh = Finset.univ := by
              ext a
              simp only [Finset.mem_univ, iff_true]
              by_cases ha : a.val < K i
              · exact Finset.mem_union_left _ (Finset.mem_map.mpr
                  ⟨⟨a.val, ha⟩, Finset.mem_univ _, Fin.ext rfl⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, Nat.le_of_not_gt ha⟩)
            have hdj : Disjoint (Finset.univ.map up) fresh := by
              apply Finset.disjoint_left.mpr
              intro a ha hf
              obtain ⟨a', _, rfl⟩ := Finset.mem_map.mp ha
              exact (Nat.not_le_of_lt a'.isLt) (Finset.mem_filter.mp hf).2
            have hh := congrArg Finset.card hpartition
            rw [Finset.card_union_of_disjoint hdj, Finset.card_map] at hh
            simp only [Finset.card_univ, Fintype.card_fin] at hh
            omega
          have hcard := Finset.card_le_card hsubset
          rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map, hfresh] at hcard
          have hcardR := (Nat.cast_le (α := ℝ)).mpr hcard
          rw [Nat.cast_add, Nat.cast_sub hKK] at hcardR
          have hsizeR := holdSize r
          have hfinal : (Nat.ceil ((k : ℝ) * N (i + 1) / gamma) : ℝ) ≤
              ((available (K (i + 1)) Cnext cnext e).card : ℝ) := by linarith
          exact_mod_cast hfinal
  obtain ⟨C, c, hc, hdC, _⟩ := hind s le_rfl
  exact ⟨C, c, hc, hdC⟩
