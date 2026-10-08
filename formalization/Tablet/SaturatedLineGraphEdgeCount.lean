import Tablet.LineGraphOfHypergraph
import Tablet.MaxDegreeAtMost
import Tablet.UniformHypergraph
import Tablet.SaturatedNeighborClassPartition
import Tablet.FiniteUnorderedPairProductSum
import Tablet.FiniteBipartiteIntersectionEdgeCount

open scoped BigOperators

-- [TABLET NODE: SaturatedLineGraphEdgeCount]
theorem SaturatedLineGraphEdgeCount :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]
      [LinearOrder V] [LinearOrder E],
      ∀ H : MultiHypergraph V E, ∀ e : E,
        UniformHypergraph H 3 →
        MaxDegreeAtMost H D →
        ((Finset.univ : Finset E).filter
          (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)).card = 3 * (D - 1) →
        let N := (Finset.univ : Finset E).filter
          (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)
        let edgeCount : ℤ :=
          (((Finset.univ : Finset (Finset E)).filter
            (fun s => s.card = 2 ∧ s ⊆ N ∧
              ∀ a, a ∈ s → ∀ b, b ∈ s → a ≠ b →
                (H.edge a ∩ H.edge b).Nonempty)).card : ℤ)
        let W : ℤ :=
          ((∑ x ∈ ((Finset.univ : Finset V).filter
            (fun x => x ∉ H.edge e ∧
              ((Finset.univ : Finset E).filter
                (fun h => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)),
            ∑ p ∈ ((Finset.univ : Finset (Finset V)).filter
              (fun p => p.card = 2 ∧ p ⊆ H.edge e)),
              ∏ v ∈ p,
                ((Finset.univ : Finset E).filter
                  (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)).card) : ℤ)
        let Y : ℤ :=
          ∑ v ∈ H.edge e,
            ∑ v' ∈ (H.edge e).filter (fun u => v < u),
              ∑ e1 ∈ ((Finset.univ : Finset E).filter
                (fun g => g ≠ e ∧ v ∈ H.edge g)),
                ∑ e2 ∈ ((Finset.univ : Finset E).filter
                  (fun g => g ≠ e ∧ v' ∈ H.edge g)),
                  max (0 : ℤ) (((H.edge e1 ∩ H.edge e2).card : ℤ) - 1)
        0 ≤ Y ∧ edgeCount = (3 * (Nat.choose (D - 1) 2) : ℤ) + W - Y := by
-- BODY
  classical
  intro D V E _ _ _ _ _ _ H e hu hd hN
  have hclasses := SaturatedNeighborClassPartition H e 3 D hu hd hN
  have hWpair (x : V) := FiniteUnorderedPairProductSum (H.edge e)
    (fun v => (((Finset.univ : Finset E).filter
      (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)).card : ℤ))
  let C := fun v : V => (Finset.univ : Finset E).filter
    (fun g => g ≠ e ∧ v ∈ H.edge g)
  let X := (Finset.univ : Finset V).filter (fun x => x ∉ H.edge e ∧
    ((Finset.univ : Finset E).filter
      (fun h => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)
  have hcrossX (v : V) (hv : v ∈ H.edge e) (w : V) (hw : w ∈ H.edge e)
      (hvw : v < w) (a : E) (ha : a ∈ C v) (b : E) (hb : b ∈ C w) :
      H.edge a ∩ H.edge b ⊆ X := by
    obtain ⟨hae, hva⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨hbe, hwb⟩ := (Finset.mem_filter.mp hb).2
    intro x hx
    obtain ⟨hxa, hxb⟩ := Finset.mem_inter.mp hx
    have hxe : x ∉ H.edge e := by
      intro hxe
      have hxv : x = v := Finset.card_le_one.mp (hclasses.2.2.2 a hae) x
        (Finset.mem_inter.mpr ⟨hxa, hxe⟩) v (Finset.mem_inter.mpr ⟨hva, hv⟩)
      have hxw : x = w := Finset.card_le_one.mp (hclasses.2.2.2 b hbe) x
        (Finset.mem_inter.mpr ⟨hxb, hxe⟩) w (Finset.mem_inter.mpr ⟨hwb, hw⟩)
      exact (ne_of_lt hvw) (hxv.symm.trans hxw)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hxe, a, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨v, Finset.mem_inter.mpr ⟨hva, hv⟩⟩, hxa⟩
  have hcross (v : V) (hv : v ∈ H.edge e) (w : V) (hw : w ∈ H.edge e)
      (hvw : v < w) :=
    FiniteBipartiteIntersectionEdgeCount H.edge (C v) (C w) X (hcrossX v hv w hw hvw)
  have hdegree (x : V) (hx : x ∈ X) (v : V) :
      ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)) =
      (C v).filter (fun g => x ∈ H.edge g) := by
    have hxe := (Finset.mem_filter.mp hx).2.1
    ext g
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨⟨fun he => hxe (he ▸ h.2), h.1⟩, h.2⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  have hW : ((∑ x ∈ X, ∑ v ∈ H.edge e,
      ∑ w ∈ (H.edge e).filter (fun u => v < u),
        ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)).card *
        ((Finset.univ : Finset E).filter (fun g => w ∈ H.edge g ∧ x ∈ H.edge g)).card) : ℤ) =
      ∑ v ∈ H.edge e, ∑ w ∈ (H.edge e).filter (fun u => v < u),
        ∑ x ∈ X, (((C v).filter (fun g => x ∈ H.edge g)).card : ℤ) *
          (((C w).filter (fun g => x ∈ H.edge g)).card : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro x hx
    rw [hdegree x hx v, hdegree x hx w]
  have hcross_sum : (∑ v ∈ H.edge e, ∑ w ∈ (H.edge e).filter (fun u => v < u),
      ((((C v) ×ˢ (C w)).filter (fun p => (H.edge p.1 ∩ H.edge p.2).Nonempty)).card : ℤ)) =
      (∑ v ∈ H.edge e, ∑ w ∈ (H.edge e).filter (fun u => v < u),
        ∑ x ∈ X, (((C v).filter (fun g => x ∈ H.edge g)).card : ℤ) *
          (((C w).filter (fun g => x ∈ H.edge g)).card : ℤ)) -
      ∑ v ∈ H.edge e, ∑ w ∈ (H.edge e).filter (fun u => v < u),
        ∑ a ∈ C v, ∑ b ∈ C w, max (0 : ℤ) (((H.edge a ∩ H.edge b).card : ℤ) - 1) := by
    simp only [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    exact hcross v hv w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  have hwithin (v : V) (hv : v ∈ H.edge e) :
      ((Finset.univ : Finset (Finset E)).filter (fun s => s.card = 2 ∧ s ⊆ C v ∧
        ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty)).card =
        Nat.choose (D - 1) 2 := by
    have heq : ((Finset.univ : Finset (Finset E)).filter (fun s => s.card = 2 ∧ s ⊆ C v ∧
        ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty)) =
        (C v).powersetCard 2 := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
      constructor
      · exact fun h => ⟨h.2.1, h.1⟩
      · rintro ⟨hs, hcard⟩
        refine ⟨hcard, hs, ?_⟩
        intro a ha b hb hab
        exact ⟨v, Finset.mem_inter.mpr
          ⟨(Finset.mem_filter.mp (hs ha)).2.2, (Finset.mem_filter.mp (hs hb)).2.2⟩⟩
    rw [heq, Finset.card_powersetCard, hclasses.1 v hv]
  dsimp only
  refine ⟨?_, ?_⟩
  · apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact le_max_left _ _
  · simp_rw [hWpair]
    rw [hW, add_sub_assoc, ← hcross_sum]
    let N := (Finset.univ : Finset E).filter
      (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)
    let A := fun v : V => (Finset.univ : Finset (Finset E)).filter
      (fun s => s.card = 2 ∧ s ⊆ C v ∧
        ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty)
    let B := fun v w : V => ((C v) ×ˢ (C w)).filter
      (fun p => (H.edge p.1 ∩ H.edge p.2).Nonempty)
    let L := (H.edge e).sigma A
    let R := (H.edge e).sigma
      (fun v => ((H.edge e).filter (fun w => v < w)).sigma (B v))
    let F : (Sigma (fun _ : V => Finset E)) ⊕
        (Sigma (fun _ : V => Sigma (fun _ : V => E × E))) → Finset E :=
      fun t => Sum.elim (fun p => p.2) (fun p => {p.2.2.1, p.2.2.2}) t
    have hroot {v w : V} (hv : v ∈ H.edge e) (hw : w ∈ H.edge e)
        {a : E} (ha : a ∈ C v) (hb : a ∈ C w) : v = w := by
      by_contra hne
      exact Finset.disjoint_left.mp (hclasses.2.1 v hv w hw hne) ha hb
    have hCN {v : V} (hv : v ∈ H.edge e) : C v ⊆ N := by
      intro a ha
      change a ∈ (Finset.univ.filter (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty))
      rw [← hclasses.2.2.1]
      exact Finset.mem_biUnion.mpr ⟨v, hv, ha⟩
    have hNroot {a : E} (ha : a ∈ N) : ∃ v ∈ H.edge e, a ∈ C v := by
      change a ∈ (Finset.univ.filter (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)) at ha
      rw [← hclasses.2.2.1] at ha
      exact Finset.mem_biUnion.mp ha
    have hAmem (v : V) (s : Finset E) : s ∈ A v ↔
        s.card = 2 ∧ s ⊆ C v ∧
        ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hBmem (v w : V) (a b : E) : (a,b) ∈ B v w ↔
        (a ∈ C v ∧ b ∈ C w) ∧ (H.edge a ∩ H.edge b).Nonempty := by
      simp only [B, Finset.mem_filter, Finset.mem_product]
    have hLmem (v : V) (s : Finset E) :
        Sum.inl ⟨v,s⟩ ∈ L.disjSum R ↔ v ∈ H.edge e ∧ s ∈ A v := by
      simp only [Finset.inl_mem_disjSum, L, Finset.mem_sigma]
    have hRmem (v w : V) (a b : E) :
        Sum.inr ⟨v,⟨w,(a,b)⟩⟩ ∈ L.disjSum R ↔
          v ∈ H.edge e ∧ (w ∈ H.edge e ∧ v < w) ∧ (a,b) ∈ B v w := by
      simp only [Finset.inr_mem_disjSum, R, Finset.mem_sigma, Finset.mem_filter]
    have hLRne {v w u : V} {s : Finset E} {a b : E}
        (hl : Sum.inl ⟨v,s⟩ ∈ L.disjSum R)
        (hr : Sum.inr ⟨w,⟨u,(a,b)⟩⟩ ∈ L.disjSum R) : s ≠ {a,b} := by
      obtain ⟨hv, hs⟩ := (hLmem v s).mp hl
      obtain ⟨hw, ⟨hu, hwu⟩, hab⟩ := (hRmem w u a b).mp hr
      obtain ⟨⟨ha, hb⟩, _⟩ := (hBmem w u a b).mp hab
      have hsub := ((hAmem v s).mp hs).2.1
      intro heq
      have hva := hroot hv hw (hsub (heq ▸ Finset.mem_insert_self a {b})) ha
      have hvb := hroot hv hu (hsub (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))) hb
      exact (ne_of_lt hwu) (hva.symm.trans hvb)
    have hcount : (L.disjSum R).card =
        ((Finset.univ : Finset (Finset E)).filter
          (fun s => s.card = 2 ∧ s ⊆ N ∧
            ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty)).card := by
      apply Finset.card_bij (fun t _ => F t)
      · intro t ht
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases t with ⟨v,s⟩ | ⟨v, w, a,b⟩
        · obtain ⟨hv, hs⟩ := (hLmem v s).mp ht
          obtain ⟨hc, hs, hi⟩ := (hAmem v s).mp hs
          exact ⟨hc, hs.trans (hCN hv), hi⟩
        · obtain ⟨hv, ⟨hw, hvw⟩, hab⟩ := (hRmem v w a b).mp ht
          obtain ⟨⟨ha, hb⟩, hi⟩ := (hBmem v w a b).mp hab
          have hne : a ≠ b := by
            intro heq
            exact (ne_of_lt hvw) (hroot hv hw ha (heq ▸ hb))
          change ({a,b} : Finset E).card = 2 ∧ _
          refine ⟨Finset.card_pair hne, ?_, ?_⟩
          · exact Finset.insert_subset_iff.mpr
              ⟨hCN hv ha, Finset.singleton_subset_iff.mpr (hCN hw hb)⟩
          · intro c hc d hd hcd
            change c ∈ ({a,b} : Finset E) at hc
            change d ∈ ({a,b} : Finset E) at hd
            simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
            rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
            · exact (hcd rfl).elim
            · exact hi
            · simpa only [Finset.inter_comm] using hi
            · exact (hcd rfl).elim
      · intro t ht u hu htu
        rcases t with ⟨v,s⟩ | ⟨v,w,a,b⟩ <;>
          rcases u with ⟨v',s'⟩ | ⟨v',w',a',b'⟩
        · change s = s' at htu
          subst s'
          obtain ⟨hv, hs⟩ := (hLmem v s).mp ht
          obtain ⟨hv', hs'⟩ := (hLmem v' s).mp hu
          obtain ⟨a, ha⟩ := Finset.card_pos.mp
            (show 0 < s.card by rw [((hAmem v s).mp hs).1]; decide)
          have heq := hroot hv hv' (((hAmem v s).mp hs).2.1 ha)
            (((hAmem v' s).mp hs').2.1 ha)
          subst v'
          rfl
        · exact (hLRne ht hu htu).elim
        · exact (hLRne hu ht htu.symm).elim
        · change ({a,b} : Finset E) = {a',b'} at htu
          obtain ⟨hv, ⟨hw, hvw⟩, hab⟩ := (hRmem v w a b).mp ht
          obtain ⟨hv', ⟨hw', hvw'⟩, hab'⟩ := (hRmem v' w' a' b').mp hu
          obtain ⟨⟨ha, hb⟩, _⟩ := (hBmem v w a b).mp hab
          obtain ⟨⟨ha', hb'⟩, _⟩ := (hBmem v' w' a' b').mp hab'
          have hma : a = a' ∨ a = b' := by
            have := htu ▸ Finset.mem_insert_self a {b}
            simpa only [Finset.mem_insert, Finset.mem_singleton] using this
          have hmb : b = a' ∨ b = b' := by
            have := htu ▸ (show b ∈ ({a,b} : Finset E) from by simp)
            simpa only [Finset.mem_insert, Finset.mem_singleton] using this
          rcases hma with rfl | rfl <;> rcases hmb with rfl | rfl
          · exact ((ne_of_lt hvw) (hroot hv hw ha hb)).elim
          · have hvv := hroot hv hv' ha ha'
            have hww := hroot hw hw' hb hb'
            subst v'; subst w'; rfl
          · have hvw'' := hroot hv hw' ha hb'
            have hwv := hroot hw hv' hb ha'
            subst w'; subst v'
            exact (lt_asymm hvw hvw').elim
          · exact ((ne_of_lt hvw) (hroot hv hw ha hb)).elim
      · intro s hs
        obtain ⟨hc, hsN, hi⟩ := (Finset.mem_filter.mp hs).2
        obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
        obtain ⟨v,hv,ha⟩ := hNroot (hsN (Finset.mem_insert_self a {b}))
        obtain ⟨w,hw,hb⟩ := hNroot
          (hsN (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
        have hiab := hi a (by simp) b (by simp) hab
        rcases lt_trichotomy v w with hvw | rfl | hwv
        · refine ⟨Sum.inr ⟨v,⟨w,(a,b)⟩⟩, ?_, rfl⟩
          exact (hRmem v w a b).mpr ⟨hv, ⟨hw,hvw⟩,
            (hBmem v w a b).mpr ⟨⟨ha,hb⟩,hiab⟩⟩
        · refine ⟨Sum.inl ⟨v,{a,b}⟩, ?_, rfl⟩
          apply (hLmem v {a,b}).mpr
          refine ⟨hv, (hAmem v {a,b}).mpr ⟨Finset.card_pair hab, ?_, hi⟩⟩
          exact Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
        · refine ⟨Sum.inr ⟨w,⟨v,(b,a)⟩⟩, ?_, ?_⟩
          · exact (hRmem w v b a).mpr ⟨hw, ⟨hv,hwv⟩,
              (hBmem w v b a).mpr ⟨⟨hb,ha⟩, by
                simpa only [Finset.inter_comm] using hiab⟩⟩
          · exact Finset.pair_comm b a
    have hLcard : L.card = 3 * Nat.choose (D - 1) 2 := by
      rw [Finset.card_sigma]
      calc
        _ = ∑ v ∈ H.edge e, Nat.choose (D - 1) 2 :=
          Finset.sum_congr rfl hwithin
        _ = _ := by simp [hu e]
    rw [Finset.card_disjSum, hLcard] at hcount
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hcount.symm
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, R, Finset.card_sigma,
      Nat.cast_sum, B] using hcast
