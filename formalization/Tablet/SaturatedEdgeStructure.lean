import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.LineGraphOfHypergraph

open scoped BigOperators

-- [TABLET NODE: SaturatedEdgeStructure]
theorem SaturatedEdgeStructure :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E,
        H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
        ∀ e : E,
          ((Finset.univ : Finset E).filter
            (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)).card = 3 * (D - 1) →
          (∀ f : E, f ≠ e →
            (H.edge f ∩ H.edge e).card ≤ 1) ∧
          (∀ x : V, x ∈ ((Finset.univ : Finset V).filter
              (fun x => x ∉ H.edge e ∧
                ((Finset.univ : Finset E).filter
                  (fun h => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)) →
            (∑ v ∈ H.edge e,
              ((Finset.univ : Finset E).filter
                (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)).card) ≤ D) ∧
          (∀ v : V, v ∈ H.edge e →
            (∑ x ∈ ((Finset.univ : Finset V).filter
              (fun x => x ∉ H.edge e ∧
                ((Finset.univ : Finset E).filter
                  (fun h => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)),
              ((Finset.univ : Finset E).filter
                (fun g => g ≠ e ∧ v ∈ H.edge g ∧ x ∈ H.edge g)).card)
              = 2 * (D - 1)) := by
-- BODY
  classical
  intro D V E _ _ _ _ H hH e hN
  have hu := hH.1
  have hd := hH.2.2
  have hecard : (H.edge e).card = 3 := hu e
  let A := fun v : V => Finset.univ.filter (fun g : E => g ≠ e ∧ v ∈ H.edge g)
  let N := Finset.univ.filter (fun g : E => g ≠ e ∧ (H.edge g ∩ H.edge e).Nonempty)
  have hA (v : V) (hv : v ∈ H.edge e) : (A v).card ≤ D - 1 := by
    have hm : e ∈ Finset.univ.filter (fun g => v ∈ H.edge g) := by simp [hv]
    have ha : A v = (Finset.univ.filter (fun g => v ∈ H.edge g)).erase e := by
      ext g
      simp [A]
    rw [ha, Finset.card_erase_of_mem hm]
    exact Nat.sub_le_sub_right (hd v) 1
  have hdouble : (∑ v ∈ H.edge e, (A v).card) =
      ∑ g ∈ N, (H.edge g ∩ H.edge e).card := by
    have ha (v : V) (hv : v ∈ H.edge e) :
        A v = N.filter (fun g => v ∈ H.edge g) := by
      ext g
      simp only [A, N, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨⟨h.1, ⟨v, Finset.mem_inter.mpr ⟨h.2, hv⟩⟩⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    calc
      _ = ∑ v ∈ H.edge e, (N.filter (fun g => v ∈ H.edge g)).card :=
        Finset.sum_congr rfl (fun v hv => congrArg Finset.card (ha v hv))
      _ = ∑ g ∈ N, ((H.edge e).filter (fun v => v ∈ H.edge g)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm
      _ = _ := by simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
  have hlo (g : E) (hg : g ∈ N) : 1 ≤ (H.edge g ∩ H.edge e).card :=
    Finset.card_pos.mpr (Finset.mem_filter.mp hg).2.2
  have hupper : (∑ v ∈ H.edge e, (A v).card) ≤ 3 * (D - 1) := by
    calc
      _ ≤ ∑ v ∈ H.edge e, (D - 1) := Finset.sum_le_sum hA
      _ = _ := by simp [hecard]
  have hlower : 3 * (D - 1) ≤ ∑ g ∈ N, (H.edge g ∩ H.edge e).card := by
    calc
      _ = ∑ g ∈ N, 1 := by simpa [N] using hN.symm
      _ ≤ _ := Finset.sum_le_sum hlo
  have htotal : (∑ v ∈ H.edge e, (A v).card) = 3 * (D - 1) := by omega
  have hAsat (v : V) (hv : v ∈ H.edge e) : (A v).card = D - 1 := by
    apply (Finset.sum_eq_sum_iff_of_le hA).mp _ v hv
    simpa [hecard] using htotal
  have hone (g : E) (hg : g ∈ N) : (H.edge g ∩ H.edge e).card = 1 := by
    symm
    apply (Finset.sum_eq_sum_iff_of_le hlo).mp _ g hg
    simpa [N, hN] using (hdouble.symm.trans htotal).symm
  have hs (g : E) (hg : g ≠ e) : (H.edge g ∩ H.edge e).card ≤ 1 := by
    by_cases hn : (H.edge g ∩ H.edge e).Nonempty
    · exact (hone g (by simp [N, hg, hn])).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  refine ⟨hs, ?_, ?_⟩
  · intro x hx
    have hxe := (Finset.mem_filter.mp hx).2.1
    calc
      _ = ∑ g ∈ Finset.univ.filter (fun g => x ∈ H.edge g),
          ((H.edge e).filter (fun v => v ∈ H.edge g)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hxg : x ∈ H.edge g <;> simp [hxg]
      _ ≤ ∑ g ∈ Finset.univ.filter (fun g => x ∈ H.edge g), 1 := by
        apply Finset.sum_le_sum
        intro g hg
        have hge : g ≠ e := by
          intro h
          subst g
          exact hxe (Finset.mem_filter.mp hg).2
        simpa [Finset.filter_mem_eq_inter, Finset.inter_comm] using hs g hge
      _ ≤ D := by simpa [HypergraphDegree] using hd x
  · intro v hv
    let X := Finset.univ.filter (fun x : V => x ∉ H.edge e ∧
      (Finset.univ.filter (fun h : E => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)
    have hgX (g : E) (hg : g ∈ A v) :
        X.filter (fun x => x ∈ H.edge g) = H.edge g \ H.edge e := by
      obtain ⟨hge, hvg⟩ := (Finset.mem_filter.mp hg).2
      ext x
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · exact fun h => ⟨h.2, h.1.1⟩
      · intro h
        refine ⟨⟨h.2, ⟨g, ?_⟩⟩, h.1⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hvg, hv⟩⟩, h.1⟩
    have htwo (g : E) (hg : g ∈ A v) : (X.filter (fun x => x ∈ H.edge g)).card = 2 := by
      obtain ⟨hge, hvg⟩ := (Finset.mem_filter.mp hg).2
      have hn : g ∈ N := by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hge, ⟨v, Finset.mem_inter.mpr ⟨hvg, hv⟩⟩⟩
      rw [hgX g hg, Finset.card_sdiff, hu g, Finset.inter_comm, hone g hn]
    change (∑ x ∈ X, _) = _
    calc
      _ = ∑ g ∈ A v, (X.filter (fun x => x ∈ H.edge g)).card := by
        simp only [A, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hge : g = e <;> by_cases hvg : v ∈ H.edge g <;> simp [hge, hvg]
      _ = ∑ g ∈ A v, 2 := Finset.sum_congr rfl htwo
      _ = 2 * (D - 1) := by simp [hAsat v hv, Nat.mul_comm]
