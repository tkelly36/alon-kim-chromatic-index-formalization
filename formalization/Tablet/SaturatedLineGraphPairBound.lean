import Tablet.IndependentPairCount
import Tablet.LineGraphOfHypergraph
import Tablet.MaxDegreeAtMost
import Tablet.SaturatedLineGraphEdgeCount
import Tablet.UniformHypergraph

-- [TABLET NODE: SaturatedLineGraphPairBound]
theorem SaturatedLineGraphPairBound :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V],
      ∀ H : MultiHypergraph V E, ∀ e : E,
        UniformHypergraph H 3 →
        MaxDegreeAtMost H D →
        ((Finset.univ : Finset E).filter
          (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)).card = 3 * (D - 1) →
        (3 * (D : ℤ)^2 - 6 * (D : ℤ) + 3 -
            ((∑ x ∈ ((Finset.univ : Finset V).filter
              (fun x => x ∉ H.edge e ∧
                ((Finset.univ : Finset E).filter
                  (fun h => (H.edge h ∩ H.edge e).Nonempty ∧ x ∈ H.edge h)).Nonempty)),
              ∑ p ∈ ((Finset.univ : Finset (Finset V)).filter
                (fun p => p.card = 2 ∧ p ⊆ H.edge e)),
                ∏ v ∈ p,
                  ((Finset.univ : Finset E).filter
                    (fun g => v ∈ H.edge g ∧ x ∈ H.edge g)).card) : ℤ))
          ≤ (@IndependentPairCount E _ _ (LineGraphOfHypergraph H)
              (Classical.decRel (LineGraphOfHypergraph H).Adj) e : ℤ) := by
-- BODY
  classical
  intro D V E _ _ _ _ H e hu hd hN
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  letI : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
  have hedge := SaturatedLineGraphEdgeCount D H e hu hd hN
  dsimp only at hedge
  let N := (Finset.univ : Finset E).filter
    (fun f => f ≠ e ∧ (H.edge f ∩ H.edge e).Nonempty)
  let P := N.powersetCard 2
  let adjacent := fun s : Finset E =>
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (H.edge a ∩ H.edge b).Nonempty
  have hneighbor : (LineGraphOfHypergraph H).neighborFinset e = N := by
    ext f
    simp only [SimpleGraph.mem_neighborFinset, LineGraphOfHypergraph, N,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.inter_comm]
    exact and_congr ne_comm Iff.rfl
  have hcompl (s : Finset E) (hs : s.card = 2) :
      (¬ adjacent s) ↔
        (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b →
          ¬ (LineGraphOfHypergraph H).Adj a b) := by
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs
    have heq : adjacent {a,b} ↔ (H.edge a ∩ H.edge b).Nonempty := by
      constructor
      · exact fun h => h a (by simp) b (by simp) hab
      · intro h x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact h
        · simpa only [Finset.inter_comm] using h
        · exact (hxy rfl).elim
    rw [heq]
    constructor
    · intro h x hx y hy hxy hAdj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact h hAdj.2
      · exact h (by simpa only [Finset.inter_comm] using hAdj.2)
      · exact hxy rfl
    · intro h hi
      exact h (by simp) (by simp) hab ⟨hab, hi⟩
  have hA : P.filter adjacent = (Finset.univ : Finset (Finset E)).filter
      (fun s => s.card = 2 ∧ s ⊆ N ∧ adjacent s) := by
    ext s
    simp only [P, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ, true_and]
    tauto
  have hI : (P.filter (fun s => ¬ adjacent s)).card =
      @IndependentPairCount E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) e := by
    unfold IndependentPairCount
    congr 1
    ext s
    simp only [P, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ,
      true_and, hneighbor]
    constructor
    · rintro ⟨⟨hsub,hcard⟩, hn⟩
      exact ⟨hcard,hsub,(hcompl s hcard).mp hn⟩
    · rintro ⟨hcard,hsub,hi⟩
      exact ⟨⟨hsub,hcard⟩,(hcompl s hcard).mpr hi⟩
  have hcount := Finset.card_filter_add_card_filter_not (s := P) adjacent
  rw [hA, hI, show P.card = Nat.choose (3 * (D - 1)) 2 by
    change (N.powersetCard 2).card = _
    rw [Finset.card_powersetCard]
    exact congrArg (fun n => Nat.choose n 2) hN] at hcount
  have hcountZ := congrArg (fun n : ℕ => (n : ℤ)) hcount
  simp only [Nat.cast_add] at hcountZ
  have hD : 1 ≤ D := by
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (H.edge e).card by rw [hu e]; decide)
    have hp : 0 < HypergraphDegree H v := Finset.card_pos.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
    exact le_trans hp (hd v)
  have hbinom : (Nat.choose (3 * (D - 1)) 2 : ℤ) -
      3 * (Nat.choose (D - 1) 2 : ℤ) = 3 * (D : ℤ)^2 - 6 * (D : ℤ) + 3 := by
    have htwo (n : ℕ) : 2 * (Nat.choose n 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
      cases n with
      | zero => norm_num
      | succ n =>
        have h := Nat.add_one_mul_choose_eq n 1
        simp only [Nat.choose_one_right] at h
        have hz := congrArg (fun n : ℕ => (n : ℤ)) h
        push_cast at hz ⊢
        nlinarith
    have h1 := htwo (3 * (D - 1))
    have h2 := htwo (D - 1)
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hD, Nat.cast_one] at h1
    rw [Nat.cast_sub hD, Nat.cast_one] at h2
    nlinarith
  change _ = _ at hcountZ
  dsimp only [N, adjacent] at hcountZ
  linarith [hedge.1, hedge.2]
