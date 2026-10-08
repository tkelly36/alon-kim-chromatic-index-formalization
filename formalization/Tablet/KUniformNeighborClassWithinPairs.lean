import Mathlib.Data.Finset.Powerset
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

set_option maxHeartbeats 800000

-- [TABLET NODE: KUniformNeighborClassWithinPairs]
theorem KUniformNeighborClassWithinPairs :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          ∀ f : E,
            UniformHypergraph H k →
            (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
            (∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
              (H.edge g ∩ H.edge f).card = 1) →
            let C : V → Finset E :=
              fun v => (Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)
            let N : Finset E :=
              (Finset.univ : Finset E).filter
                (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)
            let sameClassPairs : Finset (Finset E) :=
              (Finset.univ : Finset (Finset E)).filter
                (fun S => S.card = 2 ∧ ∃ v ∈ H.edge f, S ⊆ C v)
            (∀ v : V, v ∈ H.edge f → (C v).card = D - 1) ∧
              (∀ u : V, u ∈ H.edge f → ∀ v : V, v ∈ H.edge f → u ≠ v →
                Disjoint (C u) (C v)) ∧
              (∀ g : E, g ∈ N ↔ ∃ v ∈ H.edge f, g ∈ C v) ∧
              sameClassPairs.card ≤ k * Nat.choose (D - 1) 2 := by
-- BODY
  classical
  intro k D V E _ _ _ H f hunif hsat hone
  let C : V → Finset E :=
    fun v => (Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)
  let N : Finset E :=
    (Finset.univ : Finset E).filter
      (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)
  let sameClassPairs : Finset (Finset E) :=
    (Finset.univ : Finset (Finset E)).filter
      (fun S => S.card = 2 ∧ ∃ v ∈ H.edge f, S ⊆ C v)
  have hC_card : ∀ v : V, v ∈ H.edge f → (C v).card = D - 1 := by
    intro v hv
    have hf_mem :
        f ∈ (Finset.univ : Finset E).filter (fun g => v ∈ H.edge g) := by
      simp [hv]
    have hdeg :
        ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g)).card = D := by
      simpa [HypergraphDegree] using hsat v hv
    have hfilter :
        C v = ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g)).erase f := by
      ext g
      by_cases hgf : g = f
      · subst hgf
        simp [C, hv]
      · simp [C, hgf]
    rw [hfilter, Finset.card_erase_of_mem hf_mem, hdeg]
  have hdisjoint :
      ∀ u : V, u ∈ H.edge f → ∀ v : V, v ∈ H.edge f → u ≠ v →
        Disjoint (C u) (C v) := by
    intro u hu v hv huv
    rw [Finset.disjoint_left]
    intro g hgu hgv
    have hgu' : g ≠ f ∧ u ∈ H.edge g := by
      simpa [C] using hgu
    have hgv' : g ≠ f ∧ v ∈ H.edge g := by
      simpa [C] using hgv
    have hnon : (H.edge g ∩ H.edge f).Nonempty :=
      ⟨u, Finset.mem_inter.mpr ⟨hgu'.2, hu⟩⟩
    have hcard := hone g hgu'.1 hnon
    have hpair_sub : ({u, v} : Finset V) ⊆ H.edge g ∩ H.edge f := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hgu'.2, hu⟩
      · exact Finset.mem_inter.mpr ⟨hgv'.2, hv⟩
    have htwo : 2 ≤ (H.edge g ∩ H.edge f).card := by
      calc
        2 = ({u, v} : Finset V).card := (Finset.card_pair huv).symm
        _ ≤ (H.edge g ∩ H.edge f).card := Finset.card_le_card hpair_sub
    omega
  have hN_cover : ∀ g : E, g ∈ N ↔ ∃ v ∈ H.edge f, g ∈ C v := by
    intro g
    constructor
    · intro hg
      have hg' : g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty := by
        simpa [N] using hg
      rcases hg'.2 with ⟨v, hv⟩
      rcases Finset.mem_inter.mp hv with ⟨hvg, hvf⟩
      exact ⟨v, hvf, by simp [C, hg'.1, hvg]⟩
    · rintro ⟨v, hvf, hgv⟩
      have hgv' : g ≠ f ∧ v ∈ H.edge g := by
        simpa [C] using hgv
      have hnon : (H.edge g ∩ H.edge f).Nonempty :=
        ⟨v, Finset.mem_inter.mpr ⟨hgv'.2, hvf⟩⟩
      simp [N, hgv'.1, hnon]
  have hsame_subset :
      sameClassPairs ⊆ (H.edge f).biUnion (fun v => (C v).powersetCard 2) := by
    intro S hS
    have hS' : S.card = 2 ∧ ∃ v ∈ H.edge f, S ⊆ C v := by
      simpa [sameClassPairs] using hS
    rcases hS'.2 with ⟨v, hvf, hsub⟩
    exact Finset.mem_biUnion.mpr
      ⟨v, hvf, Finset.mem_powersetCard.mpr ⟨hsub, hS'.1⟩⟩
  have hsame_card_le_union :
      sameClassPairs.card ≤ ((H.edge f).biUnion (fun v => (C v).powersetCard 2)).card :=
    Finset.card_le_card hsame_subset
  have hunion_le_sum :
      ((H.edge f).biUnion (fun v => (C v).powersetCard 2)).card ≤
        ∑ v ∈ H.edge f, ((C v).powersetCard 2).card := by
    exact Finset.card_biUnion_le
  have hsum_choose :
      (∑ v ∈ H.edge f, ((C v).powersetCard 2).card) =
        k * Nat.choose (D - 1) 2 := by
    calc
      (∑ v ∈ H.edge f, ((C v).powersetCard 2).card)
          = ∑ v ∈ H.edge f, Nat.choose (D - 1) 2 := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.card_powersetCard, hC_card v hv]
      _ = (H.edge f).card * Nat.choose (D - 1) 2 := by simp
      _ = k * Nat.choose (D - 1) 2 := by rw [hunif f]
  exact ⟨hC_card, hdisjoint, hN_cover, by
    exact hsame_card_le_union.trans (hunion_le_sum.trans_eq hsum_choose)⟩
