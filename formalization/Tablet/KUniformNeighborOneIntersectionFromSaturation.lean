import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

set_option maxHeartbeats 700000

-- [TABLET NODE: KUniformNeighborOneIntersectionFromSaturation]
theorem KUniformNeighborOneIntersectionFromSaturation :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          ∀ f : E,
            UniformHypergraph H k →
            (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
            ((Finset.univ : Finset E).filter
              (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k →
            ∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
              (H.edge g ∩ H.edge f).card = 1 := by
-- BODY
  classical
  intro k D V E _ _ _ H f hunif hsat hneighbor_card g hgf hnon
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
  let m : E → ℕ := fun e => (H.edge f ∩ H.edge e).card
  have hsum_sat :
      Finset.sum (H.edge f) (fun v =>
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ v ∈ H.edge e)).card)
        = k * (D - 1) := by
    have hcardf : (H.edge f).card = k := hunif f
    calc
      Finset.sum (H.edge f) (fun v =>
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ v ∈ H.edge e)).card)
          = Finset.sum (H.edge f) (fun _ => D - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hf_mem :
                f ∈ (Finset.univ : Finset E).filter (fun e => v ∈ H.edge e) := by
              simp [hv]
            have hdeg :
                ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).card = D := by
              simpa [HypergraphDegree] using hsat v hv
            have hfilter :
                ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ v ∈ H.edge e)) =
                  ((Finset.univ : Finset E).filter (fun e => v ∈ H.edge e)).erase f := by
              ext e
              by_cases hef : e = f
              · subst hef
                simp [hv]
              · simp [hef]
            rw [hfilter, Finset.card_erase_of_mem hf_mem, hdeg]
      _ = (H.edge f).card * (D - 1) := by simp
      _ = k * (D - 1) := by rw [hcardf]
  have hleft :
      (∑ v ∈ H.edge f, (N.bipartiteAbove (fun v e => v ∈ H.edge e) v).card)
        = ∑ v ∈ H.edge f,
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ v ∈ H.edge e)).card := by
    apply Finset.sum_congr rfl
    intro v hv
    apply congrArg Finset.card
    ext e
    constructor
    · intro he
      have hp : e ∈ N ∧ v ∈ H.edge e := by
        simpa [Finset.bipartiteAbove] using he
      have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
        simpa [N] using hp.1
      exact by simp [hmem.1, hp.2]
    · intro he
      have hmem : e ≠ f ∧ v ∈ H.edge e := by simpa using he
      have hnon' : (H.edge e ∩ H.edge f).Nonempty :=
        ⟨v, Finset.mem_inter.mpr ⟨hmem.2, hv⟩⟩
      have hNmem : e ∈ N := by simp [N, hmem.1, hnon']
      exact (by simpa [Finset.bipartiteAbove] using And.intro hNmem hmem.2)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v e => v ∈ H.edge e) (s := H.edge f) (t := N)
  have hbelow_eq (e : E) :
      (H.edge f).bipartiteBelow (fun v e => v ∈ H.edge e) e = H.edge f ∩ H.edge e := by
    ext v
    simp [Finset.bipartiteBelow, Finset.mem_inter]
  have hsum_m :
      (∑ e ∈ N, m e) = k * (D - 1) := by
    calc
      (∑ e ∈ N, m e)
          = ∑ e ∈ N, ((H.edge f).bipartiteBelow (fun v e => v ∈ H.edge e) e).card := by
            apply Finset.sum_congr rfl
            intro e he
            rw [hbelow_eq]
      _ = ∑ v ∈ H.edge f, (N.bipartiteAbove (fun v e => v ∈ H.edge e) v).card := by
            rw [hdouble]
      _ = k * (D - 1) := by
            rw [hleft, hsum_sat]
  have hN_card : N.card = k * (D - 1) := by
    have harith : k * D - k = k * (D - 1) := by
      rw [Nat.mul_sub_left_distrib]
      simp
    simpa [N, harith] using hneighbor_card
  have hN_g : g ∈ N := by
    simp [N, hgf, hnon]
  have hone_le : ∀ e ∈ N, 1 ≤ m e := by
    intro e he
    have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
      simpa [N] using he
    rcases hmem.2 with ⟨x, hx⟩
    rcases Finset.mem_inter.mp hx with ⟨hxe, hxf⟩
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxf, hxe⟩⟩
  by_contra hnot
  have htwo : 2 ≤ m g := by
    have hmg : m g = (H.edge g ∩ H.edge f).card := by
      dsimp [m]
      rw [Finset.inter_comm]
    have hnot_m : m g ≠ 1 := by
      intro hm
      exact hnot (by simpa [hmg] using hm)
    have hg_one : 1 ≤ m g := hone_le g hN_g
    omega
  have hsum_erase :
      (∑ e ∈ N, m e) = m g + ∑ e ∈ N.erase g, m e := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hN_g]
    rw [Finset.sdiff_singleton_eq_erase]
  have herase_le :
      (N.erase g).card ≤ ∑ e ∈ N.erase g, m e := by
    calc
      (N.erase g).card = ∑ e ∈ N.erase g, 1 := by simp
      _ ≤ ∑ e ∈ N.erase g, m e := by
            exact Finset.sum_le_sum fun e he => hone_le e (Finset.mem_of_mem_erase he)
  have hcard_erase : N.card = (N.erase g).card + 1 := by
    rw [Finset.card_erase_of_mem hN_g]
    omega
  have hextra : N.card + 1 ≤ ∑ e ∈ N, m e := by
    rw [hsum_erase, hcard_erase]
    omega
  omega
