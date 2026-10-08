import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

set_option maxHeartbeats 500000

-- [TABLET NODE: KUniformSaturatedOneIntersectionNeighborCount]
theorem KUniformSaturatedOneIntersectionNeighborCount :
    ∀ k D : ℕ,
      ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          ∀ f : E,
            UniformHypergraph H k →
            (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) →
            (∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
              (H.edge g ∩ H.edge f).card = 1) →
            ((Finset.univ : Finset E).filter
              (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := by
-- BODY
  classical
  intro k D V E _ _ _ H f hunif hsat hone
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)
  have hsum_sat :
      Finset.sum (H.edge f) (fun v =>
          ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)).card)
        = k * (D - 1) := by
    have hcardf : (H.edge f).card = k := hunif f
    calc
      Finset.sum (H.edge f) (fun v =>
          ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)).card)
          = Finset.sum (H.edge f) (fun _ => D - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hf_mem :
                f ∈ (Finset.univ : Finset E).filter (fun g => v ∈ H.edge g) := by
              simp [hv]
            have hdeg :
                ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g)).card = D := by
              simpa [HypergraphDegree] using hsat v hv
            have hfilter :
                ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)) =
                  ((Finset.univ : Finset E).filter (fun g => v ∈ H.edge g)).erase f := by
              ext g
              by_cases hgf : g = f
              · subst hgf
                simp [hv]
              · simp [hgf]
            rw [hfilter, Finset.card_erase_of_mem hf_mem, hdeg]
      _ = (H.edge f).card * (D - 1) := by simp
      _ = k * (D - 1) := by rw [hcardf]
  have hleft :
      (∑ v ∈ H.edge f, (N.bipartiteAbove (fun v g => v ∈ H.edge g) v).card)
        = ∑ v ∈ H.edge f,
          ((Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)).card := by
    apply Finset.sum_congr rfl
    intro v hv
    apply congrArg Finset.card
    ext g
    constructor
    · intro hg
      have hp : g ∈ N ∧ v ∈ H.edge g := by
        simpa [Finset.bipartiteAbove] using hg
      have hmem : g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty := by
        simpa [N] using hp.1
      exact by simp [hmem.1, hp.2]
    · intro hg
      have hmem : g ≠ f ∧ v ∈ H.edge g := by simpa using hg
      have hgf : g ≠ f := hmem.1
      have hvg : v ∈ H.edge g := hmem.2
      have hnon : (H.edge g ∩ H.edge f).Nonempty :=
        ⟨v, Finset.mem_inter.mpr ⟨hvg, hv⟩⟩
      have hNmem : g ∈ N := by simp [N, hgf, hnon]
      exact (by simpa [Finset.bipartiteAbove] using And.intro hNmem hvg)
  have hright_each : ∀ g ∈ N,
      ((H.edge f).bipartiteBelow (fun v g => v ∈ H.edge g) g).card = 1 := by
    intro g hg
    have hmem : g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty := by
      simpa [N] using hg
    rcases hmem with ⟨hgf, hnon⟩
    have hcard := hone g hgf hnon
    have hset :
        (H.edge f).bipartiteBelow (fun v g => v ∈ H.edge g) g = H.edge f ∩ H.edge g := by
      ext v
      simp [Finset.bipartiteBelow, Finset.mem_inter]
    rw [hset, Finset.inter_comm, hcard]
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v g => v ∈ H.edge g) (s := H.edge f) (t := N)
  have hNsum :
      (∑ g ∈ N, ((H.edge f).bipartiteBelow (fun v g => v ∈ H.edge g) g).card) =
        N.card := by
    calc
      (∑ g ∈ N, ((H.edge f).bipartiteBelow (fun v g => v ∈ H.edge g) g).card)
          = ∑ g ∈ N, 1 := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hright_each g hg
      _ = N.card := by simp
  have hN : N.card = k * (D - 1) := by
    rw [← hNsum, ← hdouble, hleft, hsum_sat]
  have harith : k * (D - 1) = k * D - k := by
    rw [Nat.mul_sub_left_distrib]
    simp
  simpa [N, harith] using hN
