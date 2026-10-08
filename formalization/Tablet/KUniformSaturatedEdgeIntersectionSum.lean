import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Tablet.HypergraphDegree
import Tablet.UniformHypergraph

-- [TABLET NODE: KUniformSaturatedEdgeIntersectionSum]
theorem KUniformSaturatedEdgeIntersectionSum
    (k D : ℕ) {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) (f : E)
    (hunif : UniformHypergraph H k)
    (hsat : ∀ x : V, x ∈ H.edge f → HypergraphDegree H x = D) :
    (∑ e ∈ (Finset.univ : Finset E).filter
      (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty),
      (H.edge f ∩ H.edge e).card) = k * (D - 1) := by
-- BODY
  classical
  let N : Finset E := (Finset.univ : Finset E).filter
    (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
  have hsum_sat :
      Finset.sum (H.edge f) (fun x =>
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)).card)
        = k * (D - 1) := by
    have hcardf : (H.edge f).card = k := hunif f
    calc
      Finset.sum (H.edge f) (fun x =>
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)).card)
          = Finset.sum (H.edge f) (fun _ => D - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hf_mem :
                f ∈ (Finset.univ : Finset E).filter (fun e => x ∈ H.edge e) := by
              simp [hx]
            have hdeg :
                ((Finset.univ : Finset E).filter (fun e => x ∈ H.edge e)).card = D := by
              simpa [HypergraphDegree] using hsat x hx
            have hfilter :
                ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)) =
                  ((Finset.univ : Finset E).filter (fun e => x ∈ H.edge e)).erase f := by
              ext e
              by_cases hef : e = f
              · subst hef
                simp [hx]
              · simp [hef]
            rw [hfilter, Finset.card_erase_of_mem hf_mem, hdeg]
      _ = (H.edge f).card * (D - 1) := by simp
      _ = k * (D - 1) := by rw [hcardf]
  have hleft :
      (∑ x ∈ H.edge f, (N.bipartiteAbove (fun x e => x ∈ H.edge e) x).card)
        = ∑ x ∈ H.edge f,
          ((Finset.univ : Finset E).filter (fun e => e ≠ f ∧ x ∈ H.edge e)).card := by
    apply Finset.sum_congr rfl
    intro x hx
    apply congrArg Finset.card
    ext e
    constructor
    · intro he
      have hp : e ∈ N ∧ x ∈ H.edge e := by
        simpa [Finset.bipartiteAbove] using he
      have hmem : e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty := by
        simpa [N] using hp.1
      exact by simp [hmem.1, hp.2]
    · intro he
      have hmem : e ≠ f ∧ x ∈ H.edge e := by simpa using he
      have hnon : (H.edge e ∩ H.edge f).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hmem.2, hx⟩⟩
      have hNmem : e ∈ N := by simp [N, hmem.1, hnon]
      exact (by simpa [Finset.bipartiteAbove] using And.intro hNmem hmem.2)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun x e => x ∈ H.edge e) (s := H.edge f) (t := N)
  have hbelow_eq (e : E) :
      (H.edge f).bipartiteBelow (fun x e => x ∈ H.edge e) e = H.edge f ∩ H.edge e := by
    ext x
    simp [Finset.bipartiteBelow, Finset.mem_inter]
  change (∑ e ∈ N, (H.edge f ∩ H.edge e).card) = k * (D - 1)
  simp_rw [← hbelow_eq]
  rw [← hdouble, hleft, hsum_sat]
