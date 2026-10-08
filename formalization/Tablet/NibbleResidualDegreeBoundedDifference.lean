import Tablet.LineGraphOfHypergraph
import Mathlib.Combinatorics.SimpleGraph.Clique

-- [TABLET NODE: NibbleResidualDegreeBoundedDifference]
theorem NibbleResidualDegreeBoundedDifference
    {V E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    [Fintype K] [DecidableEq K] (H : MultiHypergraph V E)
    (I J : K → Finset E) (a : K)
    (hI : (LineGraphOfHypergraph H).IsIndepSet (I a : Set E))
    (hJ : (LineGraphOfHypergraph H).IsIndepSet (J a : Set E))
    (hagree : ∀ b, b ≠ a → I b = J b) (x : V) :
    |((((Finset.univ : Finset E).filter
        (fun e => x ∈ H.edge e ∧ ∀ b, e ∉ I b)).card : ℝ) -
      (((Finset.univ : Finset E).filter
        (fun e => x ∈ H.edge e ∧ ∀ b, e ∉ J b)).card : ℝ))| ≤ 1 := by
-- BODY
  classical
  let T := (Finset.univ : Finset E).filter
    (fun e => x ∈ H.edge e ∧ ∀ b, b ≠ a → e ∉ I b)
  have hcard (S : Finset E)
      (hS : (LineGraphOfHypergraph H).IsIndepSet (S : Set E)) :
      (T ∩ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e he f hf
    by_contra hne
    have heT := (Finset.mem_filter.mp (Finset.mem_inter.mp he).1).2.1
    have hfT := (Finset.mem_filter.mp (Finset.mem_inter.mp hf).1).2.1
    exact (hS
      (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hf).2 hne)
      ⟨hne, x, Finset.mem_inter.mpr ⟨heT, hfT⟩⟩
  have hleft : (Finset.univ : Finset E).filter
      (fun e => x ∈ H.edge e ∧ ∀ b, e ∉ I b) = T \ I a := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, T]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, fun b _ => h b⟩, h a⟩
    · rintro ⟨⟨hx, h⟩, ha⟩
      refine ⟨hx, fun b => ?_⟩
      by_cases hb : b = a
      · simpa [hb] using ha
      · exact h b hb
  have hright : (Finset.univ : Finset E).filter
      (fun e => x ∈ H.edge e ∧ ∀ b, e ∉ J b) = T \ J a := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, T]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, fun b hb => by simpa [hagree b hb] using h b⟩, h a⟩
    · rintro ⟨⟨hx, h⟩, ha⟩
      refine ⟨hx, fun b => ?_⟩
      by_cases hb : b = a
      · simpa [hb] using ha
      · simpa [← hagree b hb] using h b hb
  rw [hleft, hright]
  have hi := hcard (I a) hI
  have hj := hcard (J a) hJ
  have ei := Finset.card_sdiff_add_card_inter T (I a)
  have ej := Finset.card_sdiff_add_card_inter T (J a)
  have hle : (T \ I a).card ≤ (T \ J a).card + 1 := by omega
  have hge : (T \ J a).card ≤ (T \ I a).card + 1 := by omega
  have hle' : ((T \ I a).card : ℝ) ≤ (T \ J a).card + 1 := by exact_mod_cast hle
  have hge' : ((T \ J a).card : ℝ) ≤ (T \ I a).card + 1 := by exact_mod_cast hge
  exact abs_le.mpr ⟨by linarith, by linarith⟩
