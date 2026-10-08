import Tablet.ChromaticIndexAtMost
import Tablet.FiniteGraphGreedyColoring
import Tablet.UniformHypergraphLineDegreeBound

-- [TABLET NODE: PartialEdgeColoringGreedyFinish]
theorem PartialEdgeColoringGreedyFinish {V E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) (k K N : ℕ) (hu : UniformHypergraph H k)
    (C : Finset E) (c : {e : E // e ∈ C} → Fin K)
    (hc : ∀ e f, e ≠ f → (H.edge e.val ∩ H.edge f.val).Nonempty → c e ≠ c f)
    (hd : MaxDegreeAtMost
      (⟨fun e : {e : E // e ∉ C} => H.edge e.val⟩ :
        MultiHypergraph V {e : E // e ∉ C}) N) :
    ChromaticIndexAtMost H (K + (k * N + 1)) := by
-- BODY
  classical
  let R := {e : E // e ∉ C}
  let Hr : MultiHypergraph V R := ⟨fun e => H.edge e.val⟩
  have hur : UniformHypergraph Hr k := fun e => hu e.val
  have hline (e : R) : (LineGraphOfHypergraph Hr).degree e < k * N + 1 :=
    lt_of_le_of_lt ((UniformHypergraphLineDegreeBound Hr hur hd e).trans
      (Nat.mul_le_mul_left k (Nat.sub_le N 1))) (Nat.lt_succ_self _)
  obtain ⟨d, hdproper⟩ := FiniteGraphGreedyColoring (LineGraphOfHypergraph Hr)
    (Nat.succ_pos _) hline
  let f : E → Fin (K + (k * N + 1)) := fun e =>
    if he : e ∈ C then ⟨(c ⟨e, he⟩).val, by omega⟩
    else ⟨K + (d ⟨e, he⟩).val, by have := (d ⟨e, he⟩).isLt; omega⟩
  refine ⟨f, ?_⟩
  intro e g heg hint hfg
  have hv := congrArg Fin.val hfg
  by_cases he : e ∈ C <;> by_cases hg : g ∈ C
  · have h := hc ⟨e, he⟩ ⟨g, hg⟩ (by intro h; exact heg (congrArg Subtype.val h)) hint
    exact h (Fin.ext (by simpa [f, he, hg] using hv))
  · simp only [f, dif_pos he, dif_neg hg] at hv
    have := (c ⟨e, he⟩).isLt
    omega
  · simp only [f, dif_neg he, dif_pos hg] at hv
    have := (c ⟨g, hg⟩).isLt
    omega
  · have ha : (LineGraphOfHypergraph Hr).Adj ⟨e, he⟩ ⟨g, hg⟩ :=
      ⟨by intro h; exact heg (congrArg Subtype.val h), hint⟩
    apply hdproper _ _ ha
    apply Fin.ext
    simpa [f, he, hg] using hv
