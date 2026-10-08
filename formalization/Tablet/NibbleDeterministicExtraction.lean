import Tablet.NibbleResidualDegree
import Tablet.NibbleDeletedColors
import Tablet.HypergraphDegree
import Mathlib.Combinatorics.SimpleGraph.Clique

-- [TABLET NODE: NibbleDeterministicExtraction]
theorem NibbleDeterministicExtraction {V E K : Type*} [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq E] [DecidableEq K]
    (H : MultiHypergraph V E) (L M : E → Finset K) (I : K → Finset E)
    (hsub : ∀ e, M e ⊆ L e)
    (hcolor : ∀ a e, e ∈ I a → a ∈ M e)
    (hind : ∀ a, (LineGraphOfHypergraph H).IsIndepSet (I a : Set E)) :
    ∃ C : Finset E, ∃ c : {e // e ∈ C} → K,
      (∀ e, e ∈ C ↔ ∃ a, e ∈ I a) ∧
      (∀ e, c e ∈ L e.val) ∧
      (∀ e f, e ≠ f → (H.edge e.val ∩ H.edge f.val).Nonempty → c e ≠ c f) ∧
      ∃ Lc : {e // e ∉ C} → Finset K,
        (∀ f a, a ∈ Lc f ↔ a ∈ L f.val ∧
          ∀ e, c e = a → ¬ (H.edge e.val ∩ H.edge f.val).Nonempty) ∧
        (∀ x, @HypergraphDegree V {e // e ∉ C} _ _ _
          ⟨fun f => H.edge f.val⟩ x = NibbleResidualDegree H I x) ∧
        (∀ f, (M f.val).card - (NibbleDeletedColors H M I f.val).card ≤
          (Lc f).card) := by
-- BODY
  classical
  let C : Finset E := Finset.univ.filter fun e => ∃ a, e ∈ I a
  have hC (e : E) : e ∈ C ↔ ∃ a, e ∈ I a := by simp [C]
  have hex (e : {e // e ∈ C}) : ∃ a, e.val ∈ I a := (hC e.val).mp e.property
  let c : {e // e ∈ C} → K := fun e => Classical.choose (hex e)
  have hc (e : {e // e ∈ C}) : e.val ∈ I (c e) := Classical.choose_spec (hex e)
  let Lc : {e // e ∉ C} → Finset K := fun f => (L f.val).filter fun a =>
    ∀ e, c e = a → ¬ (H.edge e.val ∩ H.edge f.val).Nonempty
  refine ⟨C, c, hC, ?_, ?_, Lc, ?_, ?_, ?_⟩
  · intro e
    exact hsub e.val (hcolor (c e) e.val (hc e))
  · intro e f hef hinter hsame
    have hne : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    exact (hind (c e) (hc e) (by simpa [hsame] using hc f) hne) ⟨hne, hinter⟩
  · intro f a
    simp only [Lc, Finset.mem_filter]
  · intro x
    unfold HypergraphDegree NibbleResidualDegree
    apply Finset.card_bij (fun f _ => f.val)
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact ⟨hf, fun a ha => f.property ((hC f.val).mpr ⟨a, ha⟩)⟩
    · intro f _ g _ h
      exact Subtype.ext h
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hn : e ∉ C := by
        intro h
        obtain ⟨a, ha⟩ := (hC e).mp h
        exact he.2 a ha
      exact ⟨⟨e, hn⟩, by simpa using he.1, rfl⟩
  · intro f
    have hdel : NibbleDeletedColors H M I f.val ⊆ M f.val :=
      Finset.filter_subset _ _
    have hkeep : M f.val \ NibbleDeletedColors H M I f.val ⊆ Lc f := by
      intro a ha
      obtain ⟨haM, haD⟩ := Finset.mem_sdiff.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨hsub f.val haM, ?_⟩
      intro e hea hinter
      apply haD
      apply Finset.mem_filter.mpr
      refine ⟨haM, e.val, ?_, ?_⟩
      · simpa [hea] using hc e
      · refine ⟨?_, ?_⟩
        · intro h
          exact f.property (h ▸ e.property)
        · simpa [Finset.inter_comm] using hinter
    rw [← Finset.card_sdiff_of_subset hdel]
    exact Finset.card_le_card hkeep
