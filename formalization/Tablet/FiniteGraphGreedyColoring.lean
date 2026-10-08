import Tablet.Preamble

-- [TABLET NODE: FiniteGraphGreedyColoring]
theorem FiniteGraphGreedyColoring {E : Type*} [Fintype E] [DecidableEq E]
    (G : SimpleGraph E) [DecidableRel G.Adj] {q : ℕ}
    (hq : 0 < q) (hd : ∀ e, G.degree e < q) :
    ∃ c : E → Fin q, ∀ e f, G.Adj e f → c e ≠ c f := by
-- BODY
  classical
  have build : ∀ s : Finset E, ∃ c : E → Fin q,
      ∀ e ∈ s, ∀ f ∈ s, G.Adj e f → c e ≠ c f := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hq⟩, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨c, hc⟩ := ih
      let bad := ((G.neighborFinset a) ∩ s).image c
      have hbad : bad.card < (Finset.univ : Finset (Fin q)).card := by
        calc
          bad.card ≤ ((G.neighborFinset a) ∩ s).card := Finset.card_image_le
          _ ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
          _ < q := hd a
          _ = (Finset.univ : Finset (Fin q)).card := by simp
      obtain ⟨b, hb, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
      let c' : E → Fin q := fun e => if e = a then b else c e
      refine ⟨c', ?_⟩
      intro e he f hf hef
      have hne := G.ne_of_adj hef
      rcases Finset.mem_insert.mp he with heq | he
      · subst e
        have hfa : f ≠ a := hne.symm
        have hfs : f ∈ s := (Finset.mem_insert.mp hf).resolve_left hfa
        have hcb : c f ≠ b := by
          intro h
          apply hbnot
          exact Finset.mem_image.mpr ⟨f, Finset.mem_inter.mpr
            ⟨(G.mem_neighborFinset a f).mpr hef, hfs⟩, h⟩
        simpa [c', hfa] using hcb.symm
      · rcases Finset.mem_insert.mp hf with heq | hf
        · subst f
          have hea : e ≠ a := hne
          have hcb : c e ≠ b := by
            intro h
            apply hbnot
            exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset a e).mpr hef.symm, he⟩, h⟩
          simpa [c', hea] using hcb
        · have hea : e ≠ a := fun h => ha (h ▸ he)
          have hfa : f ≠ a := fun h => ha (h ▸ hf)
          simpa [c', hea, hfa] using hc e he f hf hef
  obtain ⟨c, hc⟩ := build Finset.univ
  exact ⟨c, fun e f hef => hc e (Finset.mem_univ _) f (Finset.mem_univ _) hef⟩
