import Tablet.Preamble

-- [TABLET NODE: FiniteBipartiteIncidenceTableRowBound]
theorem FiniteBipartiteIncidenceTableRowBound :
    ∀ {V E : Type*} [DecidableEq V] [DecidableEq E],
      ∀ (X : Finset V) (C : Finset E) (edge : E → Finset V) (m : ℕ),
        (∀ g : E, g ∈ C → (X ∩ edge g).card ≤ m) →
        (∑ j : Fin X.card,
          (C.filter (fun g => ((Finset.equivFin X).symm j).1 ∈ edge g)).card)
          ≤ C.card * m := by
-- BODY
  classical
  intro V E _ _ X C edge m hbound
  let xOf : Fin X.card → V := fun j => ((Finset.equivFin X).symm j).1
  let P : Finset (E × Fin X.card) :=
    ((C.product Finset.univ).filter (fun p : E × Fin X.card =>
      p.1 ∈ C ∧ xOf p.2 ∈ edge p.1))
  have hcol :
      (∑ j : Fin X.card,
          (C.filter (fun g => xOf j ∈ edge g)).card) = P.card := by
    calc
      (∑ j : Fin X.card, (C.filter (fun g => xOf j ∈ edge g)).card)
          = ∑ j : Fin X.card, ((P.filter (fun p => p.2 = j)).card) := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.card_bij
              (fun g _hg => (g, j))
              (by
                intro g hg
                have hg' : g ∈ C ∧ xOf j ∈ edge g := by
                  simpa using hg
                simp [P, hg'.1, hg'.2])
              (by
                intro g₁ _ g₂ _ hpair
                exact Prod.ext_iff.mp hpair |>.1)
              (by
                intro p hp
                have hp' : p ∈ P ∧ p.2 = j := by
                  simpa using hp
                refine ⟨p.1, ?_, ?_⟩
                · have hmem : p.1 ∈ C ∧ xOf p.2 ∈ edge p.1 := by
                    simpa [P] using hp'.1
                  simpa [hp'.2] using hmem
                · ext <;> simp [hp'.2])
      _ = P.card := by
        have hmaps : (P : Set (E × Fin X.card)).MapsTo Prod.snd
            ((Finset.univ : Finset (Fin X.card)) : Set (Fin X.card)) := by
          intro p hp
          simp
        rw [(Finset.card_eq_sum_card_fiberwise (s := P) (t := Finset.univ)
          (f := Prod.snd) hmaps).symm]
  have hrow :
      P.card ≤ C.card * m := by
    have hmaps : (P : Set (E × Fin X.card)).MapsTo Prod.fst C := by
      intro p hp
      have hp' : p.1 ∈ C ∧ xOf p.2 ∈ edge p.1 := by
        simpa [P] using hp
      exact hp'.1
    calc
      P.card
          = ∑ g ∈ C, ((P.filter (fun p => p.1 = g)).card) := by
            rw [Finset.card_eq_sum_card_fiberwise (s := P) (t := C)
              (f := Prod.fst) hmaps]
      _ ≤ ∑ _g ∈ C, m := by
            apply Finset.sum_le_sum
            intro g hgC
            let Y : Finset V := X ∩ edge g
            have hfiber_le : (P.filter (fun p => p.1 = g)).card ≤ Y.card := by
              refine Finset.card_le_card_of_injOn
                (fun p : E × Fin X.card => xOf p.2) ?_ ?_
              · intro p hp
                have hp' : p ∈ P ∧ p.1 = g := by
                  simpa using hp
                have hmem : p.1 ∈ C ∧ xOf p.2 ∈ edge p.1 := by
                  simpa [P] using hp'.1
                have hx : xOf p.2 ∈ X := ((Finset.equivFin X).symm p.2).2
                simpa [Y, hp'.2] using Finset.mem_inter.mpr ⟨hx, hmem.2⟩
              · intro p hp q hq heq
                have hp' : p ∈ P ∧ p.1 = g := by
                  simpa using hp
                have hq' : q ∈ P ∧ q.1 = g := by
                  simpa using hq
                have hfin : p.2 = q.2 := by
                  have hsub :
                      (Finset.equivFin X).symm p.2 =
                        (Finset.equivFin X).symm q.2 := by
                    ext
                    exact heq
                  exact (EquivLike.injective (Finset.equivFin X).symm) hsub
                ext <;> simp [hp'.2, hq'.2, hfin]
            exact hfiber_le.trans (hbound g hgC)
      _ = C.card * m := by simp
  exact hcol.trans_le hrow
