import Tablet.SamplingSplitOutsideBlockerTargetEndpointEquivalence
import Tablet.SamplingPriorityPositiveUnitSupport
import Tablet.SamplingNonadjacentPairOrderedChamberDiagonalNull

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerEndpointBoundaryCellReduction]
theorem SamplingSplitOutsideBlockerEndpointBoundaryCellReduction
    {α W : Type u} [Fintype α] [DecidableEq α] [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ν : @MeasureTheory.Measure (Finset W × (W → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (Cand : Finset α) (embed : α → W)
    (localCoord : Finset W) {n : ℕ}
    (blocker : Fin n → α → W) (hasBlocker : Fin n → α → Prop)
    (cell : Set (Finset W × (W → ℝ)))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hν_atom : ∀ A : Finset W,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset W).card - A.card)))
    (hν_rect : ∀ A : Finset W, ∀ t : W → ℝ,
      (∀ v : W, t v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ v : W, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v : W, t v))
    (hcover : ∀ x : α, x ∈ Cand → ∀ y : W, G.Adj (embed x) y →
      y ∈ localCoord ∨ ∃ i : Fin n, hasBlocker i x ∧ y = blocker i x)
    (hblocker_adj : ∀ i : Fin n, ∀ x : α, x ∈ Cand → hasBlocker i x →
      G.Adj (embed x) (blocker i x))
    (hlocal_self : ∀ x : α, x ∈ Cand → embed x ∈ localCoord) :
    ν ({η : Finset W × (W → ℝ) |
          ((Finset.univ.filter fun z : W =>
            z ∈ η.1 ∧
              ∀ y : W, y ∈ η.1 → G.Adj z y → η.2 y < η.2 z) ∩
              Cand.image embed).Nonempty} ∩ cell) =
      ν ({η : Finset W × (W → ℝ) |
          ∃ x : α, ∃ hx : x ∈ Cand,
            embed x ∈ η.1 ∧
              (∀ y : W, y ∈ localCoord → y ∈ η.1 →
                G.Adj (embed x) y → η.2 y < η.2 (embed x)) ∧
              ∀ i : Fin n, hasBlocker i x →
                ¬ (blocker i x ∈ η.1 ∧
                  η.2 (embed x) < η.2 (blocker i x) ∧
                    η.2 (blocker i x) ∈ Set.Icc (0 : ℝ) 1)} ∩ cell) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset W × (W → ℝ)) :=
    MeasurableSpace.prod ⊤ inferInstance
  have hsupport := SamplingPriorityPositiveUnitSupport ν
    (fun A => by rw [hν_atom A]; exact ENNReal.ofReal_ne_top) hν_rect
  have hcube (A : Finset W) :
      ν {ω | ω.1 = A ∧ ∀ q : W, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A} := by
    apply measure_congr
    filter_upwards [hsupport] with ω hω
    exact propext ⟨And.left, fun hA =>
      ⟨hA, fun q _ => ⟨(hω q).1.le, (hω q).2⟩⟩⟩
  have hnotie (x : α) (i : Fin n) :
      ∀ᵐ ω ∂ν, x ∈ Cand → hasBlocker i x →
        embed x ∈ ω.1 → blocker i x ∈ ω.1 →
          ω.2 (embed x) ≠ ω.2 (blocker i x) := by
    by_cases hx : x ∈ Cand
    · by_cases hi : hasBlocker i x
      · have hne : embed x ≠ blocker i x :=
          (hblocker_adj i x hx hi).ne
        have hn := SamplingNonadjacentPairOrderedChamberDiagonalNull
          ν p (embed x) (blocker i x) hp0 hp1 hne hν_atom hcube hν_rect
        have hae := compl_mem_ae_iff.mpr hn
        filter_upwards [hsupport, hae] with ω hω hnω
        intro _ _ hxA hiA heq
        exact hnω ⟨hxA, hiA, fun q _ => ⟨(hω q).1.le, (hω q).2⟩, heq⟩
      · exact Filter.Eventually.of_forall fun _ _ h => (hi h).elim
    · exact Filter.Eventually.of_forall fun _ h => (hx h).elim
  have hall : ∀ᵐ ω ∂ν, ∀ x : α, ∀ i : Fin n,
      x ∈ Cand → hasBlocker i x →
        embed x ∈ ω.1 → blocker i x ∈ ω.1 →
          ω.2 (embed x) ≠ ω.2 (blocker i x) :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr (hnotie x)
  apply measure_congr
  filter_upwards [hsupport, hall] with η hη htie
  apply propext
  constructor
  · rintro ⟨⟨z, hz⟩, hcell⟩
    obtain ⟨hzsurv, hzimage⟩ := Finset.mem_inter.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzimage
    obtain ⟨_, hxA, hsurv⟩ := Finset.mem_filter.mp hzsurv
    refine ⟨⟨x, hx, hxA, fun y _ hy hadj => hsurv y hy hadj, ?_⟩, hcell⟩
    intro i hi hbad
    exact (hsurv (blocker i x) hbad.1 (hblocker_adj i x hx hi)).not_gt hbad.2.1
  · rintro ⟨⟨x, hx, hxA, hlocal, hblock⟩, hcell⟩
    refine ⟨⟨embed x, Finset.mem_inter.mpr ⟨?_, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩⟩,
      hcell⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hxA, ?_⟩
    intro y hy hadj
    rcases hcover x hx y hadj with hylocal | ⟨i, hi, rfl⟩
    · exact hlocal y hylocal hy hadj
    · have hnlt : ¬ η.2 (embed x) < η.2 (blocker i x) := by
        intro hlt
        exact hblock i hi ⟨hy, hlt, (hη (blocker i x)).1.le, (hη (blocker i x)).2⟩
      exact lt_of_le_of_ne (le_of_not_gt hnlt) (htie x i hx hi hxA hy).symm
