import Tablet.SamplingSplitOutsideBlockerPairedCandidateEvent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPairedCandidateEventMeasurable]
theorem SamplingSplitOutsideBlockerPairedCandidateEventMeasurable
    {V V' : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V']
    (G : SimpleGraph V) (φ : V → V') (r : V) (X : Finset V)
    {n : ℕ} (zAt : Fin n → V) (B : Fin n → Finset V)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (P T : Finset (Fin n)) (x : {x : V // x ∈ X}) :
    @MeasurableSet ((Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
      (MeasurableSpace.prod (MeasurableSpace.prod ⊤ inferInstance)
        (MeasurableSpace.prod ⊤ inferInstance))
      (SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β P T x) := by
-- BODY
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  let State := (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ))
  have ha (v : V) : Measurable (fun ζ : State => v ∈ ζ.1.1) :=
    (measurable_of_finite (fun A : Finset V => v ∈ A)).comp
      (measurable_fst.comp measurable_fst)
  have ha' (v : V') : Measurable (fun ζ : State => v ∈ ζ.2.1) :=
    (measurable_of_finite (fun A : Finset V' => v ∈ A)).comp
      (measurable_fst.comp measurable_snd)
  have hp (v : V) : Measurable (fun ζ : State => ζ.1.2 v) :=
    (measurable_pi_apply v).comp (measurable_snd.comp measurable_fst)
  have hp' (v : V') : Measurable (fun ζ : State => ζ.2.2 v) :=
    (measurable_pi_apply v).comp (measurable_snd.comp measurable_snd)
  have hlt (v y : V) : Measurable (fun ζ : State => ζ.1.2 v < ζ.1.2 y) :=
    measurableSet_setOf.mp (measurableSet_lt (hp v) (hp y))
  have hlt' (v y : V') : Measurable (fun ζ : State => ζ.2.2 v < ζ.2.2 y) :=
    measurableSet_setOf.mp (measurableSet_lt (hp' v) (hp' y))
  have hu (v : V) : Measurable (fun ζ : State => ζ.1.2 v ∈ Set.Icc (0 : ℝ) 1) :=
    measurableSet_setOf.mp (measurableSet_Icc.preimage (hp v))
  have hu' (v : V') : Measurable (fun ζ : State => ζ.2.2 v ∈ Set.Icc (0 : ℝ) 1) :=
    measurableSet_setOf.mp (measurableSet_Icc.preimage (hp' v))
  unfold SamplingSplitOutsideBlockerPairedCandidateEvent
  apply Measurable.setOf
  exact (ha x.1).and ((ha' (φ x.1)).and
    ((Measurable.forall fun y => measurable_const.imp
      ((ha y).imp (measurable_const.imp (hlt y x.1)))).and
    ((Measurable.forall fun y => measurable_const.imp
      ((ha' (φ y)).imp (measurable_const.imp (hlt' (φ y) (φ x.1))))).and
    ((Measurable.forall fun i => measurable_const.imp (measurable_const.imp
      (Measurable.forall fun hz =>
        ((ha' (β ⟨x, ⟨zAt i, hz⟩⟩)).and
          ((hlt' (φ x.1) (β ⟨x, ⟨zAt i, hz⟩⟩)).and
            (hu' (β ⟨x, ⟨zAt i, hz⟩⟩)))).not))).and
    (Measurable.forall fun i => measurable_const.imp (measurable_const.imp
      ((ha (zAt i)).and ((hlt x.1 (zAt i)).and (hu (zAt i)))).not))))))
