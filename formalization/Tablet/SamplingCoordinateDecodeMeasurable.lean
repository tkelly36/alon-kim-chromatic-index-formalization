import Tablet.SamplingSplitOutsideBlockerProductDecode
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

-- [TABLET NODE: SamplingCoordinateDecodeMeasurable]
theorem SamplingCoordinateDecodeMeasurable
    {V T : Type*} [Fintype V] [DecidableEq V] (s : V → T) :
    @Measurable (T → ℝ × ℝ) (Finset V × (V → ℝ))
      inferInstance (MeasurableSpace.prod ⊤ inferInstance)
      (fun q => (Finset.univ.filter (fun v => (q (s v)).1 = 1),
        fun v => (q (s v)).2)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  have ha : Measurable (fun q : T → ℝ × ℝ =>
      Finset.univ.filter (fun v => (q (s v)).1 = 1)) := by
    apply measurable_to_countable'
    intro A
    have he : {q : T → ℝ × ℝ |
        Finset.univ.filter (fun v => (q (s v)).1 = 1) = A} =
        {q | ∀ v, ((q (s v)).1 = 1 ↔ v ∈ A)} := by
      ext q
      simp only [Set.mem_setOf_eq, Finset.ext_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
    change MeasurableSet {q : T → ℝ × ℝ |
      Finset.univ.filter (fun v => (q (s v)).1 = 1) = A}
    rw [he]
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro v
    have hm : Measurable (fun q : T → ℝ × ℝ => (q (s v)).1) :=
      (measurable_pi_apply (s v)).fst
    have heq := measurableSet_eq_fun hm (measurable_const (a := (1 : ℝ)))
    by_cases hv : v ∈ A
    · simpa only [hv, iff_true] using heq
    · simpa only [hv, iff_false] using heq.compl
  exact ha.prodMk (measurable_pi_lambda _ fun v =>
    measurable_snd.comp (measurable_pi_apply (s v)))
