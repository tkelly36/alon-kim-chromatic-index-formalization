import Tablet.NibbleProductSamplingLaw
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

-- [TABLET NODE: NibbleSelectedSetProductLaw]
theorem NibbleSelectedSetProductLaw {V E K : Type*} [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq E] [DecidableEq K]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]
    {H : MultiHypergraph V E} {M : E → Finset K} {Delta : ℕ}
    (Q : NibbleCompletionData H M Delta) (gamma : ℝ)
    (hg : 0 < gamma) (hgD : gamma ≤ Delta) :
    let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a)) (gamma / Delta)
    (∀ a, Measurable (fun ω => NibbleSelectedEdges Q ω a)) ∧
    iIndepFun (fun a ω => NibbleSelectedEdges Q ω a) ν ∧
    ν.map (fun ω a => NibbleSelectedEdges Q ω a) =
      Measure.pi (fun a => ν.map (fun ω => NibbleSelectedEdges Q ω a)) := by
-- BODY
  classical
  let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a)) (gamma / Delta)
  obtain ⟨hprob, _, _, hmem, _, hrect, _⟩ := NibbleProductSamplingLaw Q gamma hg hgD
  letI : IsProbabilityMeasure ν := hprob
  have hmeas (a : K) : Measurable (fun ω => NibbleSelectedEdges Q ω a) := by
    apply measurable_to_countable'
    intro S
    have he : {ω | NibbleSelectedEdges Q ω a = S} =
        ⋂ e, {ω | e ∈ NibbleSelectedEdges Q ω a ↔ e ∈ S} := by
      ext ω
      simp [Finset.ext_iff]
    change MeasurableSet {ω | NibbleSelectedEdges Q ω a = S}
    rw [he]
    exact MeasurableSet.iInter fun e => (hmem a e).iff (MeasurableSet.const _)
  let lift (a : K) (η : Fin (Q.size a) → ℝ × ℝ)
      (t : Sigma fun a => Fin (Q.size a)) : ℝ × ℝ :=
    Function.update (fun a (_ : Fin (Q.size a)) => (0, 0)) a η t.1 t.2
  have hlift (a : K) : Measurable (lift a) := by
    apply measurable_pi_lambda
    intro t
    by_cases h : t.1 = a
    · subst a
      simpa [lift] using (measurable_pi_apply t.2)
    · simpa [lift, Function.update_of_ne h] using
        (measurable_const : Measurable (fun _ : (Fin (Q.size a) → ℝ × ℝ) => ((0, 0) : ℝ × ℝ)))
  have hlocal (a : K) (ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ) :
      NibbleSelectedEdges Q (lift a (fun v => ω ⟨a, v⟩)) a =
        NibbleSelectedEdges Q ω a := by
    simp [NibbleSelectedEdges, NibbleCompletedSelection, lift]
  have hmap : ν.map (fun ω a => NibbleSelectedEdges Q ω a) =
      Measure.pi (fun a => ν.map (fun ω => NibbleSelectedEdges Q ω a)) := by
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (measurable_pi_lambda _ hmeas) (MeasurableSet.univ_pi hs)]
    let F (a : K) := (fun η => NibbleSelectedEdges Q (lift a η) a) ⁻¹' s a
    have hF (a : K) : MeasurableSet (F a) := (hs a).preimage ((hmeas a).comp (hlift a))
    have he : (fun ω a => NibbleSelectedEdges Q ω a) ⁻¹' Set.univ.pi s =
        {ω | ∀ a, (fun v => ω ⟨a, v⟩) ∈ F a} := by
      ext ω
      simp [F, hlocal, Set.mem_pi]
    rw [he, hrect F hF]
    apply Finset.prod_congr rfl
    intro a _
    rw [Measure.map_apply (hmeas a) (hs a)]
    congr 1
    ext ω
    simp [F, hlocal]
  exact ⟨hmeas, (iIndepFun_iff_map_fun_eq_pi_map (fun a => (hmeas a).aemeasurable)).2 hmap,
    hmap⟩
