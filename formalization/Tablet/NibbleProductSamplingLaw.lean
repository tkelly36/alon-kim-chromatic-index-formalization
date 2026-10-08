import Tablet.NibbleProductMeasure
import Tablet.NibbleSelectedEdges
import Tablet.SamplingRegularGraphSamplingLawExists
import Tablet.SamplingActivationRectangleMeasureUniqueness
import Mathlib.Combinatorics.SimpleGraph.Clique

open MeasureTheory BigOperators

-- [TABLET NODE: NibbleProductSamplingLaw]
theorem NibbleProductSamplingLaw {V E K : Type*} [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq E] [DecidableEq K]
    {H : MultiHypergraph V E} {M : E → Finset K} {Delta : ℕ}
    (Q : NibbleCompletionData H M Delta) (gamma : ℝ)
    (hg : 0 < gamma) (hgD : gamma ≤ Delta) :
    let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a))
      (gamma / Delta)
    IsProbabilityMeasure ν ∧
    (∀ a, ∃ μ : Finset (Fin (Q.size a)) → ℝ,
      @RandomIndependentSetSampling _ _ _ (Q.graph a)
        (Classical.decRel _) Delta gamma μ ∧
      ∀ S, ν {ω | NibbleCompletedSelection Q ω a = S} = ENNReal.ofReal (μ S)) ∧
    (∀ a S, MeasurableSet {ω | NibbleCompletedSelection Q ω a = S}) ∧
    (∀ a e, MeasurableSet {ω | e ∈ NibbleSelectedEdges Q ω a}) ∧
    (∀ ω a, (LineGraphOfHypergraph H).IsIndepSet
      (NibbleSelectedEdges Q ω a : Set E)) ∧
    (∀ (F : (a : K) → Set (Fin (Q.size a) → ℝ × ℝ)),
      (∀ a, MeasurableSet (F a)) →
      ν {ω | ∀ a, (fun v => ω ⟨a, v⟩) ∈ F a} =
        ∏ a, ν {ω | (fun v => ω ⟨a, v⟩) ∈ F a}) ∧
    (∀ s : (Sigma fun a => Fin (Q.size a)) → Set (ℝ × ℝ),
      (∀ t, MeasurableSet (s t)) →
      ν {ω | ∀ t, ω t ∈ s t} =
        ∏ t, ((ENNReal.ofReal (gamma / Delta) • Measure.dirac (1 : ℝ) +
          ENNReal.ofReal (1 - gamma / Delta) • Measure.dirac (0 : ℝ)).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1))) (s t)) := by
-- BODY
  classical
  have hD : (0 : ℝ) < Delta := lt_of_lt_of_le hg hgD
  let p : ℝ := gamma / Delta
  have hp : 0 ≤ p := le_of_lt (div_pos hg hD)
  have hp1 : p ≤ 1 := (div_le_one hD).2 hgD
  let b : Measure ℝ := ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
  haveI : IsProbabilityMeasure b := ⟨by
    simp only [b, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp (sub_nonneg.mpr hp1)]
    simp⟩
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by
    simp⟩
  let κ := b.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
  haveI : IsProbabilityMeasure κ := inferInstance
  let c := MeasurableEquiv.piCurry (fun a (_ : Fin (Q.size a)) => ℝ × ℝ)
  let ρ (a : K) := Measure.pi (fun _ : Fin (Q.size a) => κ)
  have hc : MeasurePreserving c (Measure.pi (fun _ => κ)) (Measure.pi ρ) := by as_aux_lemma =>
    apply MeasurePreserving.symm c.symm
    refine ⟨c.symm.measurable, ?_⟩
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply c.symm.measurable (MeasurableSet.univ_pi hs)]
    have he : c.symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun a => Set.univ.pi (fun v => s ⟨a, v⟩)) := by
      ext ω
      simp [c, Set.mem_pi, Sigma.forall, Sigma.uncurry]
    rw [he, Measure.pi_pi]
    simp only [ρ, Measure.pi_pi]
    exact (Fintype.prod_sigma (fun t => κ (s t))).symm
  have hcolor (a : K) (F : Set (Fin (Q.size a) → ℝ × ℝ))
      (hF : MeasurableSet F) : (NibbleProductMeasure p)
      {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
        (fun v => ω ⟨a, v⟩) ∈ F} = ρ a F := by
    have heval : (Measure.pi ρ).map (Function.eval a) = ρ a := by
      simp [Measure.pi_map_eval, measure_univ]
    have h := hc.measure_preimage
      (hF.preimage (measurable_pi_apply a)).nullMeasurableSet
    rw [← Measure.map_apply (measurable_pi_apply a) hF, heval] at h
    exact h
  change IsProbabilityMeasure (Measure.pi (fun _ : Sigma fun a => Fin (Q.size a) => κ)) ∧ _
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    let W := Fin (Q.size a)
    letI : MeasurableSpace (Finset W) := ⊤
    let decode : (W → ℝ × ℝ) → Finset W × (W → ℝ) := fun ω =>
      (Finset.univ.filter (fun v => (ω v).1 = 1), fun v => (ω v).2)
    have hdecode : Measurable decode := by as_aux_lemma =>
      apply Measurable.prodMk
      · apply measurable_to_countable'
        intro A
        have he : {ω : W → ℝ × ℝ | (decode ω).1 = A} =
            ⋂ v, {ω | (ω v).1 = 1 ↔ v ∈ A} := by
          ext ω
          simp [decode, Finset.ext_iff]
        change MeasurableSet {ω | (decode ω).1 = A}
        rw [he]
        exact MeasurableSet.iInter fun v =>
          (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply v))
            measurable_const).iff (MeasurableSet.const _)
      · exact measurable_pi_lambda _ fun v =>
          measurable_snd.comp (measurable_pi_apply v)
    have hraw (A : Finset W) (s : W → Set ℝ) :
        ρ a {ω | (decode ω).1 = A ∧ ∀ v, (ω v).2 ∈ s v} =
          ENNReal.ofReal (p ^ A.card * (1 - p) ^ (Fintype.card W - A.card)) *
            ∏ v, (volume.restrict (Set.Icc (0 : ℝ) 1)) (s v) := by as_aux_lemma =>
      let t (v : W) : Set ℝ := if v ∈ A then {1} else {1}ᶜ
      have he : {ω : W → ℝ × ℝ | (decode ω).1 = A ∧ ∀ v, (ω v).2 ∈ s v} =
          Set.univ.pi (fun v => t v ×ˢ s v) := by
        ext ω
        simp only [decode, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ,
          true_and, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
          Set.mem_prod]
        rw [← forall_and]
        apply forall_congr'
        intro v
        by_cases hv : v ∈ A <;> simp [t, hv]
      have hb (v : W) : b (t v) =
          if v ∈ A then ENNReal.ofReal p else ENNReal.ofReal (1 - p) := by
        by_cases hv : v ∈ A <;> simp [b, t, hv]
      rw [he, Measure.pi_pi]
      simp only [κ, Measure.prod_prod, hb, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_ite]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
        ← Finset.mem_compl, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.card_compl]
      rw [ENNReal.ofReal_mul (pow_nonneg hp _), ENNReal.ofReal_pow hp,
        ENNReal.ofReal_pow (sub_nonneg.mpr hp1)]
    let η := (ρ a).map decode
    have ha (A : Finset W) : η {ω | ω.1 = A} =
        ENNReal.ofReal (p ^ A.card * (1 - p) ^ (Fintype.card W - A.card)) := by as_aux_lemma =>
      rw [Measure.map_apply hdecode (measurableSet_eq_fun measurable_fst measurable_const)]
      simpa only [Set.mem_univ, implies_true, and_true, measure_univ,
        Finset.prod_const_one, mul_one] using hraw A (fun _ => Set.univ)
    have hr (A : Finset W) (t : W → ℝ) (ht : ∀ v, t v ∈ Set.Icc (0 : ℝ) 1) :
        η {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
          η {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v) := by as_aux_lemma =>
      have hm : MeasurableSet {ω : Finset W × (W → ℝ) |
          ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} := by measurability
      rw [Measure.map_apply hdecode hm, ha]
      change ρ a {ω | (decode ω).1 = A ∧ ∀ v, (ω v).2 ∈ Set.Icc 0 (t v)} = _
      rw [hraw]
      congr 1
      have hv (v : W) : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 (t v)) =
          ENNReal.ofReal (t v) := by
        rw [Measure.restrict_apply measurableSet_Icc,
          Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl (ht v).2)]
        simp
      simp_rw [hv]
      exact (ENNReal.ofReal_prod_of_nonneg (fun v _ => (ht v).1)).symm
    letI := Classical.decRel (Q.graph a).Adj
    obtain ⟨μ, hμ⟩ := SamplingRegularGraphSamplingLawExists (Q.graph a) Delta gamma
      (fun v => by
        calc
          (Q.graph a).degree v = ((Q.graph a).neighborSet v).ncard := by
            rw [Set.ncard_eq_toFinset_card']
            rfl
          _ = Delta := Q.regular a v) hg hgD
    obtain ⟨η', hmass, ha', hcube', hr', hsingle', hpush, hind⟩ := hμ.2.2
    have heq : η = η' := by
      apply SamplingActivationRectangleMeasureUniqueness η η'
        (fun A => ENNReal.ofReal (p ^ A.card *
          (1 - p) ^ (Fintype.card W - A.card))) (fun _ => ENNReal.ofReal_ne_top)
      · exact ha
      · simpa only [Finset.card_univ] using ha'
      · exact hr
      · exact hr'
    refine ⟨μ, hμ, ?_⟩
    intro S
    let E : Set (Finset W × (W → ℝ)) := {ω |
      S = Finset.univ.filter (fun v => v ∈ ω.1 ∧
        ∀ u, u ∈ ω.1 → (Q.graph a).Adj v u → ω.2 u < ω.2 v)}
    have hE : MeasurableSet E := by
      simp only [E, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.setOf_forall]
      apply MeasurableSet.iInter
      intro v
      apply MeasurableSet.iff (MeasurableSet.const _)
      apply MeasurableSet.inter
      · exact (MeasurableSet.of_discrete : MeasurableSet {A : Finset W | v ∈ A}).preimage
          measurable_fst
      · change MeasurableSet {ω : Finset W × (W → ℝ) |
          ∀ u, u ∈ ω.1 → (Q.graph a).Adj v u → ω.2 u < ω.2 v}
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun u => MeasurableSet.imp
          ((MeasurableSet.of_discrete : MeasurableSet {A : Finset W | u ∈ A}).preimage
            measurable_fst)
          (MeasurableSet.imp (MeasurableSet.const _)
            (measurableSet_lt ((measurable_pi_apply u).comp measurable_snd)
              ((measurable_pi_apply v).comp measurable_snd)))
    have hpre : {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
        NibbleCompletedSelection Q ω a = S} =
        {ω | (fun v => ω ⟨a, v⟩) ∈ decode ⁻¹' E} := by
      ext ω
      simp only [E, decode, Set.mem_setOf_eq, Set.mem_preimage,
        NibbleCompletedSelection, Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    rw [hpre, hcolor a _ (hE.preimage hdecode)]
    rw [← Measure.map_apply hdecode hE]
    change η E = ENNReal.ofReal (μ S)
    rw [heq]
    convert (hpush S).symm using 1
    congr 1
    ext ω
    simp only [E, Set.mem_setOf_eq, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  · intro a S
    have hm (v : Fin (Q.size a)) : MeasurableSet
        {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
          v ∈ NibbleCompletedSelection Q ω a} := by
      simp only [NibbleCompletedSelection, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
        measurable_const).inter (by
          change MeasurableSet {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
            ∀ u, (ω ⟨a, u⟩).1 = 1 →
            (Q.graph a).Adj v u → (ω ⟨a, u⟩).2 < (ω ⟨a, v⟩).2}
          simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun u =>
          MeasurableSet.imp
            (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
              measurable_const)
            (MeasurableSet.imp (MeasurableSet.const _)
              (measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
                (measurable_snd.comp (measurable_pi_apply _)))))
    have heq : {ω | NibbleCompletedSelection Q ω a = S} =
        ⋂ v, {ω | v ∈ NibbleCompletedSelection Q ω a ↔ v ∈ S} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
    rw [heq]
    exact MeasurableSet.iInter fun v => (hm v).iff (MeasurableSet.const _)
  · intro a e
    have hm (v : Fin (Q.size a)) : MeasurableSet
        {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
          v ∈ NibbleCompletedSelection Q ω a} := by
      simp only [NibbleCompletedSelection, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
        measurable_const).inter (by
          change MeasurableSet {ω : (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ |
            ∀ u, (ω ⟨a, u⟩).1 = 1 →
            (Q.graph a).Adj v u → (ω ⟨a, u⟩).2 < (ω ⟨a, v⟩).2}
          simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun u =>
          MeasurableSet.imp
            (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
              measurable_const)
            (MeasurableSet.imp (MeasurableSet.const _)
              (measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
                (measurable_snd.comp (measurable_pi_apply _)))))
    simp only [NibbleSelectedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun h => hm (Q.embed a ⟨e, h⟩)
  · intro ω a
    rw [SimpleGraph.isIndepSet_iff]
    intro e he f hf hef hadj
    simp only [Finset.mem_coe, NibbleSelectedEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at he hf
    obtain ⟨he, hve⟩ := he
    obtain ⟨hf, hvf⟩ := hf
    simp only [NibbleCompletedSelection, Finset.mem_filter, Finset.mem_univ,
      true_and] at hve hvf
    have h := (Q.induced a ⟨e, he⟩ ⟨f, hf⟩).2 hadj
    exact (lt_asymm (hve.2 _ hvf.1 h) (hvf.2 _ hve.1 h.symm))
  · intro F hF
    have htotal := hc.measure_preimage (MeasurableSet.univ_pi hF).nullMeasurableSet
    rw [Measure.pi_pi] at htotal
    calc
      _ = ∏ a, ρ a (F a) := by
        simpa only [Set.pi, Set.mem_univ, forall_true_left, Set.preimage,
          c, MeasurableEquiv.coe_piCurry, Sigma.curry] using htotal
      _ = _ := Finset.prod_congr rfl (fun a _ => (hcolor a (F a) (hF a)).symm)
  · intro s hs
    simpa only [Set.pi, Set.mem_univ, forall_true_left] using
      Measure.pi_pi (fun _ => κ) s
