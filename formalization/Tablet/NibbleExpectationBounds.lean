import Tablet.NibbleProductSamplingLaw
import Tablet.NibbleResidualDegree
import Tablet.NibbleDeletedColors
import Tablet.NibbleInducedBParameterComparison
import Tablet.IndependentSetSamplingBound
import Tablet.MaxDegreeAtMost
import Tablet.FiniteIndicatorCountExpectation
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory BigOperators

-- [TABLET NODE: NibbleExpectationBounds]
theorem NibbleExpectationBounds (eps : ℝ) (heps : 0 < eps) :
    ∃ Delta0 gamma0 : ℕ, ∀ Delta D ell : ℕ, ∀ gamma : ℝ,
      Delta0 ≤ Delta → (gamma0 : ℝ) ≤ gamma →
      0 < gamma → gamma ≤ Delta →
      ∀ {V E K : Type*} [Fintype E] [Fintype K]
        [DecidableEq V] [DecidableEq E] [DecidableEq K],
      ∀ (H : MultiHypergraph V E) (M : E → Finset K),
      MaxDegreeAtMost H D → (∀ e, (M e).card = ell) →
      (∀ e, ((LineGraphOfHypergraph H).neighborSet e).ncard ≤ Delta) →
      ∀ b : ℝ,
      (∀ e, @LocalBParameter E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel _) Delta e ≤ b) →
      ∀ Q : NibbleCompletionData H M Delta,
      let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a)) (gamma / Delta)
      (∀ x, (∫ ω, (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) ∂ν) ≤
        D * (1 - (1 - Real.exp (-gamma)) / Delta + 2 / (Delta : ℝ)^2)^ell) ∧
      (∀ e, (∫ ω, ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) ∂ν) ≤
        (b + eps) * ell) := by
-- BODY
  classical
  obtain ⟨Delta0, gamma0, hsampling⟩ := IndependentSetSamplingBound eps heps
  refine ⟨Delta0, gamma0, ?_⟩
  intro Delta D ell gamma hDelta hgamma hg hgD V E K _ _ _ _ _ H M hdeg hlist
    hline b hb Q
  dsimp only
  let Ω := (Sigma fun a => Fin (Q.size a)) → ℝ × ℝ
  let ν : Measure Ω := NibbleProductMeasure (gamma / Delta)
  obtain ⟨hprob, hmarginal, hcompleted, hselected, hind, hcolors, hcoordinates⟩ :=
    NibbleProductSamplingLaw Q gamma hg hgD
  letI : IsProbabilityMeasure ν := hprob
  have hDpos : (0 : ℝ) < Delta := lt_of_lt_of_le hg hgD
  have hDone : (1 : ℝ) ≤ Delta := by
    have hn : 0 < Delta := by exact_mod_cast hDpos
    exact_mod_cast hn
  let q : ℝ := 1 - (1 - Real.exp (-gamma)) / Delta + 2 / (Delta : ℝ)^2
  have hq : 0 ≤ q := by
    have hfrac : (1 - Real.exp (-gamma)) / Delta ≤ 1 :=
      (div_le_one hDpos).mpr (by linarith [Real.exp_pos (-gamma)])
    dsimp [q]
    exact add_nonneg (sub_nonneg.mpr hfrac) (by positivity)
  have hunselected (e : E) : MeasurableSet {ω : Ω | ∀ a, e ∉ NibbleSelectedEdges Q ω a} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => (hselected a e).compl
  have hdeleted (e : E) (a : K) : MeasurableSet
      {ω : Ω | ∃ f ∈ NibbleSelectedEdges Q ω a, (LineGraphOfHypergraph H).Adj e f} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun f =>
      (hselected a f).inter (MeasurableSet.const _)
  have marginal_event (a : K) (μ : Finset (Fin (Q.size a)) → ℝ)
      (hn : ∀ S, 0 ≤ μ S)
      (hm : ∀ S, ν {ω | NibbleCompletedSelection Q ω a = S} = ENNReal.ofReal (μ S))
      (P : Finset (Fin (Q.size a)) → Prop) :
      ν.real {ω | P (NibbleCompletedSelection Q ω a)} = ∑ S, if P S then μ S else 0 := by
    let A (S : Finset (Fin (Q.size a))) : Set Ω :=
      if P S then {ω | NibbleCompletedSelection Q ω a = S} else ∅
    have he : {ω | P (NibbleCompletedSelection Q ω a)} = ⋃ S, A S := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨NibbleCompletedSelection Q ω a, ?_⟩
        rw [show A (NibbleCompletedSelection Q ω a) =
          {w | NibbleCompletedSelection Q w a = NibbleCompletedSelection Q ω a} from if_pos h]
        rfl
      · rintro ⟨S, hS⟩
        by_cases hp : P S
        · simp only [A, if_pos hp] at hS
          change NibbleCompletedSelection Q ω a = S at hS
          exact hS.symm ▸ hp
        · simp [A, hp] at hS
    have hAm (S) : MeasurableSet (A S) := by
      dsimp [A]
      split_ifs
      · exact hcompleted a S
      · exact MeasurableSet.empty
    have hAd : Pairwise (fun S T => Disjoint (A S) (A T)) := by
      intro S T hST
      by_cases hs : P S <;> by_cases ht : P T
      · simp only [A, if_pos hs, if_pos ht]
        exact Set.disjoint_left.mpr (fun ω hS hT => hST (hS.symm.trans hT))
      all_goals simp [A, hs, ht]
    rw [he, measureReal_iUnion_fintype hAd hAm]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hp : P S
    · simp [A, hp, measureReal_def, hm, ENNReal.toReal_ofReal (hn S)]
    · simp [A, hp]
  have hsingle (e : E) (a : K) (ha : a ∈ M e) :
      ν.real {ω : Ω | e ∉ NibbleSelectedEdges Q ω a} ≤ q := by
    obtain ⟨μ, hμ, hpush⟩ := hmarginal a
    letI : DecidableRel (Q.graph a).Adj := Classical.decRel _
    have hreg (v) : (Q.graph a).degree v = Delta := by
      calc
        _ = ((Q.graph a).neighborSet v).ncard := by
          rw [Set.ncard_eq_toFinset_card']
          rfl
        _ = Delta := Q.regular a v
    have hbound := (hsampling Delta gamma hDelta hgamma (Q.graph a) hreg μ hμ).1
      (Q.embed a ⟨e, ha⟩)
    have he : {ω : Ω | e ∈ NibbleSelectedEdges Q ω a} =
        {ω | Q.embed a ⟨e, ha⟩ ∈ NibbleCompletedSelection Q ω a} := by
      ext ω
      change (e ∈ NibbleSelectedEdges Q ω a) ↔
        Q.embed a ⟨e, ha⟩ ∈ NibbleCompletedSelection Q ω a
      simp [NibbleSelectedEdges, ha]
    have hm := marginal_event a μ hμ.2.1.1 hpush
      (fun S => Q.embed a ⟨e, ha⟩ ∈ S)
    rw [← he] at hm
    have hc := measureReal_compl (μ := ν) (hselected a e)
    change ν.real {ω | e ∉ NibbleSelectedEdges Q ω a} = _ at hc
    rw [hc, probReal_univ, hm]
    have hl := (abs_le.mp hbound).1
    change -(2 / (Delta : ℝ)^2) ≤
      (∑ S, if Q.embed a ⟨e, ha⟩ ∈ S then μ S else 0) -
        (1 - Real.exp (-gamma)) / Delta at hl
    dsimp only [q]
    have halg (x y z : ℝ) (h : -z ≤ x - y) : 1 - x ≤ 1 - y + z := by linarith
    convert halg _ _ _ hl using 1
    congr 1
    apply Finset.sum_congr rfl
    intro S _
    by_cases hs : Q.embed a ⟨e, ha⟩ ∈ S <;> simp [hs]
  have hsurvival (e : E) :
      ν.real {ω : Ω | ∀ a, e ∉ NibbleSelectedEdges Q ω a} ≤ q ^ ell := by
    let A (a : K) : Set (Fin (Q.size a) → ℝ × ℝ) := {w |
      ∃ h : a ∈ M e, (w (Q.embed a ⟨e, h⟩)).1 = 1 ∧
        ∀ u, (w u).1 = 1 → (Q.graph a).Adj (Q.embed a ⟨e, h⟩) u →
          (w u).2 < (w (Q.embed a ⟨e, h⟩)).2}
    have hA (a) : MeasurableSet (A a) := by
      simp only [A, Set.setOf_exists]
      apply MeasurableSet.iUnion
      intro h
      apply MeasurableSet.inter
      · exact measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
          measurable_const
      · change MeasurableSet {w : Fin (Q.size a) → ℝ × ℝ |
          ∀ u, (w u).1 = 1 → (Q.graph a).Adj (Q.embed a ⟨e, h⟩) u →
            (w u).2 < (w (Q.embed a ⟨e, h⟩)).2}
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun u => MeasurableSet.imp
          (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _)) measurable_const)
          (MeasurableSet.imp (MeasurableSet.const _)
            (measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
              (measurable_snd.comp (measurable_pi_apply _))))
    have he (a) : {ω : Ω | (fun v => ω ⟨a, v⟩) ∈ (A a)ᶜ} =
        {ω | e ∉ NibbleSelectedEdges Q ω a} := by
      ext ω
      change ((fun v => ω ⟨a, v⟩) ∈ (A a)ᶜ) ↔ e ∉ NibbleSelectedEdges Q ω a
      simp [A, NibbleSelectedEdges, NibbleCompletedSelection]
    have hall : {ω : Ω | ∀ a, (fun v => ω ⟨a, v⟩) ∈ (A a)ᶜ} =
        {ω | ∀ a, e ∉ NibbleSelectedEdges Q ω a} := by
      simp only [Set.setOf_forall, he]
    have hp := hcolors (fun a => (A a)ᶜ) (fun a => (hA a).compl)
    rw [hall] at hp
    have hp' : ν {ω | ∀ a, e ∉ NibbleSelectedEdges Q ω a} =
        ∏ a, ν {ω | e ∉ NibbleSelectedEdges Q ω a} :=
      hp.trans (Finset.prod_congr rfl fun a _ => congrArg ν (he a))
    have hreal := congrArg ENNReal.toReal hp'
    simp only [ENNReal.toReal_prod] at hreal
    change ν.real {ω | ∀ a, e ∉ NibbleSelectedEdges Q ω a} =
      ∏ a, ν.real {ω | e ∉ NibbleSelectedEdges Q ω a} at hreal
    rw [hreal]
    calc
      _ ≤ ∏ a : K, if a ∈ M e then q else 1 := by
        apply Finset.prod_le_prod
        · intro a _
          exact measureReal_nonneg
        · intro a _
          by_cases ha : a ∈ M e
          · simpa [ha] using hsingle e a ha
          · have hempty : {ω : Ω | e ∉ NibbleSelectedEdges Q ω a} = Set.univ := by
              ext ω
              simp [NibbleSelectedEdges, ha]
            simp [ha, hempty]
      _ = q ^ ell := by
        rw [Finset.prod_ite]
        simp [hlist]
  have hdeletion (e : E) (a : K) (ha : a ∈ M e) :
      ν.real {ω : Ω | ∃ f ∈ NibbleSelectedEdges Q ω a,
        (LineGraphOfHypergraph H).Adj e f} ≤ b + eps := by
    obtain ⟨μ, hμ, hpush⟩ := hmarginal a
    letI : DecidableRel (Q.graph a).Adj := Classical.decRel _
    let oldNeighbors : Finset {f : E // a ∈ M f} :=
      Finset.univ.filter fun f => (LineGraphOfHypergraph H).Adj e f.val
    let X : Finset (Fin (Q.size a)) := oldNeighbors.image (Q.embed a)
    let r := Q.embed a ⟨e, ha⟩
    have hX (v) (hv : v ∈ X) : (Q.graph a).Adj r v := by
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
      exact (Q.induced a ⟨e, ha⟩ f).2 (Finset.mem_filter.mp hf).2
    have hevent : {ω : Ω | ∃ f ∈ NibbleSelectedEdges Q ω a,
        (LineGraphOfHypergraph H).Adj e f} =
        {ω | (NibbleCompletedSelection Q ω a ∩ X).Nonempty} := by
      ext ω
      change (∃ f ∈ NibbleSelectedEdges Q ω a, (LineGraphOfHypergraph H).Adj e f) ↔
        (NibbleCompletedSelection Q ω a ∩ X).Nonempty
      constructor
      · rintro ⟨f, hf, hadj⟩
        obtain ⟨haf, hsel⟩ := (Finset.mem_filter.mp hf).2
        refine ⟨Q.embed a ⟨f, haf⟩, Finset.mem_inter.mpr ⟨hsel, ?_⟩⟩
        exact Finset.mem_image.mpr ⟨⟨f, haf⟩, by simp [oldNeighbors, hadj], rfl⟩
      · rintro ⟨v, hv⟩
        obtain ⟨hsel, hXv⟩ := Finset.mem_inter.mp hv
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hXv
        refine ⟨f.val, ?_, (Finset.mem_filter.mp hf).2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f.property, hsel⟩⟩
    rw [hevent, marginal_event a μ hμ.2.1.1 hpush (fun S => (S ∩ X).Nonempty)]
    have hreg (v) : (Q.graph a).degree v = Delta := by
      calc
        _ = ((Q.graph a).neighborSet v).ncard := by
          rw [Set.ncard_eq_toFinset_card']
          rfl
        _ = Delta := Q.regular a v
    have hbound := (hsampling Delta gamma hDelta hgamma (Q.graph a) hreg μ hμ).2 r X hX
    let s : Set (Fin (Q.size a)) := {v | v ∈ X ∨ v = r}
    letI : Fintype s := Fintype.ofFinite s
    letI : DecidableEq s := Classical.decEq s
    letI : DecidableRel ((Q.graph a).induce s).Adj := Classical.decRel _
    have hparameter : LocalBParameter ((Q.graph a).induce s) Delta
        (⟨r, Or.inr rfl⟩ : s) ≤ b := by
      let t : Finset E := Finset.univ.filter fun f =>
        a ∈ M f ∧ (f = e ∨ (LineGraphOfHypergraph H).Adj e f)
      let G := (LineGraphOfHypergraph H).induce (t : Set E)
      letI : DecidableRel G.Adj := Classical.decRel _
      have ht (f : t) : a ∈ M f.val ∧
          (f.val = e ∨ (LineGraphOfHypergraph H).Adj e f.val) :=
        (Finset.mem_filter.mp f.property).2
      let root : t := ⟨e, by simp [t, ha]⟩
      let j : t → s := fun f => ⟨Q.embed a ⟨f.val, (ht f).1⟩, by
        rcases (ht f).2 with hf | hf
        · right
          apply congrArg (Q.embed a)
          exact Subtype.ext hf
        · left
          exact Finset.mem_image.mpr ⟨⟨f.val, (ht f).1⟩,
            by simp [oldNeighbors, hf], rfl⟩⟩
      have hjinj : Function.Injective j := by
        intro u v huv
        have heq := Q.injective a (congrArg Subtype.val huv)
        exact Subtype.ext (congrArg (fun z : {f : E // a ∈ M f} => z.val) heq)
      have hjsurj : Function.Surjective j := by
        intro v
        rcases v.property with hv | hv
        · obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hv
          have hadj := (Finset.mem_filter.mp hf).2
          refine ⟨⟨f.val, by simp [t, f.property, hadj]⟩, ?_⟩
          exact Subtype.ext heq
        · refine ⟨root, ?_⟩
          exact Subtype.ext hv.symm
      let φ : G ≃g (Q.graph a).induce s :=
        { Equiv.ofBijective j ⟨hjinj, hjsurj⟩ with
          map_rel_iff' := by
            intro u v
            exact Q.induced a ⟨u.val, (ht u).1⟩ ⟨v.val, (ht v).1⟩ }
      have hiso := LocalBParameterNeighborhoodEmbeddingTransport G
        ((Q.graph a).induce s) Delta root (φ root) ⟨φ, φ.injective⟩
        (by
          intro x hx
          simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
          exact φ.map_rel_iff.mpr hx)
        (by
          intro y hy
          refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
          simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
          exact φ.map_rel_iff.mp (by simpa using hy))
        (by
          intro x hx y hy
          exact φ.map_rel_iff.symm)
      have hroot : φ root = (⟨r, Or.inr rfl⟩ : s) := by rfl
      rw [hroot] at hiso
      rw [← hiso]
      have hd : (LineGraphOfHypergraph H).degree e ≤ Delta := by
        have hh := hline e
        rw [Set.ncard_eq_toFinset_card'] at hh
        exact hh
      have hpositive : 0 < Delta := by exact_mod_cast hDpos
      exact (NibbleInducedBParameterComparison (LineGraphOfHypergraph H) Delta
        hpositive t root hd).trans (hb e)
    have hsum : (∑ S : Finset (Fin (Q.size a)),
        if (S ∩ X).Nonempty then μ S else 0) ≤
        LocalBParameter ((Q.graph a).induce s) Delta (⟨r, Or.inr rfl⟩ : s) + eps := by
      convert hbound using 1
    have hfinal := hsum.trans (add_le_add hparameter (le_refl eps))
    convert hfinal using 1
    apply Finset.sum_congr rfl
    intro S _
    by_cases hs : (S ∩ X).Nonempty <;> simp [hs]
  constructor
  · intro x
    let incident := Finset.univ.filter fun e => x ∈ H.edge e
    have he (ω : Ω) : NibbleResidualDegree H (NibbleSelectedEdges Q ω) x =
        (incident.filter fun e => ∀ a, e ∉ NibbleSelectedEdges Q ω a).card := by
      unfold NibbleResidualDegree
      congr 1
      ext e
      simp [incident]
    simp_rw [he]
    rw [(FiniteIndicatorCountExpectation ν incident
      (fun e ω => ∀ a, e ∉ NibbleSelectedEdges Q ω a) (fun e _ => hunselected e)).2]
    calc
      _ ≤ ∑ _e ∈ incident, q ^ ell := Finset.sum_le_sum fun e _ => hsurvival e
      _ = (incident.card : ℝ) * q ^ ell := by simp
      _ ≤ D * q ^ ell := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hdeg x) (pow_nonneg hq _)
  · intro e
    change (∫ ω, (((M e).filter fun a => ∃ f ∈ NibbleSelectedEdges Q ω a,
      (LineGraphOfHypergraph H).Adj e f).card : ℝ) ∂ν) ≤ _
    rw [(FiniteIndicatorCountExpectation ν (M e)
      (fun a ω => ∃ f ∈ NibbleSelectedEdges Q ω a, (LineGraphOfHypergraph H).Adj e f)
      (fun a _ => hdeleted e a)).2]
    calc
      _ ≤ ∑ _a ∈ M e, (b + eps) := Finset.sum_le_sum fun a ha => hdeletion e a ha
      _ = (b + eps) * ell := by simp [hlist, mul_comm, add_mul]
