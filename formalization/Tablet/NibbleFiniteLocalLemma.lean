import Tablet.NibbleProductMeasure
import Mathlib.Probability.Independence.Basic

open MeasureTheory

-- [TABLET NODE: NibbleFiniteLocalLemma]
theorem NibbleFiniteLocalLemma {T J : Type*} [Fintype T] [Fintype J]
    [DecidableEq T] [DecidableEq J] (p P : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hP : 0 ≤ P) (q : ℕ) (hq : 1 ≤ q)
    (hsmall : Real.exp 1 * P * (q + 1) ≤ 1)
    (B : J → Set (T → ℝ × ℝ)) (S : J → Finset T)
    (hmeas : ∀ j, MeasurableSet (B j))
    (hdet : ∀ j ω ω', (∀ t ∈ S j, ω t = ω' t) → (ω ∈ B j ↔ ω' ∈ B j))
    (hprob : ∀ j, NibbleProductMeasure p (B j) ≤ ENNReal.ofReal P)
    (hdep : ∀ j, ((Finset.univ : Finset J).filter
      (fun i => i ≠ j ∧ (S i ∩ S j).Nonempty)).card ≤ q) :
    0 < NibbleProductMeasure p {ω | ∀ j, ω ∉ B j} ∧
      ∃ ω, ∀ j, ω ∉ B j := by
-- BODY
  classical
  let b : Measure ℝ := ENNReal.ofReal p • Measure.dirac 1 +
    ENNReal.ofReal (1 - p) • Measure.dirac 0
  haveI : IsProbabilityMeasure b := ⟨by
    simp only [b, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp (sub_nonneg.mpr hp1)]
    simp⟩
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by
    simp⟩
  let κ := b.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
  let ν : Measure (T → ℝ × ℝ) := NibbleProductMeasure p
  have hν : ν = Measure.pi (fun _ : T => κ) := rfl
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hcylinder (s : Finset T) (E : Set (T → ℝ × ℝ))
      (hE : MeasurableSet E)
      (hd : ∀ ω ω', (∀ t ∈ s, ω t = ω' t) → (ω ∈ E ↔ ω' ∈ E)) :
      ∃ C : Set (s → ℝ × ℝ), MeasurableSet C ∧
        E = (fun ω (t : s) => ω t) ⁻¹' C := by
    let ext : (s → ℝ × ℝ) → T → ℝ × ℝ :=
      fun x t => if ht : t ∈ s then x ⟨t, ht⟩ else (0, 0)
    have hext : Measurable ext := by
      apply measurable_pi_lambda
      intro t
      by_cases ht : t ∈ s
      · simpa only [ext, dif_pos ht] using measurable_pi_apply (⟨t, ht⟩ : s)
      · simpa only [ext, dif_neg ht] using
          (measurable_const : Measurable (fun _ : s → ℝ × ℝ => ((0 : ℝ), (0 : ℝ))))
    refine ⟨ext ⁻¹' E, hE.preimage hext, ?_⟩
    ext ω
    apply hd
    intro t ht
    simp [ext, ht]
  have hindcoords : ProbabilityTheory.iIndepFun
      (fun t (ω : T → ℝ × ℝ) => ω t) ν := by
    rw [hν]
    exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  let avoid (K : Finset J) : Set (T → ℝ × ℝ) := {ω | ∀ j ∈ K, ω ∉ B j}
  have havoidmeas (K : Finset J) : MeasurableSet (avoid K) := by
    simpa only [avoid, Set.mem_iInter, Set.mem_compl_iff, Set.setOf_forall] using
      MeasurableSet.biInter (Set.to_countable (K : Set J)) (fun j _ => (hmeas j).compl)
  have hind (i : J) (K : Finset J)
      (hK : ∀ j ∈ K, Disjoint (S i) (S j)) :
      ν (B i ∩ avoid K) = ν (B i) * ν (avoid K) := by
    let U := K.biUnion S
    have hdis : Disjoint (S i) U := by
      apply Finset.disjoint_left.mpr
      intro t ht hu
      obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.mp hu
      exact Finset.disjoint_left.mp (hK j hj) ht htj
    obtain ⟨C, hC, hBC⟩ := hcylinder (S i) (B i) (hmeas i) (hdet i)
    obtain ⟨D, hD, hAD⟩ := hcylinder U (avoid K) (havoidmeas K) (by
      intro ω ω' heq
      apply forall₂_congr
      intro j hj
      exact not_congr (hdet j ω ω' (fun t ht =>
        heq t (Finset.mem_biUnion.mpr ⟨j, hj, ht⟩))))
    rw [hBC, hAD]
    exact (hindcoords.indepFun_finset (S i) U hdis
      (fun t => measurable_pi_apply t)).measure_inter_preimage_eq_mul C D hC hD
  let z : ℝ := 1 / ((q : ℝ) + 1)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hzlt : z < 1 := by dsimp [z]; exact (div_lt_one (by positivity)).2 (by linarith)
  have hbase : 0 < 1 - z := sub_pos.mpr hzlt
  have hexp : Real.exp (-1) ≤ (1 - z) ^ q := by
    apply (Real.le_log_iff_exp_le (pow_pos hbase q)).mp
    rw [Real.log_pow]
    have hlog := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos hbase) hqpos.le
    have heq : (q : ℝ) * (1 - (1 - z)⁻¹) = -1 := by
      dsimp [z]
      field_simp [ne_of_gt hqpos]
      ring
    linarith
  have hnum : P ≤ z * (1 - z) ^ q := by
    have hEP : Real.exp 1 * P ≤ z := by
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) + 1)).2 hsmall
    have hPexp : P ≤ z * Real.exp (-1) := by
      rw [Real.exp_neg]
      exact (le_mul_inv_iff₀ (Real.exp_pos 1)).2 (by nlinarith [hEP])
    exact hPexp.trans (mul_le_mul_of_nonneg_left hexp hzpos.le)
  have hPz : P ≤ z := hnum.trans (by
    exact mul_le_of_le_one_right hzpos.le (pow_le_one₀ hbase.le (by linarith)))
  have hprobR (i : J) : ν.real (B i) ≤ P := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hprob i)).trans_eq
      (ENNReal.toReal_ofReal hP)
  have hindR (i : J) (K : Finset J) (hK : ∀ j ∈ K, Disjoint (S i) (S j)) :
      ν.real (B i ∩ avoid K) = ν.real (B i) * ν.real (avoid K) := by
    simp only [measureReal_def, hind i K hK, ENNReal.toReal_mul]
  have hstep (i : J) (K : Finset J) :
      ν.real (avoid (insert i K)) = ν.real (avoid K) - ν.real (B i ∩ avoid K) := by
    have heq : avoid (insert i K) = avoid K \ B i := by
      ext ω
      simp only [avoid, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp,
        Set.mem_diff]
      tauto
    rw [heq]
    have hadd := measureReal_inter_add_diff (μ := ν) (s := avoid K) (hmeas i)
    rw [Set.inter_comm] at hadd
    linarith
  have hmain (K : Finset J) : 0 < ν.real (avoid K) ∧
      ∀ i ∉ K, ν.real (B i ∩ avoid K) ≤ z * ν.real (avoid K) := by
    induction K using Finset.strongInductionOn
    case _ K ih =>
      have hpos : 0 < ν.real (avoid K) := by
        by_cases hempty : K = ∅
        · subst K
          simp [avoid]
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hsub : K.erase i ⊂ K := Finset.erase_ssubset hi
        have hprev := ih (K.erase i) hsub
        have hbound := hprev.2 i (Finset.notMem_erase i K)
        have heq := hstep i (K.erase i)
        rw [Finset.insert_erase hi] at heq
        nlinarith [mul_pos hbase hprev.1]
      refine ⟨hpos, ?_⟩
      intro i hi
      let N := K.filter (fun j => ¬ Disjoint (S i) (S j))
      let R := K \ N
      have hRdis (j : J) (hj : j ∈ R) : Disjoint (S i) (S j) := by
        have hmem := Finset.mem_sdiff.mp hj
        by_contra hn
        exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1, hn⟩)
      by_cases hN : N = ∅
      · have hRK : R = K := by simp [R, hN]
        rw [← hRK, hindR i R hRdis]
        exact mul_le_mul_of_nonneg_right (hprobR i |>.trans hPz)
          (measureReal_nonneg)
      · have hNsub : N ⊆ K := Finset.filter_subset _ _
        have hRsub : R ⊆ K := Finset.sdiff_subset
        have hNR : N ∪ R = K := Finset.union_sdiff_of_subset hNsub
        have hchain (L : Finset J) (hL : L ⊆ N) :
            (1 - z) ^ L.card * ν.real (avoid R) ≤ ν.real (avoid (L ∪ R)) := by
          induction L using Finset.induction_on with
          | empty => simp
          | @insert j L hj ihL =>
            have hjN := hL (Finset.mem_insert_self j L)
            have hLN : L ⊆ N := fun a ha => hL (Finset.mem_insert_of_mem ha)
            have hjR : j ∉ R := by
              intro hh
              exact (Finset.mem_sdiff.mp hh).2 hjN
            have hjLR : j ∉ L ∪ R := by simp [hj, hjR]
            have hproper : L ∪ R ⊂ K := by
              apply Finset.ssubset_iff_subset_ne.mpr
              refine ⟨Finset.union_subset (hLN.trans hNsub) hRsub, ?_⟩
              intro he
              exact hjLR (he ▸ hNsub hjN)
            have hbound := (ih (L ∪ R) hproper).2 j hjLR
            have hrec := ihL hLN
            have hst := hstep j (L ∪ R)
            rw [Finset.card_insert_of_notMem hj, pow_succ, Finset.insert_union]
            calc
              (1 - z) ^ L.card * (1 - z) * ν.real (avoid R) =
                  (1 - z) * ((1 - z) ^ L.card * ν.real (avoid R)) := by ring
              _ ≤ (1 - z) * ν.real (avoid (L ∪ R)) :=
                mul_le_mul_of_nonneg_left hrec hbase.le
              _ ≤ ν.real (avoid (insert j (L ∪ R))) := by linarith
        have hden := hchain N (Finset.Subset.refl _)
        rw [hNR] at hden
        have hcard : N.card ≤ q := by
          apply le_trans (Finset.card_le_card ?_) (hdep i)
          intro j hj
          obtain ⟨hjK, hjdis⟩ := Finset.mem_filter.mp hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · intro he
            exact hi (he ▸ hjK)
          · exact Finset.not_disjoint_iff_nonempty_inter.mp
              (fun hd => hjdis hd.symm)
        have hpow : (1 - z) ^ q ≤ (1 - z) ^ N.card :=
          pow_le_pow_of_le_one hbase.le (by linarith) hcard
        have hnumN : P ≤ z * (1 - z) ^ N.card :=
          hnum.trans (mul_le_mul_of_nonneg_left hpow hzpos.le)
        calc
          ν.real (B i ∩ avoid K) ≤ ν.real (B i ∩ avoid R) := by
            apply measureReal_mono _ (measure_ne_top ν _)
            intro ω hω
            exact ⟨hω.1, fun j hj => hω.2 j (hRsub hj)⟩
          _ = ν.real (B i) * ν.real (avoid R) := hindR i R hRdis
          _ ≤ P * ν.real (avoid R) :=
            mul_le_mul_of_nonneg_right (hprobR i) measureReal_nonneg
          _ ≤ (z * (1 - z) ^ N.card) * ν.real (avoid R) :=
            mul_le_mul_of_nonneg_right hnumN measureReal_nonneg
          _ ≤ z * ν.real (avoid K) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hden hzpos.le
  have hpositive : 0 < ν {ω | ∀ j, ω ∉ B j} := by
    have h := (hmain Finset.univ).1
    have heq : avoid Finset.univ = {ω | ∀ j, ω ∉ B j} := by simp [avoid]
    rw [heq, measureReal_def] at h
    exact (ENNReal.toReal_pos_iff.mp h).1
  refine ⟨hpositive, ?_⟩
  have hn : ({ω | ∀ j, ω ∉ B j} : Set (T → ℝ × ℝ)).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, measure_empty] at hpositive
    exact (lt_irrefl 0) hpositive
  exact hn
