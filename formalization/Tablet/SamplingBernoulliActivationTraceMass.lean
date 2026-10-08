import Tablet.Preamble

open MeasureTheory

-- [TABLET NODE: SamplingBernoulliActivationTraceMass]
theorem SamplingBernoulliActivationTraceMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hact : ∀ F : Finset V, ν {ω | ω.1 = F} =
      ENNReal.ofReal (p ^ F.card * (1 - p) ^ (Fintype.card V - F.card)))
    (S A : Finset V) (hA : A ⊆ S) :
    ν {ω | ω.1 ∩ S = A} =
      ENNReal.ofReal (p ^ A.card * (1 - p) ^ (S.card - A.card)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  have hout (E : Finset V) (hE : E ∈ Sᶜ.powerset) :
      ∀ v ∈ E, v ∉ S := by
    intro v hv
    simpa using (Finset.mem_powerset.mp hE) hv
  have hrecover (E : Finset V) (hE : E ∈ Sᶜ.powerset) : (A ∪ E) \ S = E := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hn⟩
      · exact (hn (hA hv)).elim
      · exact hv
    · intro hv
      exact ⟨Or.inr hv, hout E hE v hv⟩
  have hcover : {ω : Finset V × (V → ℝ) | ω.1 ∩ S = A} =
      ⋃ E ∈ Sᶜ.powerset, {ω | ω.1 = A ∪ E} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨ω.1 \ S, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro v hv
        simpa using (Finset.mem_sdiff.mp hv).2
      · rw [← h]
        ext v
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
    · rintro ⟨E, hE, h⟩
      rw [h]
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hv | hv, hs⟩
        · exact hv
        · exact (hout E hE v hv hs).elim
      · intro hv
        exact ⟨Or.inl hv, hA hv⟩
  have hd : Set.PairwiseDisjoint (↑Sᶜ.powerset)
      (fun E : Finset V => {ω : Finset V × (V → ℝ) | ω.1 = A ∪ E}) := by
    intro E hE F hF hEF
    apply Set.disjoint_left.mpr
    intro ω he hf
    apply hEF
    have hh := congrArg (fun K : Finset V => K \ S) (he.symm.trans hf)
    simpa only [hrecover E hE, hrecover F hF] using hh
  rw [hcover, measure_biUnion_finset hd (fun E _ =>
    measurable_fst (measurableSet_singleton (A ∪ E)))]
  simp_rw [hact]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun E _ =>
    mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _))]
  congr 1
  have hterm (E : Finset V) (hE : E ∈ Sᶜ.powerset) :
      p ^ (A ∪ E).card * (1 - p) ^ (Fintype.card V - (A ∪ E).card) =
        (p ^ A.card * (1 - p) ^ (S.card - A.card)) *
          (p ^ E.card * (1 - p) ^ (Sᶜ.card - E.card)) := by
    have hdis : Disjoint A E := Finset.disjoint_left.mpr
      (fun v hv he => hout E hE v he (hA hv))
    have hcard := Finset.card_union_of_disjoint hdis
    have ha := Finset.card_le_card hA
    have he := Finset.card_le_card (Finset.mem_powerset.mp hE)
    have hs : S.card + Sᶜ.card = Fintype.card V := by
      rw [Finset.card_compl]
      exact Nat.add_sub_of_le (Finset.card_le_univ S)
    have hdiff : Fintype.card V - (A ∪ E).card =
        (S.card - A.card) + (Sᶜ.card - E.card) := by omega
    rw [hdiff, hcard, pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Finset.sum_pow_mul_eq_add_pow]
  have hpadd : p + (1 - p) = 1 := by ring
  rw [hpadd, one_pow, mul_one]
