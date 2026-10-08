import Tablet.SamplingFiniteCoordinateMarginalCellLaw

open BigOperators

-- [TABLET NODE: SamplingFiniteCoordinateCellExtensionMass]
theorem SamplingFiniteCoordinateCellExtensionMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (C D A0 AD L U K : Finset V) (t : V → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hCD : Disjoint C D)
    (hA0 : A0 ⊆ C) (hAD : AD ⊆ D)
    (hL : L ⊆ C) (hU : U ⊆ C) (hK : K ⊆ D)
    (hLU : Disjoint L U)
    (hKU : Disjoint K U)
    (hLK : Disjoint L K)
    (ht0 : ∀ v : V, v ∈ (L ∪ K) ∪ U → 0 ≤ t v)
    (ht1 : ∀ v : V, v ∈ (L ∪ K) ∪ U → t v ≤ 1)
    (hν_atom : ∀ A : Finset V,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)))
    (hν_rect : ∀ A : Finset V, ∀ s : V → ℝ,
      (∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v : V, s v)) :
    ∃ wBase wExt : ℝ,
      0 ≤ wBase ∧ 0 ≤ wExt ∧
      ENNReal.ofReal wBase =
        ν {ω |
          ω.1 ∩ C = A0 ∧
            (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
              ∀ v : V, v ∈ U → t v < ω.2 v} ∧
      ENNReal.ofReal wExt =
        ν {ω |
          ω.1 ∩ (C ∪ D) = A0 ∪ AD ∧
            (∀ v : V, v ∈ L ∪ K → ω.2 v ≤ t v) ∧
              ∀ v : V, v ∈ U → t v < ω.2 v} ∧
      wExt =
        wBase *
          (p ^ AD.card * (1 - p) ^ (D.card - AD.card)) *
            (∏ v : V, if v ∈ K then t v else 1) := by
-- BODY
  classical
  have hcuts : L ∪ U ⊆ (L ∪ K) ∪ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left U (Finset.mem_union_left K hv)
    · exact Finset.mem_union_right (L ∪ K) hv
  obtain ⟨wBase, hwBase, hBase, hBaseFormula⟩ :=
    SamplingFiniteCoordinateMarginalCellLaw ν p C A0 L U t hp0 hp1
      hA0 hL hU hLU (fun v hv => ht0 v (hcuts hv))
      (fun v hv => ht1 v (hcuts hv)) hν_atom hν_rect
  obtain ⟨wExt, hwExt, hExt, hExtFormula⟩ :=
    SamplingFiniteCoordinateMarginalCellLaw ν p (C ∪ D) (A0 ∪ AD) (L ∪ K) U t
      hp0 hp1 (Finset.union_subset_union hA0 hAD)
      (Finset.union_subset_union hL hK)
      (fun v hv => Finset.mem_union_left D (hU hv))
      (Finset.disjoint_union_left.mpr ⟨hLU, hKU⟩) ht0 ht1 hν_atom hν_rect
  refine ⟨wBase, wExt, hwBase, hwExt, hBase, hExt, ?_⟩
  have hAA : Disjoint A0 AD := hCD.mono hA0 hAD
  have hcard : C.card + D.card - (A0.card + AD.card) =
      (C.card - A0.card) + (D.card - AD.card) := by
    have := Finset.card_le_card hA0
    have := Finset.card_le_card hAD
    omega
  have hprod : (∏ v : V, if v ∈ L ∪ K then t v else 1) =
      (∏ v : V, if v ∈ L then t v else 1) *
        (∏ v : V, if v ∈ K then t v else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    have hnot : ¬(v ∈ L ∧ v ∈ K) := by
      rintro ⟨hvL, hvK⟩
      exact Finset.disjoint_left.mp hLK hvL hvK
    by_cases hvL : v ∈ L <;> by_cases hvK : v ∈ K <;>
      simp_all only [Finset.mem_union, ite_true, ite_false, or_true, true_or,
        false_or, mul_one, one_mul, not_true_eq_false, and_self]
  rw [hExtFormula, hBaseFormula, Finset.card_union_of_disjoint hAA,
    Finset.card_union_of_disjoint hCD, hcard, pow_add, pow_add, hprod]
  ring
