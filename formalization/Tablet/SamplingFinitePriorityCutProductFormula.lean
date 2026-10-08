import Tablet.Preamble
import Mathlib.MeasureTheory.Measure.MeasureSpace

open BigOperators

set_option maxHeartbeats 1000000

-- [TABLET NODE: SamplingFinitePriorityCutProductFormula]
theorem SamplingFinitePriorityCutProductFormula
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (A L U : Finset V) (t : V → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hLU : Disjoint L U)
    (ht0 : ∀ v : V, v ∈ L ∪ U → 0 ≤ t v)
    (ht1 : ∀ v : V, v ∈ L ∪ U → t v ≤ 1)
    (hν_atom : ∀ A0 : Finset V,
      ν {ω | ω.1 = A0} =
        ENNReal.ofReal
          (p ^ A0.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A0.card)))
    (hν_rect : ∀ A0 : Finset V, ∀ s : V → ℝ,
      (∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A0 ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} =
          ν {ω | ω.1 = A0} * ENNReal.ofReal (∏ v : V, s v)) :
    ν {ω |
        ω.1 = A ∧
          (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
            (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
              ∀ v : V, v ∈ U → t v < ω.2 v} =
      ENNReal.ofReal
        (p ^ A.card *
          (1 - p) ^ ((Finset.univ : Finset V).card - A.card) *
            (∏ v : V, if v ∈ L then t v else 1) *
              (∏ v : V, if v ∈ U then (1 - t v) else 1)) := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  let atom : ℝ :=
    p ^ A.card * (1 - p) ^ ((Finset.univ : Finset V).card - A.card)
  have hatom_nonneg : 0 ≤ atom := by
    dsimp [atom]
    exact mul_nonneg (pow_nonneg hp0 A.card)
      (pow_nonneg (sub_nonneg.mpr hp1) ((Finset.univ : Finset V).card - A.card))
  have hmain :
      ∀ U : Finset V, ∀ L : Finset V,
        Disjoint L U →
        (∀ v : V, v ∈ L ∪ U → 0 ≤ t v) →
        (∀ v : V, v ∈ L ∪ U → t v ≤ 1) →
        ν {ω |
            ω.1 = A ∧
              (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
                (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                  ∀ v : V, v ∈ U → t v < ω.2 v} =
          ENNReal.ofReal
            (atom *
              (∏ v : V, if v ∈ L then t v else 1) *
                (∏ v : V, if v ∈ U then (1 - t v) else 1)) := by
    intro U
    refine Finset.induction_on U ?base ?step
    · intro L hLU ht0 ht1
      let s : V → ℝ := fun v => if v ∈ L then t v else 1
      have hs : ∀ v : V, s v ∈ Set.Icc (0 : ℝ) 1 := by
        intro v
        by_cases hvL : v ∈ L
        · have hvLU : v ∈ L ∪ (∅ : Finset V) := by
            simp [hvL]
          exact ⟨by simpa [s, hvL] using ht0 v hvLU,
            by simpa [s, hvL] using ht1 v hvLU⟩
        · simp [s, hvL]
      have hset :
          {ω : Finset V × (V → ℝ) |
            ω.1 = A ∧
              (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
                (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                  ∀ v : V, v ∈ (∅ : Finset V) → t v < ω.2 v} =
          {ω : Finset V × (V → ℝ) |
            ω.1 = A ∧ ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ s v} := by
        ext ω
        constructor
        · intro hω
          refine ⟨hω.1, ?_⟩
          intro v
          by_cases hvL : v ∈ L
          · exact ⟨(hω.2.1 v).1, by simpa [s, hvL] using hω.2.2.1 v hvL⟩
          · exact ⟨(hω.2.1 v).1, by simpa [s, hvL] using (hω.2.1 v).2⟩
        · intro hω
          refine ⟨hω.1, ?_, ?_, ?_⟩
          · intro v
            by_cases hvL : v ∈ L
            · exact ⟨(hω.2 v).1,
                (hω.2 v).2.trans (by
                  simpa [s, hvL] using ht1 v (by simp [hvL]))⟩
            · exact ⟨(hω.2 v).1, by simpa [s, hvL] using (hω.2 v).2⟩
          · intro v hvL
            simpa [s, hvL] using (hω.2 v).2
          · intro v hvU
            simp at hvU
      have hprod_nonneg : 0 ≤ ∏ v : V, s v := by
        refine Finset.prod_nonneg ?_
        intro v hv
        by_cases hvL : v ∈ L
        · simpa [s, hvL] using ht0 v (by simp [hvL])
        · simp [s, hvL]
      rw [hset, hν_rect A s hs, hν_atom A]
      rw [← ENNReal.ofReal_mul hatom_nonneg]
      simp [s, atom, mul_assoc]
    · intro u U0 hu_not_U0 ih L hLU ht0 ht1
      have hu_not_L : u ∉ L := by
        intro huL
        exact (Finset.disjoint_left.mp hLU huL) (by simp)
      have hLU0 : Disjoint L U0 := by
        exact hLU.mono_right (by intro v hv; simp [hv])
      have hInsU0 : Disjoint (insert u L) U0 := by
        rw [Finset.disjoint_left]
        intro v hvIns hvU0
        rcases Finset.mem_insert.mp hvIns with rfl | hvL
        · exact hu_not_U0 hvU0
        · exact (Finset.disjoint_left.mp hLU hvL) (by simp [hvU0])
      have ht0_LU0 : ∀ v : V, v ∈ L ∪ U0 → 0 ≤ t v := by
        intro v hv
        exact ht0 v (by
          rcases Finset.mem_union.mp hv with hvL | hvU0
          · exact Finset.mem_union.mpr (Or.inl hvL)
          · exact Finset.mem_union.mpr (Or.inr (by simp [hvU0])))
      have ht1_LU0 : ∀ v : V, v ∈ L ∪ U0 → t v ≤ 1 := by
        intro v hv
        exact ht1 v (by
          rcases Finset.mem_union.mp hv with hvL | hvU0
          · exact Finset.mem_union.mpr (Or.inl hvL)
          · exact Finset.mem_union.mpr (Or.inr (by simp [hvU0])))
      have ht0_ins : ∀ v : V, v ∈ insert u L ∪ U0 → 0 ≤ t v := by
        intro x hv
        rcases Finset.mem_union.mp hv with hvIns | hvU0
        · exact ht0 x (by
            rcases Finset.mem_insert.mp hvIns with hx | hvL
            · exact Finset.mem_union.mpr (Or.inr (by simp [hx]))
            · exact Finset.mem_union.mpr (Or.inl hvL))
        · exact ht0 x (by simp [hvU0])
      have ht1_ins : ∀ v : V, v ∈ insert u L ∪ U0 → t v ≤ 1 := by
        intro x hv
        rcases Finset.mem_union.mp hv with hvIns | hvU0
        · exact ht1 x (by
            rcases Finset.mem_insert.mp hvIns with hx | hvL
            · exact Finset.mem_union.mpr (Or.inr (by simp [hx]))
            · exact Finset.mem_union.mpr (Or.inl hvL))
        · exact ht1 x (by simp [hvU0])
      let Ebase : Set (Finset V × (V → ℝ)) :=
        {ω |
          ω.1 = A ∧
            (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
              (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                ∀ v : V, v ∈ U0 → t v < ω.2 v}
      let Elow : Set (Finset V × (V → ℝ)) :=
        {ω |
          ω.1 = A ∧
            (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
              (∀ v : V, v ∈ insert u L → ω.2 v ≤ t v) ∧
                ∀ v : V, v ∈ U0 → t v < ω.2 v}
      have hcell_diff :
          {ω : Finset V × (V → ℝ) |
            ω.1 = A ∧
              (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
                (∀ v : V, v ∈ L → ω.2 v ≤ t v) ∧
                  ∀ v : V, v ∈ insert u U0 → t v < ω.2 v} =
          Ebase \ Elow := by
        ext ω
        constructor
        · intro hω
          refine ⟨?_, ?_⟩
          · refine ⟨hω.1, hω.2.1, hω.2.2.1, ?_⟩
            intro v hv
            exact hω.2.2.2 v (by simp [hv])
          · intro hlow
            have hle : ω.2 u ≤ t u := hlow.2.2.1 u (by simp)
            have hlt : t u < ω.2 u := hω.2.2.2 u (by simp)
            exact (not_le_of_gt hlt) hle
        · intro hω
          rcases hω with ⟨hbase, hnotlow⟩
          refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, ?_⟩
          intro x hvU
          rcases Finset.mem_insert.mp hvU with hx | hxU0
          · by_contra hnot
            have hnotu : ¬ t u < ω.2 u := by
              simpa [hx] using hnot
            have hins : ∀ w : V, w ∈ insert u L → ω.2 w ≤ t w := by
              intro w hw
              rcases Finset.mem_insert.mp hw with hw_eq | hwL
              · simpa [hw_eq] using le_of_not_gt hnotu
              · exact hbase.2.2.1 w hwL
            exact hnotlow ⟨hbase.1, hbase.2.1, hins, hbase.2.2.2⟩
          · exact hbase.2.2.2 x hxU0
      have hsubset : Elow ⊆ Ebase := by
        intro ω hω
        exact ⟨hω.1, hω.2.1, (by
          intro v hvL
          exact hω.2.2.1 v (by simp [hvL])), hω.2.2.2⟩
      have hbase_measure := ih L hLU0 ht0_LU0 ht1_LU0
      have hlow_measure := ih (insert u L) hInsU0 ht0_ins ht1_ins
      have hlow_finite : ν Elow ≠ ⊤ := by
        change
          ν {ω |
            ω.1 = A ∧
              (∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1) ∧
                (∀ v : V, v ∈ insert u L → ω.2 v ≤ t v) ∧
                  ∀ v : V, v ∈ U0 → t v < ω.2 v} ≠ ⊤
        rw [hlow_measure]
        exact ENNReal.ofReal_ne_top
      rw [hcell_diff]
      rw [MeasureTheory.measure_diff hsubset
        (show MeasureTheory.NullMeasurableSet Elow ν from by
          exact (by
            dsimp [Elow]
            measurability : MeasurableSet Elow).nullMeasurableSet)
        hlow_finite]
      rw [hbase_measure, hlow_measure]
      have ht0u : 0 ≤ t u := ht0 u (by simp)
      have ht1u : t u ≤ 1 := ht1 u (by simp)
      have hlow_real_nonneg :
          0 ≤ atom *
            (∏ v : V, if v ∈ insert u L then t v else 1) *
              (∏ v : V, if v ∈ U0 then (1 - t v) else 1) := by
        refine mul_nonneg (mul_nonneg hatom_nonneg ?_) ?_
        · refine Finset.prod_nonneg ?_
          intro v hv
          by_cases hvMem : v ∈ insert u L
          · rcases Finset.mem_insert.mp hvMem with hv_eq | hvL
            · simpa [hvMem] using (by simpa [hv_eq] using ht0u)
            · simpa [hvMem] using ht0 v (by simp [hvL])
          · simp [hvMem]
        · refine Finset.prod_nonneg ?_
          intro v hv
          by_cases hvMem : v ∈ U0
          · simpa [hvMem] using sub_nonneg.mpr (ht1 v (by simp [hvMem]))
          · simp [hvMem]
      rw [← ENNReal.ofReal_sub _ hlow_real_nonneg]
      congr 1
      have hprod_insert_L :
          (∏ v : V, if v ∈ insert u L then t v else 1) =
            t u * (∏ v : V, if v ∈ L then t v else 1) := by
        simp only [Finset.mem_insert]
        rw [← Finset.prod_filter (s := (Finset.univ : Finset V))
            (p := fun v => v = u ∨ v ∈ L) (f := t),
          ← Finset.prod_filter (s := (Finset.univ : Finset V))
            (p := fun v => v ∈ L) (f := t)]
        rw [← Finset.prod_insert
          (s := (Finset.univ.filter fun v : V => v ∈ L)) (a := u) (f := t)]
        · congr 1
          ext v
          simp
        · simp [hu_not_L]
      have hprod_insert_U :
          (∏ v : V, if v ∈ insert u U0 then (1 - t v) else 1) =
            (1 - t u) * (∏ v : V, if v ∈ U0 then (1 - t v) else 1) := by
        simp only [Finset.mem_insert]
        rw [← Finset.prod_filter (s := (Finset.univ : Finset V))
            (p := fun v => v = u ∨ v ∈ U0) (f := fun v => 1 - t v),
          ← Finset.prod_filter (s := (Finset.univ : Finset V))
            (p := fun v => v ∈ U0) (f := fun v => 1 - t v)]
        rw [← Finset.prod_insert
          (s := (Finset.univ.filter fun v : V => v ∈ U0)) (a := u)
          (f := fun v => 1 - t v)]
        · congr 1
          ext v
          simp
        · simp [hu_not_U0]
      rw [hprod_insert_L, hprod_insert_U]
      simp [atom, mul_assoc, mul_comm]
      ring
  rw [hmain U L hLU ht0 ht1]
