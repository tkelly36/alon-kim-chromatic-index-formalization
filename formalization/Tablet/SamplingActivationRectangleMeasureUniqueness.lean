import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable

open MeasureTheory

-- [TABLET NODE: SamplingActivationRectangleMeasureUniqueness]
theorem SamplingActivationRectangleMeasureUniqueness
    {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : @Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (m : Finset V → ENNReal) (hm : ∀ A, m A ≠ ⊤)
    (hμ : ∀ A, μ {ω | ω.1 = A} = m A)
    (hν : ∀ A, ν {ω | ω.1 = A} = m A)
    (hrμ : ∀ (A : Finset V) (t : V → ℝ), (∀ v, t v ∈ Set.Icc (0 : ℝ) 1) →
      μ {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
        μ {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v))
    (hrν : ∀ (A : Finset V) (t : V → ℝ), (∀ v, t v ∈ Set.Icc (0 : ℝ) 1) →
      ν {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
        ν {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v)) :
    μ = ν := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V) := ⊤
  let Q : Set (V → ℝ) := {q | ∀ v, q v ∈ Set.Icc (0 : ℝ) 1}
  have hQ : MeasurableSet Q := by
    simp only [Q, Set.setOf_forall]
    exact MeasurableSet.iInter fun v => measurableSet_Icc.preimage (measurable_pi_apply v)
  have hH (A : Finset V) : MeasurableSet {ω : Finset V × (V → ℝ) | ω.1 = A} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have calc_atom (ρ : Measure (Finset V × (V → ℝ)))
      (ha : ∀ A, ρ {ω | ω.1 = A} = m A)
      (hr : ∀ (A : Finset V) (t : V → ℝ), (∀ v, t v ∈ Set.Icc (0 : ℝ) 1) →
        ρ {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
          ρ {ω | ω.1 = A} * ENNReal.ofReal (∏ v, t v))
      (E : Set (Finset V × (V → ℝ))) (hE : MeasurableSet E) (A : Finset V) :
      ρ (E ∩ {ω | ω.1 = A}) =
        m A * volume ({q | (A, q) ∈ E} ∩ Q) := by
    let H : Set (Finset V × (V → ℝ)) := {ω | ω.1 = A}
    let U : Set (Finset V × (V → ℝ)) := {ω | ω.2 ∈ Q}
    have hU : MeasurableSet U := hQ.preimage measurable_snd
    have hone : ρ (H ∩ U) = m A := by
      have hh := hr A (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩)
      change ρ {ω | ω.1 = A ∧ ∀ v, 0 ≤ ω.2 v ∧ ω.2 v ≤ 1} = m A
      simpa only [Finset.prod_const_one, ENNReal.ofReal_one, mul_one, ha] using hh
    have hn : ρ (H \ U) = 0 := by
      have hh := measure_diff (μ := ρ) (s₁ := H) (s₂ := H ∩ U)
        Set.inter_subset_left ((hH A).inter hU).nullMeasurableSet
        (hone ▸ hm A)
      have he : H \ (H ∩ U) = H \ U := by ext ω; simp
      rw [he, hone] at hh
      simpa only [H, ha, tsub_self] using hh
    have hnE : ρ ((E ∩ H) \ U) = 0 := by
      apply measure_mono_null (t := H \ U) _ hn
      intro ω h
      exact ⟨h.1.2, h.2⟩
    have hinter := measure_inter_conull' hnE
    let C : Set (V → ℝ) := {q | (A, q) ∈ E} ∩ Q
    have hC : MeasurableSet C :=
      (hE.preimage (measurable_const.prodMk measurable_id)).inter hQ
    have hcalc := SamplingFiniteProductLowerOrthantEqualityMeasurable ρ
      (fun ω => ω.1 = A) Prod.snd measurable_snd (m A) C hC
      Set.inter_subset_right (by rw [ha]; exact hm A) (ha A).symm
      (fun t ht => by simpa only [ha] using hr A t ht)
    have hset : ({ω : Finset V × (V → ℝ) | ω.1 = A ∧ ω.2 ∈ C} ∩
        {ω | ∀ v, ω.2 v ∈ Set.Icc (0 : ℝ) 1}) = (E ∩ H) ∩ U := by
      ext ω
      simp only [C, H, U, Q, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hA, hE, hQ⟩, _⟩
        exact ⟨⟨by simpa only [← hA, Prod.eta] using hE, hA⟩, hQ⟩
      · rintro ⟨⟨hE, hA⟩, hQ⟩
        exact ⟨⟨hA, by simpa only [← hA, Prod.eta] using hE, hQ⟩, hQ⟩
    rw [hset, hinter] at hcalc
    exact hcalc
  apply Measure.ext
  intro E hE
  have hparts : E = ⋃ A : Finset V, E ∩ {ω | ω.1 = A} := by
    ext ω
    simp
  have hd : Pairwise (fun A B : Finset V =>
      Disjoint (E ∩ {ω | ω.1 = A}) (E ∩ {ω | ω.1 = B})) := by
    intro A B hAB
    apply Set.disjoint_left.mpr
    intro ω hA hB
    exact hAB (hA.2.symm.trans hB.2)
  rw [hparts, measure_iUnion hd (fun A => hE.inter (hH A)),
    measure_iUnion hd (fun A => hE.inter (hH A))]
  apply tsum_congr
  intro A
  rw [calc_atom μ hμ hrμ E hE A, calc_atom ν hν hrν E hE A]
