import Tablet.SamplingBernoulliActivationMass
import Tablet.SamplingOneCoordinateChamberVolume
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

open BigOperators

universe u

-- [TABLET NODE: SamplingFiniteProductPriorityLawExists]
theorem SamplingFiniteProductPriorityLawExists :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, ∀ gamma : ℝ,
          0 < gamma → gamma ≤ (Delta : ℝ) →
            ∃ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
              ν Set.univ = 1 ∧
                (∀ A : Finset V,
                  ν {ω | ω.1 = A} =
                    ENNReal.ofReal
                      ((gamma / (Delta : ℝ)) ^ A.card *
                        (1 - gamma / (Delta : ℝ)) ^
                          ((Finset.univ : Finset V).card - A.card))) ∧
                (∀ A : Finset V,
                  ν {ω | ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
                    ν {ω | ω.1 = A}) ∧
                (∀ A : Finset V, ∀ t : V → ℝ,
                  (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                    ν {ω |
                      ω.1 = A ∧
                        ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                      ν {ω | ω.1 = A} *
                        ENNReal.ofReal (∏ v : V, t v)) ∧
                (∀ A : Finset V, ∀ v : V, v ∈ A →
                  ν {ω |
                    ω.1 = A ∧
                      (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
                        ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
                    ν {ω | ω.1 = A} *
                      ENNReal.ofReal
                        (∫ a in (0 : ℝ)..1,
                          a ^
                            ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))) := by
-- BODY
  classical
  intro V hV hDec G hAdj Delta gamma hgamma hle
  let w : Finset V → ℝ := fun A =>
    (gamma / (Delta : ℝ)) ^ A.card *
      (1 - gamma / (Delta : ℝ)) ^
        ((Finset.univ : Finset V).card - A.card)
  let cube : Set (V → ℝ) := Set.Icc (fun _ : V => (0 : ℝ)) (fun _ : V => (1 : ℝ))
  let lam : MeasureTheory.Measure (V → ℝ) := MeasureTheory.volume.restrict cube
  letI : MeasurableSpace (Finset V) := ⊤
  let act : MeasureTheory.Measure (Finset V) :=
    ∑ A : Finset V, (ENNReal.ofReal (w A)) • MeasureTheory.Measure.dirac A
  let ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance) :=
    MeasureTheory.Measure.prod act lam
  have hmass : lam Set.univ = 1 := by
    have hcube_eq : cube = Set.Icc (fun _ : V => (0 : ℝ)) (fun _ : V => (1 : ℝ)) := rfl
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    change MeasureTheory.volume cube = 1
    rw [hcube_eq, Real.volume_Icc_pi]
    simp
  have hact_atom : ∀ A : Finset V,
      act ({A} : Set (Finset V)) = ENNReal.ofReal (w A) := by
    intro A
    rw [show act ({A} : Set (Finset V)) =
        ∑ B : Finset V,
          ENNReal.ofReal (w B) *
            MeasureTheory.Measure.dirac B ({A} : Set (Finset V)) by
      simp [act]]
    rw [Finset.sum_eq_single A]
    · simp
    · intro B _ hBA
      simp [hBA]
    · intro hA
      exact False.elim (hA (Finset.mem_univ A))
  refine ⟨ν, ?_, ?_, ?_, ?_, ?_⟩
  · have hnonneg := (SamplingBernoulliActivationMass (V := V) Delta gamma hgamma hle).1
    have hsum_w : (∑ A : Finset V, w A) = 1 := by
      simpa [w] using (SamplingBernoulliActivationMass (V := V) Delta gamma hgamma hle).2
    change (MeasureTheory.Measure.prod act lam) Set.univ = 1
    rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
    have hact : act Set.univ = 1 := by
      rw [show act Set.univ =
          ∑ A : Finset V, ENNReal.ofReal (w A) by
        simp [act]]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun A _ => by simpa [w] using hnonneg A)]
      simp [hsum_w]
    simp [hact, hmass]
  · intro A
    change (MeasureTheory.Measure.prod act lam) {ω | ω.1 = A} =
      ENNReal.ofReal (w A)
    have hset :
        ({ω : Finset V × (V → ℝ) | ω.1 = A} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ Set.univ := by
      ext ω
      simp
    rw [hset, MeasureTheory.Measure.prod_prod]
    rw [hact_atom A, hmass]
    simp
  · intro A
    change (MeasureTheory.Measure.prod act lam)
        {ω | ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
      (MeasureTheory.Measure.prod act lam) {ω | ω.1 = A}
    let E : Set (V → ℝ) :=
      {q | ∀ v : V, v ∈ A → q v ∈ Set.Icc (0 : ℝ) 1}
    have hset_left :
        ({ω : Finset V × (V → ℝ) |
            ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ E := by
      ext ω
      simp [E]
    have hset_right :
        ({ω : Finset V × (V → ℝ) | ω.1 = A} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ Set.univ := by
      ext ω
      simp
    rw [hset_left, hset_right, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.prod_prod]
    have hE_meas : MeasurableSet E := by
      dsimp [E]
      measurability
    have hcube_subset : cube ⊆ E := by
      intro q hq v hv
      exact ⟨hq.1 v, hq.2 v⟩
    have hE_mass : lam E = 1 := by
      rw [MeasureTheory.Measure.restrict_apply hE_meas]
      rw [Set.inter_eq_right.mpr hcube_subset]
      change MeasureTheory.volume cube = 1
      rw [show cube = Set.Icc (fun _ : V => (0 : ℝ)) (fun _ : V => (1 : ℝ)) from rfl,
        Real.volume_Icc_pi]
      simp
    rw [hE_mass, hmass]
  · intro A t ht
    change (MeasureTheory.Measure.prod act lam)
        {ω |
          ω.1 = A ∧
            ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
      (MeasureTheory.Measure.prod act lam) {ω | ω.1 = A} *
        ENNReal.ofReal (∏ v : V, t v)
    let box : Set (V → ℝ) :=
      {q | ∀ v : V, 0 ≤ q v ∧ q v ≤ t v}
    have hset_left :
        ({ω : Finset V × (V → ℝ) |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ box := by
      ext ω
      simp [box]
    have hset_right :
        ({ω : Finset V × (V → ℝ) | ω.1 = A} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ Set.univ := by
      ext ω
      simp
    have hbox_meas : MeasurableSet box := by
      dsimp [box]
      measurability
    have hbox_subset : box ⊆ cube := by
      intro q hq
      exact ⟨fun v => (hq v).1, fun v => (hq v).2.trans (ht v).2⟩
    have hbox_Icc : box = Set.Icc (fun _ : V => (0 : ℝ)) t := by
      ext q
      constructor
      · intro hq
        exact ⟨fun v => (hq v).1, fun v => (hq v).2⟩
      · intro hq v
        exact ⟨hq.1 v, hq.2 v⟩
    have hbox_mass : lam box = ENNReal.ofReal (∏ v : V, t v) := by
      rw [MeasureTheory.Measure.restrict_apply hbox_meas]
      rw [Set.inter_eq_left.mpr hbox_subset, hbox_Icc, Real.volume_Icc_pi]
      simp [ENNReal.ofReal_prod_of_nonneg, fun v : V => (ht v).1]
    rw [hset_left, hset_right, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.prod_prod, hact_atom A, hmass, hbox_mass]
    simp
  · intro A v hv
    change (MeasureTheory.Measure.prod act lam)
        {ω |
          ω.1 = A ∧
            (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
              ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
      (MeasureTheory.Measure.prod act lam) {ω | ω.1 = A} *
        ENNReal.ofReal
          (∫ a in (0 : ℝ)..1,
            a ^
              ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))
    let B : Finset V := Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u
    let E : Set (V → ℝ) :=
      {q |
        (∀ u : V, u ∈ A → q u ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ u : V, u ∈ A → G.Adj v u → q u < q v}
    let C : Set (V → ℝ) :=
      {q |
        (∀ x : V, q x ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ z : V, z ∈ B → q z < q v}
    have hvB : v ∉ B := by
      intro hvBmem
      have hvadj : G.Adj v v := (Finset.mem_filter.mp hvBmem).2.2
      exact G.loopless.irrefl v hvadj
    have hset_left :
        ({ω : Finset V × (V → ℝ) |
          ω.1 = A ∧
            (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
              ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ E := by
      ext ω
      simp [E]
    have hset_right :
        ({ω : Finset V × (V → ℝ) | ω.1 = A} :
            Set (Finset V × (V → ℝ))) =
          ({A} : Set (Finset V)) ×ˢ Set.univ := by
      ext ω
      simp
    have hE_meas : MeasurableSet E := by
      dsimp [E]
      measurability
    have hcube_inter_E : cube ∩ E = C := by
      ext q
      constructor
      · intro hq
        constructor
        · intro x
          exact ⟨hq.1.1 x, hq.1.2 x⟩
        · intro z hzB
          have hz : z ∈ A ∧ G.Adj v z := (Finset.mem_filter.mp hzB).2
          exact hq.2.2 z hz.1 hz.2
      · intro hq
        constructor
        · exact ⟨fun x => (hq.1 x).1, fun x => (hq.1 x).2⟩
        · constructor
          · intro u _hu
            exact hq.1 u
          · intro u huA huv
            exact hq.2 u (by simp [B, huA, huv])
    have hC_volume :
        MeasureTheory.volume C =
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1,
              a ^
                ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
      simpa [C, B] using
        (SamplingOneCoordinateChamberVolume (V := V) v B hvB)
    have hE_mass :
        lam E =
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1,
              a ^
                ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card)) := by
      rw [MeasureTheory.Measure.restrict_apply hE_meas]
      rw [Set.inter_comm E cube, hcube_inter_E, hC_volume]
    rw [hset_left, hset_right, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.prod_prod, hE_mass, hmass]
    simp
