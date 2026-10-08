import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable
import Tablet.SamplingUnitCubeChamberVolumeIntegral
import Tablet.SamplingTripleChamberAffineIntegralIdentity

open BigOperators

set_option maxHeartbeats 1000000

-- [TABLET NODE: SamplingTripleFixedActivationSixChamberAssembly]
theorem SamplingTripleFixedActivationSixChamberAssembly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (A : Finset V) (a b c : V)
    (hgamma_pos : 0 < gamma)
    (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab_ind : ¬ G.Adj a b) (hac_ind : ¬ G.Adj a c) (hbc_ind : ¬ G.Adj b c)
    (hcube :
      ν {ω |
        ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hlower_rect :
      ∀ t : V → ℝ,
        (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
          ν {ω |
            ω.1 = A ∧
              ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
            ν {ω | ω.1 = A} *
              ENNReal.ofReal (∏ v : V, t v)) :
    let Q : Finset V := {a, b, c}
    let orders : Finset (V × V × V) :=
      {((a, b, c) : V × V × V), (a, c, b), (b, a, c),
        (b, c, a), (c, a, b), (c, b, a)}
    let weight : V × V × V → ℝ := fun t =>
      (1 / gamma ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / gamma) ^
                  ((A.filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ G.Adj t.1 w).card) *
                (1 - y / gamma) ^
                  ((A.filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                      ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                  (1 - z / gamma) ^
                    ((A.filter fun w : V =>
                      w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                        ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧ G.Adj t.2.2 w).card)
    ν {ω |
        ω.1 = A ∧
          ∀ q : V, q ∈ Q →
            ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ≤
      (∑ t ∈ orders, ν {ω | ω.1 = A} * ENNReal.ofReal (weight t)) ∧
      ∀ t ∈ orders, 0 ≤ weight t := by
-- BODY
  classical
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  intro Q orders weight
  let Sx (t : V × V × V) := A.filter fun w =>
    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ G.Adj t.1 w
  let Sy (t : V × V × V) := A.filter fun w =>
    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w
  let Sz (t : V × V × V) := A.filter fun w =>
    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
      ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧ G.Adj t.2.2 w
  have hweight (t : V × V × V) :
      weight t = ∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y,
        x ^ (Sx t).card * y ^ (Sy t).card * z ^ (Sz t).card :=
    (SamplingTripleChamberAffineIntegralIdentity gamma (Sx t) (Sy t) (Sz t)
      hgamma_pos).symm
  have hmonomial (m n k : ℕ) :
      (∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..z, ∫ x in (0 : ℝ)..y,
        x ^ m * y ^ n * z ^ k) =
        1 / (((m : ℝ) + 1) * (m + n + 2) * (m + n + k + 3)) := by
    have hi (y z : ℝ) :
        (∫ x in (0 : ℝ)..y, x ^ m * y ^ n * z ^ k) =
          y ^ (m + n + 1) * z ^ k / ((m : ℝ) + 1) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
        integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero m), sub_zero]
      rw [show m + n + 1 = (m + 1) + n by omega, pow_add]
      ring
    simp_rw [hi, intervalIntegral.integral_div, intervalIntegral.integral_mul_const,
      integral_pow]
    simp only [zero_pow (by omega : m + n + 1 + 1 ≠ 0), sub_zero]
    have hp (z : ℝ) :
        z ^ (m + n + 1 + 1) / (↑(m + n + 1) + 1) * z ^ k =
          z ^ (m + n + 1 + 1 + k) / (↑(m + n + 1) + 1) := by
      rw [pow_add]
      ring
    simp_rw [hp, intervalIntegral.integral_div, integral_pow]
    simp only [one_pow, zero_pow (by omega : m + n + 1 + 1 + k + 1 ≠ 0), sub_zero]
    push_cast
    simp only [div_div]
    congr 1
    ring
  have hpos (t : V × V × V) : 0 < weight t := by
    rw [hweight, hmonomial]
    positivity
  refine ⟨?_, fun t _ => (hpos t).le⟩
  by_cases hfinite : ν {ω | ω.1 = A} = ⊤
  · have hterm : ν {ω | ω.1 = A} * ENNReal.ofReal (weight (a, b, c)) = ⊤ := by
      rw [hfinite, ENNReal.top_mul]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (hpos _))
    have hmem : (a, b, c) ∈ orders := by simp [orders]
    have hsum := Finset.single_le_sum
      (f := fun t => ν {ω | ω.1 = A} * ENNReal.ofReal (weight t))
      (fun t _ => bot_le) hmem
    dsimp only at hsum
    rw [hterm] at hsum
    exact le_trans le_top hsum
  let cube : Set (Finset V × (V → ℝ)) := {ω | ∀ v : V, ω.2 v ∈ Set.Icc (0 : ℝ) 1}
  have hfull : ν {ω | ω.1 = A ∧ ∀ v : V, ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
      ν {ω | ω.1 = A} := by
    simpa using hlower_rect (fun _ => 1) (fun _ => by norm_num)
  let chamber (t : V × V × V) : Set (Finset V × (V → ℝ)) :=
    {ω | ω.1 = A ∧ ω.2 t.1 ≤ ω.2 t.2.1 ∧ ω.2 t.2.1 ≤ ω.2 t.2.2 ∧
      ∀ q ∈ Q, ∀ w ∈ A, G.Adj q w → ω.2 w < ω.2 q}
  have hdata (t : V × V × V) (ht : t ∈ orders) :
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        ({t.1, t.2.1, t.2.2} : Finset V) = Q := by
    simp only [orders, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Q, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
        Finset.insert_comm] <;> ext v <;> simp [or_comm, or_left_comm]
  have hchamber (t : V × V × V) (ht : t ∈ orders) :
      ν (chamber t) ≤ ν {ω | ω.1 = A} * ENNReal.ofReal (weight t) := by
    rcases hdata t ht with ⟨hpq, hpr, hqr, hQ⟩
    let C : Set (V → ℝ) := {q | q t.1 ≤ q t.2.1 ∧ q t.2.1 ≤ q t.2.2 ∧
      (∀ w ∈ Sx t, q w < q t.1) ∧ (∀ w ∈ Sy t, q w < q t.2.1) ∧
        (∀ w ∈ Sz t, q w < q t.2.2) ∧ ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1}
    have hC : MeasurableSet C := by dsimp [C]; measurability
    have hCcube : C ⊆ {q : V → ℝ | ∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1} :=
      fun _ h => h.2.2.2.2.2
    have htransport := SamplingFiniteProductLowerOrthantEqualityMeasurable ν
      (fun ω => ω.1 = A) (fun ω => ω.2) measurable_snd (ν {ω | ω.1 = A}) C
      hC hCcube hfinite rfl hlower_rect
    have hdisjX : Disjoint (Sx t) ({t.1, t.2.1, t.2.2} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro w hw hq
      exact (Finset.mem_filter.mp hw).2.1 hq
    have hdisjY : Disjoint (Sy t) ({t.1, t.2.1, t.2.2} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro w hw hq
      exact (Finset.mem_filter.mp hw).2.1 hq
    have hdisjZ : Disjoint (Sz t) ({t.1, t.2.1, t.2.2} : Finset V) := by
      apply Finset.disjoint_left.mpr
      intro w hw hq
      exact (Finset.mem_filter.mp hw).2.1 hq
    have hxy : Disjoint (Sx t) (Sy t) := by
      apply Finset.disjoint_left.mpr
      intro w hx hy
      exact (Finset.mem_filter.mp hy).2.2.1 (Finset.mem_filter.mp hx).2.2
    have hxz : Disjoint (Sx t) (Sz t) := by
      apply Finset.disjoint_left.mpr
      intro w hx hz
      exact (Finset.mem_filter.mp hz).2.2.1 (Finset.mem_filter.mp hx).2.2
    have hyz : Disjoint (Sy t) (Sz t) := by
      apply Finset.disjoint_left.mpr
      intro w hy hz
      exact (Finset.mem_filter.mp hz).2.2.2.1 (Finset.mem_filter.mp hy).2.2.2
    have hvol : MeasureTheory.volume C ≤ ENNReal.ofReal (weight t) := by
      rw [hweight]
      exact SamplingUnitCubeChamberVolumeIntegral t.1 t.2.1 t.2.2
        (Sx t) (Sy t) (Sz t) hpq hpr hqr hdisjX hdisjY hdisjZ hxy hxz hyz
    have hmeas : MeasurableSet {ω : Finset V × (V → ℝ) |
        ω.2 t.1 ≤ ω.2 t.2.1 ∧ ω.2 t.2.1 ≤ ω.2 t.2.2 ∧
          ∀ q ∈ Q, ∀ w ∈ A, G.Adj q w → ω.2 w < ω.2 q} := by measurability
    have heq := MeasureTheory.Measure.measure_inter_eq_of_measure_eq hmeas hfull
      (fun ω h => h.1) (by rw [hfull]; exact hfinite)
    have heq' : ν (chamber t ∩ cube) = ν (chamber t) := by
      simpa only [chamber, cube, ← Set.setOf_and, and_assoc, and_left_comm,
        and_comm] using heq
    rw [← heq']
    calc
      ν (chamber t ∩ cube) ≤
          ν ({ω | ω.1 = A ∧ ω.2 ∈ C} ∩ cube) := by
        apply MeasureTheory.measure_mono
        intro ω hω
        rcases hω with ⟨⟨hA, hp, hq, hbeat⟩, hc⟩
        refine ⟨⟨hA, hp, hq, ?_, ?_, ?_, hc⟩, hc⟩
        · intro w hw
          have hw' := Finset.mem_filter.mp hw
          exact hbeat t.1 (hQ ▸ (by simp)) w hw'.1 hw'.2.2
        · intro w hw
          have hw' := Finset.mem_filter.mp hw
          exact hbeat t.2.1 (hQ ▸ (by simp)) w hw'.1 hw'.2.2.2
        · intro w hw
          have hw' := Finset.mem_filter.mp hw
          exact hbeat t.2.2 (hQ ▸ (by simp)) w hw'.1 hw'.2.2.2.2
      _ = ν {ω | ω.1 = A} * MeasureTheory.volume C := htransport
      _ ≤ ν {ω | ω.1 = A} * ENNReal.ofReal (weight t) := mul_le_mul_left' hvol _
  have hcover : {ω : Finset V × (V → ℝ) | ω.1 = A ∧
      ∀ q ∈ Q, ∀ w ∈ A, G.Adj q w → ω.2 w < ω.2 q} ⊆
        ⋃ t ∈ orders, chamber t := by
    intro ω hω
    have horder : ∃ t ∈ orders, ω.2 t.1 ≤ ω.2 t.2.1 ∧ ω.2 t.2.1 ≤ ω.2 t.2.2 := by
      by_cases hab' : ω.2 a ≤ ω.2 b
      · by_cases hbc' : ω.2 b ≤ ω.2 c
        · exact ⟨(a, b, c), by simp [orders], hab', hbc'⟩
        · by_cases hac' : ω.2 a ≤ ω.2 c
          · exact ⟨(a, c, b), by simp [orders], hac', le_of_not_ge hbc'⟩
          · exact ⟨(c, a, b), by simp [orders], le_of_not_ge hac', hab'⟩
      · by_cases hac' : ω.2 a ≤ ω.2 c
        · exact ⟨(b, a, c), by simp [orders], le_of_not_ge hab', hac'⟩
        · by_cases hbc' : ω.2 b ≤ ω.2 c
          · exact ⟨(b, c, a), by simp [orders], hbc', le_of_not_ge hac'⟩
          · exact ⟨(c, b, a), by simp [orders], le_of_not_ge hbc', le_of_not_ge hab'⟩
    rcases horder with ⟨t, ht, hp, hq⟩
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hω.1, hp, hq, hω.2⟩⟩
  exact (MeasureTheory.measure_mono hcover).trans
    ((MeasureTheory.measure_biUnion_finset_le orders chamber).trans
      (Finset.sum_le_sum hchamber))
