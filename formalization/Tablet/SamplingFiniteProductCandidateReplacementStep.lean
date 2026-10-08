import Tablet.RandomIndependentSetSampling
import Tablet.SamplingCandidateSetReplacementSurvivalComparison
import Tablet.SamplingFiniteProductLowerOrthantEqualityMeasurable

open BigOperators

-- [TABLET NODE: SamplingFiniteProductCandidateReplacementStep]
theorem SamplingFiniteProductCandidateReplacementStep
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : ℝ) (π : α → ℝ)
    (η : @MeasureTheory.Measure (Bool × ℝ) ⊤)
    (θ : @MeasureTheory.Measure (α → Bool × ℝ) ⊤)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ0 : ∀ x : α, 0 ≤ π x) (hπ1 : ∀ x : α, π x ≤ 1)
    (hη_univ : η Set.univ = 1)
    (hη_active_unit :
      η {ω | ω.1 = true ∧ ω.2 ∈ Set.Icc (0 : ℝ) 1} =
        ENNReal.ofReal p)
    (hη_lower :
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        η {ω | ω.1 = true ∧ 0 ≤ ω.2 ∧ ω.2 ≤ t} =
          ENNReal.ofReal (p * t))
    (hθ_univ : θ Set.univ = 1)
    (hθ_cylinder :
      ∀ A : Finset α, ∀ t : α → ℝ,
        (∀ x : α, x ∈ A → t x ∈ Set.Icc (0 : ℝ) 1) →
          θ {ω |
            (∀ x : α, (ω x).1 = decide (x ∈ A)) ∧
              ∀ x : α, x ∈ A → 0 ≤ (ω x).2 ∧ (ω x).2 ≤ t x} =
            ENNReal.ofReal
              (p ^ A.card *
                (1 - p) ^ ((Finset.univ : Finset α).card - A.card) *
                  ∏ x ∈ A, t x)) :
    η {ω |
        ¬ (ω.1 = true ∧
          (∀ x : α, π x < ω.2) ∧
            ω.2 ∈ Set.Icc (0 : ℝ) 1)} ≤
      θ {ω |
        ∃ x : α,
          ¬ ((ω x).1 = true ∧
            π x < (ω x).2 ∧
              (ω x).2 ∈ Set.Icc (0 : ℝ) 1)} := by
-- BODY
  classical
  letI : MeasurableSpace (Bool × ℝ) := ⊤
  letI : MeasurableSpace (α → Bool × ℝ) := ⊤
  obtain ⟨x0, _, hmax, hcomp⟩ := SamplingCandidateSetReplacementSurvivalComparison
    (Finset.univ : Finset α) p π Finset.univ_nonempty hp0 hp1
    (fun x _ => hπ0 x) (fun x _ => hπ1 x)
  let K : Set (Bool × ℝ) := {ω | ω.1 = true ∧
    (∀ x, π x < ω.2) ∧ ω.2 ∈ Set.Icc (0 : ℝ) 1}
  let L : Set (Bool × ℝ) := {ω | ω.1 = true ∧ 0 ≤ ω.2 ∧ ω.2 ≤ π x0}
  let U : Set (Bool × ℝ) := {ω | ω.1 = true ∧ ω.2 ∈ Set.Icc (0 : ℝ) 1}
  have hL : η L = ENNReal.ofReal (p * π x0) := hη_lower _ ⟨hπ0 x0, hπ1 x0⟩
  have hsub : L ⊆ U := fun ω h => ⟨h.1, h.2.1, h.2.2.trans (hπ1 x0)⟩
  have hK : K = U \ L := by
    ext ω
    constructor
    · rintro ⟨ha, hall, hunit⟩
      exact ⟨⟨ha, hunit⟩, fun hl => (not_le_of_gt (hall x0)) hl.2.2⟩
    · rintro ⟨⟨ha, hunit⟩, hn⟩
      have hlt : π x0 < ω.2 := lt_of_not_ge (fun hle => hn ⟨ha, hunit.1, hle⟩)
      exact ⟨ha, fun x => lt_of_le_of_lt (hmax x (Finset.mem_univ x)) hlt, hunit⟩
  have hmassK : η K = ENNReal.ofReal (p * (1 - π x0)) := by
    rw [hK, MeasureTheory.measure_diff hsub
      MeasurableSpace.measurableSet_top.nullMeasurableSet (by rw [hL]; exact ENNReal.ofReal_ne_top),
      hη_active_unit, hL, ← ENNReal.ofReal_sub _ (mul_nonneg hp0 (hπ0 x0))]
    congr 1
    ring
  let P : Set (α → Bool × ℝ) := {ω | ∀ x,
    (ω x).1 = true ∧ π x < (ω x).2 ∧ (ω x).2 ∈ Set.Icc (0 : ℝ) 1}
  have hrect : ∀ s : α → ℝ, (∀ x, s x ∈ Set.Icc (0 : ℝ) 1) →
      θ {ω | (∀ x, (ω x).1 = true) ∧ ∀ x, 0 ≤ (ω x).2 ∧ (ω x).2 ≤ s x} =
        ENNReal.ofReal (p ^ Fintype.card α * ∏ x, s x) := by
    intro s hs
    simpa using hθ_cylinder Finset.univ s (fun x _ => hs x)
  let F (ω : α → Bool × ℝ) :=
    (∀ x, (ω x).1 = true) ∧ ∀ x, (ω x).2 ∈ Set.Icc (0 : ℝ) 1
  let C : Set (α → ℝ) := Set.pi Set.univ (fun x => Set.Ioc (π x) 1)
  have hF : θ {ω | F ω} = ENNReal.ofReal (p ^ Fintype.card α) := by
    simpa [F] using hrect (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩)
  have hC : MeasurableSet C := MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Ioc)
  have hCcube : C ⊆ {q | ∀ x, q x ∈ Set.Icc (0 : ℝ) 1} := by
    intro q hq x
    have hx := hq x (Set.mem_univ x)
    exact ⟨(hπ0 x).trans hx.1.le, hx.2⟩
  have hlower : ∀ s : α → ℝ, (∀ x, s x ∈ Set.Icc (0 : ℝ) 1) →
      θ {ω | F ω ∧ ∀ x, 0 ≤ (ω x).2 ∧ (ω x).2 ≤ s x} =
        ENNReal.ofReal (p ^ Fintype.card α) * ENNReal.ofReal (∏ x, s x) := by
    intro s hs
    have heq : {ω | F ω ∧ ∀ x, 0 ≤ (ω x).2 ∧ (ω x).2 ≤ s x} =
        {ω | (∀ x, (ω x).1 = true) ∧ ∀ x, 0 ≤ (ω x).2 ∧ (ω x).2 ≤ s x} := by
      ext ω
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, fun x => ⟨(h.2 x).1, (h.2 x).2.trans (hs x).2⟩⟩, h.2⟩⟩
    rw [heq, hrect s hs, ENNReal.ofReal_mul (pow_nonneg hp0 _)]
  have hbox := SamplingFiniteProductLowerOrthantEqualityMeasurable θ F
    (fun ω x => (ω x).2) (by exact measurable_from_top)
    (ENNReal.ofReal (p ^ Fintype.card α)) C hC hCcube
    (by rw [hF]; exact ENNReal.ofReal_ne_top) hF.symm hlower
  have hstrict : θ {ω | (∀ x, (ω x).1 = true) ∧
      ∀ x, π x < (ω x).2 ∧ (ω x).2 ≤ 1} =
      ENNReal.ofReal (p ^ Fintype.card α * ∏ x, (1 - π x)) := by
    have heq : ({ω | F ω ∧ (fun x => (ω x).2) ∈ C} ∩
        {ω | ∀ x, (ω x).2 ∈ Set.Icc (0 : ℝ) 1}) =
        {ω | (∀ x, (ω x).1 = true) ∧ ∀ x, π x < (ω x).2 ∧ (ω x).2 ≤ 1} := by
      ext ω
      constructor
      · intro h
        exact ⟨h.1.1.1, fun x => h.1.2 x (Set.mem_univ x)⟩
      · intro h
        have hu : ∀ x, (ω x).2 ∈ Set.Icc (0 : ℝ) 1 :=
          fun x => ⟨(hπ0 x).trans (h.2 x).1.le, (h.2 x).2⟩
        exact ⟨⟨⟨h.1, hu⟩, fun x _ => h.2 x⟩, hu⟩
    rw [heq] at hbox
    rw [hbox, Real.volume_pi_Ioc,
      ← ENNReal.ofReal_prod_of_nonneg (fun x _ => sub_nonneg.mpr (hπ1 x)),
      ← ENNReal.ofReal_mul (pow_nonneg hp0 _)]
  have hP : P = {ω | (∀ x, (ω x).1 = true) ∧ ∀ x, π x < (ω x).2 ∧ (ω x).2 ≤ 1} := by
    ext ω
    constructor
    · intro h
      exact ⟨fun x => (h x).1, fun x => ⟨(h x).2.1, (h x).2.2.2⟩⟩
    · rintro ⟨ha, hq⟩
      exact fun x => ⟨ha x, (hq x).1, (hπ0 x).trans (hq x).1.le, (hq x).2⟩
  have hmassP : θ P = ENNReal.ofReal (∏ x, p * (1 - π x)) := by
    rw [hP]
    simpa [Finset.prod_mul_distrib] using hstrict
  have hsurvK : η Kᶜ = ENNReal.ofReal (1 - p * (1 - π x0)) := by
    rw [MeasureTheory.measure_compl MeasurableSpace.measurableSet_top (by
      rw [hmassK]; exact ENNReal.ofReal_ne_top), hη_univ, hmassK,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (mul_nonneg hp0 (sub_nonneg.mpr (hπ1 x0)))]
  have hsurvP : θ Pᶜ = ENNReal.ofReal (1 - ∏ x, p * (1 - π x)) := by
    rw [MeasureTheory.measure_compl MeasurableSpace.measurableSet_top (by
      rw [hmassP]; exact ENNReal.ofReal_ne_top), hθ_univ, hmassP,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Finset.prod_nonneg
        (fun x _ => mul_nonneg hp0 (sub_nonneg.mpr (hπ1 x))))]
  have hgoal : η Kᶜ ≤ θ Pᶜ := by
    rw [hsurvK, hsurvP]
    exact ENNReal.ofReal_le_ofReal (by simpa using hcomp)
  simpa only [K, P, Set.compl_setOf, not_forall] using hgoal
