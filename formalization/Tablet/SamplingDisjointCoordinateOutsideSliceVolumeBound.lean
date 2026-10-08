import Tablet.RandomIndependentSetSampling

open BigOperators

-- [TABLET NODE: SamplingDisjointCoordinateOutsideSliceVolumeBound]
theorem SamplingDisjointCoordinateOutsideSliceVolumeBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b c : V)
    (Sx Sy Sz : Finset V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSxQ : Disjoint Sx ({a, b, c} : Finset V))
    (hSyQ : Disjoint Sy ({a, b, c} : Finset V))
    (hSzQ : Disjoint Sz ({a, b, c} : Finset V))
    (hSxy : Disjoint Sx Sy) (hSxz : Disjoint Sx Sz) (hSyz : Disjoint Sy Sz)
    (x y z : ℝ)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz1 : z ≤ 1) :
    MeasureTheory.volume
        {r : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c} → ℝ |
          ∃ q : V → ℝ,
            q a ≤ q b ∧ q b ≤ q c ∧
              (∀ w : V, w ∈ Sx → q w < q a) ∧
                (∀ w : V, w ∈ Sy → q w < q b) ∧
                  (∀ w : V, w ∈ Sz → q w < q c) ∧
                    (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                      q a = x ∧ q b = y ∧ q c = z ∧
                        ∀ v : {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}, q v.1 = r v} ≤
      ENNReal.ofReal (x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
-- BODY
  classical
  have _ : a ≠ b := hab
  have _ : a ≠ c := hac
  have _ : b ≠ c := hbc
  have _ : z ≤ 1 := hz1
  let β := {v : V // v ≠ a ∧ v ≠ b ∧ v ≠ c}
  let upper : β → ℝ :=
    fun v => if v.1 ∈ Sx then x else if v.1 ∈ Sy then y else if v.1 ∈ Sz then z else 1
  have hsub :
      {r : β → ℝ |
          ∃ q : V → ℝ,
            q a ≤ q b ∧ q b ≤ q c ∧
              (∀ w : V, w ∈ Sx → q w < q a) ∧
                (∀ w : V, w ∈ Sy → q w < q b) ∧
                  (∀ w : V, w ∈ Sz → q w < q c) ∧
                    (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                      q a = x ∧ q b = y ∧ q c = z ∧
                        ∀ v : β, q v.1 = r v} ⊆
        Set.Icc (fun _ : β => (0 : ℝ)) upper := by
    intro r hr
    rcases hr with ⟨q, _hqab, _hqbc, hSx, hSy, hSz, hcube, hqa, hqb, hqc, hqr⟩
    constructor
    · intro v
      exact (show (0 : ℝ) ≤ r v from by simpa [← hqr v] using (hcube v.1).1)
    · intro v
      by_cases hvx : v.1 ∈ Sx
      · have hle : r v ≤ x := by
          rw [← hqr v]
          exact le_of_lt (lt_of_lt_of_eq (hSx v.1 hvx) hqa)
        simpa [upper, hvx] using hle
      · by_cases hvy : v.1 ∈ Sy
        · have hle : r v ≤ y := by
            rw [← hqr v]
            exact le_of_lt (lt_of_lt_of_eq (hSy v.1 hvy) hqb)
          simpa [upper, hvx, hvy] using hle
        · by_cases hvz : v.1 ∈ Sz
          · have hle : r v ≤ z := by
              rw [← hqr v]
              exact le_of_lt (lt_of_lt_of_eq (hSz v.1 hvz) hqc)
            simpa [upper, hvx, hvy, hvz] using hle
          · have hle : r v ≤ 1 := by simpa [← hqr v] using (hcube v.1).2
            simpa [upper, hvx, hvy, hvz] using hle
  have hprod :
      (∏ i : β, ENNReal.ofReal (upper i - 0)) =
        ENNReal.ofReal (x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
    let A : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ Sx)
    let B : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ Sy)
    let C : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ Sz)
    have hAcard : A.card = Sx.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ A) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro v hv
        have hvnot : v ≠ a ∧ v ≠ b ∧ v ≠ c := by
          have hva : v ∉ ({a, b, c} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hSxQ hv hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hva
          exact ⟨hva.1, hva.2.1, hva.2.2⟩
        refine ⟨⟨v, hvnot⟩, ?_, rfl⟩
        simp [A, hv]
    have hBcard : B.card = Sy.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ B) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro v hv
        have hvnot : v ≠ a ∧ v ≠ b ∧ v ≠ c := by
          have hva : v ∉ ({a, b, c} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hSyQ hv hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hva
          exact ⟨hva.1, hva.2.1, hva.2.2⟩
        refine ⟨⟨v, hvnot⟩, ?_, rfl⟩
        simp [B, hv]
    have hCcard : C.card = Sz.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ C) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro v hv
        have hvnot : v ≠ a ∧ v ≠ b ∧ v ≠ c := by
          have hva : v ∉ ({a, b, c} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hSzQ hv hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hva
          exact ⟨hva.1, hva.2.1, hva.2.2⟩
        refine ⟨⟨v, hvnot⟩, ?_, rfl⟩
        simp [C, hv]
    have hdisAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact Finset.disjoint_left.mp hSxy (Finset.mem_filter.mp hiA).2
        (Finset.mem_filter.mp hiB).2
    have hdisAC : Disjoint A C := by
      rw [Finset.disjoint_left]
      intro i hiA hiC
      exact Finset.disjoint_left.mp hSxz (Finset.mem_filter.mp hiA).2
        (Finset.mem_filter.mp hiC).2
    have hdisBC : Disjoint B C := by
      rw [Finset.disjoint_left]
      intro i hiB hiC
      exact Finset.disjoint_left.mp hSyz (Finset.mem_filter.mp hiB).2
        (Finset.mem_filter.mp hiC).2
    let f : β → ENNReal := fun i => ENNReal.ofReal (upper i - 0)
    have hfA : ∀ i ∈ A, f i = ENNReal.ofReal x := by
      intro i hi
      have hix : i.1 ∈ Sx := (Finset.mem_filter.mp hi).2
      simp [f, upper, hix]
    have hfB : ∀ i ∈ B, f i = ENNReal.ofReal y := by
      intro i hi
      have hix : i.1 ∉ Sx := by
        intro hix
        exact Finset.disjoint_left.mp hSxy hix (Finset.mem_filter.mp hi).2
      have hiy : i.1 ∈ Sy := (Finset.mem_filter.mp hi).2
      simp [f, upper, hix, hiy]
    have hfC : ∀ i ∈ C, f i = ENNReal.ofReal z := by
      intro i hi
      have hix : i.1 ∉ Sx := by
        intro hix
        exact Finset.disjoint_left.mp hSxz hix (Finset.mem_filter.mp hi).2
      have hiy : i.1 ∉ Sy := by
        intro hiy
        exact Finset.disjoint_left.mp hSyz hiy (Finset.mem_filter.mp hi).2
      have hiz : i.1 ∈ Sz := (Finset.mem_filter.mp hi).2
      simp [f, upper, hix, hiy, hiz]
    have hfR : ∀ i ∈ ((Finset.univ : Finset β) \ ((A ∪ B) ∪ C)), f i = 1 := by
      intro i hi
      have hnot : i ∉ (A ∪ B) ∪ C := (Finset.mem_sdiff.mp hi).2
      have hix : i.1 ∉ Sx := by
        intro h
        exact hnot (by simp [A, h])
      have hiy : i.1 ∉ Sy := by
        intro h
        exact hnot (by simp [B, h])
      have hiz : i.1 ∉ Sz := by
        intro h
        exact hnot (by simp [C, h])
      simp [f, upper, hix, hiy, hiz]
    have hUsub : ((A ∪ B) ∪ C) ⊆ (Finset.univ : Finset β) := by
      intro i _hi
      simp
    have hprod_univ : (∏ i : β, f i) = ∏ i ∈ ((A ∪ B) ∪ C), f i := by
      have hs := Finset.prod_sdiff (s₁ := ((A ∪ B) ∪ C))
        (s₂ := (Finset.univ : Finset β)) (f := f) hUsub
      have hres : (∏ i ∈ ((Finset.univ : Finset β) \ ((A ∪ B) ∪ C)), f i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact hfR i hi
      rw [hres, one_mul] at hs
      exact hs.symm
    have hdisAB_C : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_union_left]
      exact ⟨hdisAC, hdisBC⟩
    have hprodU :
        (∏ i ∈ ((A ∪ B) ∪ C), f i) =
          (∏ i ∈ A, f i) * (∏ i ∈ B, f i) * (∏ i ∈ C, f i) := by
      rw [Finset.prod_union hdisAB_C, Finset.prod_union hdisAB, mul_assoc]
    calc
      (∏ i : β, ENNReal.ofReal (upper i - 0)) = ∏ i : β, f i := by simp [f]
      _ = (∏ i ∈ A, f i) * (∏ i ∈ B, f i) * (∏ i ∈ C, f i) := by
        rw [hprod_univ, hprodU]
      _ = (ENNReal.ofReal x) ^ Sx.card *
            (ENNReal.ofReal y) ^ Sy.card * (ENNReal.ofReal z) ^ Sz.card := by
        have hprodA : (∏ i ∈ A, f i) = (ENNReal.ofReal x) ^ A.card := by
          trans ∏ i ∈ A, ENNReal.ofReal x
          · exact Finset.prod_congr rfl (by intro i hi; exact hfA i hi)
          · simp
        have hprodB : (∏ i ∈ B, f i) = (ENNReal.ofReal y) ^ B.card := by
          trans ∏ i ∈ B, ENNReal.ofReal y
          · exact Finset.prod_congr rfl (by intro i hi; exact hfB i hi)
          · simp
        have hprodC : (∏ i ∈ C, f i) = (ENNReal.ofReal z) ^ C.card := by
          trans ∏ i ∈ C, ENNReal.ofReal z
          · exact Finset.prod_congr rfl (by intro i hi; exact hfC i hi)
          · simp
        rw [hprodA, hprodB, hprodC, hAcard, hBcard, hCcard]
      _ = ENNReal.ofReal (x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := by
        rw [ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_mul]
          · rw [ENNReal.ofReal_pow hx0, ENNReal.ofReal_pow (le_trans hx0 hxy),
              ENNReal.ofReal_pow (le_trans (le_trans hx0 hxy) hyz)]
          · exact pow_nonneg hx0 _
        · exact mul_nonneg (pow_nonneg hx0 _) (pow_nonneg (le_trans hx0 hxy) _)
  change
    MeasureTheory.volume
        {r : β → ℝ |
          ∃ q : V → ℝ,
            q a ≤ q b ∧ q b ≤ q c ∧
              (∀ w : V, w ∈ Sx → q w < q a) ∧
                (∀ w : V, w ∈ Sy → q w < q b) ∧
                  (∀ w : V, w ∈ Sz → q w < q c) ∧
                    (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                      q a = x ∧ q b = y ∧ q c = z ∧
                        ∀ v : β, q v.1 = r v} ≤
      ENNReal.ofReal (x ^ Sx.card * y ^ Sy.card * z ^ Sz.card)
  calc
    MeasureTheory.volume
        {r : β → ℝ |
          ∃ q : V → ℝ,
            q a ≤ q b ∧ q b ≤ q c ∧
              (∀ w : V, w ∈ Sx → q w < q a) ∧
                (∀ w : V, w ∈ Sy → q w < q b) ∧
                  (∀ w : V, w ∈ Sz → q w < q c) ∧
                    (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                      q a = x ∧ q b = y ∧ q c = z ∧
                        ∀ v : β, q v.1 = r v} ≤
        MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) :=
          MeasureTheory.measure_mono hsub
    _ = ∏ i : β, ENNReal.ofReal (upper i - 0) := by rw [Real.volume_Icc_pi]
    _ = ENNReal.ofReal (x ^ Sx.card * y ^ Sy.card * z ^ Sz.card) := hprod
