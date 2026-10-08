import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open BigOperators

-- [TABLET NODE: SamplingTwoCoordinateOutsideSliceVolumeBound]
theorem SamplingTwoCoordinateOutsideSliceVolumeBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V)
    (S T : Finset V)
    (hab : a ≠ b)
    (hSQ : Disjoint S ({a, b} : Finset V))
    (hTQ : Disjoint T ({a, b} : Finset V))
    (hST : Disjoint S T)
    (x y : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxy : y ≤ x) (hx1 : x ≤ 1) :
    MeasureTheory.volume
        {r : {v : V // v ≠ a ∧ v ≠ b} → ℝ |
          ∃ q : V → ℝ,
            y ≤ x ∧
              (∀ w : V, w ∈ S → q w < q a) ∧
                (∀ w : V, w ∈ T → q w < q b) ∧
                  (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                    q a = x ∧ q b = y ∧
                      ∀ v : {v : V // v ≠ a ∧ v ≠ b}, q v.1 = r v} ≤
      ENNReal.ofReal (x ^ S.card * y ^ T.card) := by
-- BODY
  classical
  have _ : a ≠ b := hab
  let β := {v : V // v ≠ a ∧ v ≠ b}
  let upper : β → ℝ :=
    fun v => if v.1 ∈ S then x else if v.1 ∈ T then y else 1
  have hy1 : y ≤ 1 := hxy.trans hx1
  have hsub :
      {r : β → ℝ |
          ∃ q : V → ℝ,
            y ≤ x ∧
              (∀ w : V, w ∈ S → q w < q a) ∧
                (∀ w : V, w ∈ T → q w < q b) ∧
                  (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                    q a = x ∧ q b = y ∧
                      ∀ v : β, q v.1 = r v} ⊆
        Set.Icc (fun _ : β => (0 : ℝ)) upper := by
    intro r hr
    rcases hr with ⟨q, _hyx, hS, hT, hcube, hqa, hqb, hqr⟩
    constructor
    · intro v
      exact (show (0 : ℝ) ≤ r v from by simpa [← hqr v] using (hcube v.1).1)
    · intro v
      by_cases hvS : v.1 ∈ S
      · have hle : r v ≤ x := by
          rw [← hqr v]
          exact le_of_lt (lt_of_lt_of_eq (hS v.1 hvS) hqa)
        simpa [upper, hvS] using hle
      · by_cases hvT : v.1 ∈ T
        · have hle : r v ≤ y := by
            rw [← hqr v]
            exact le_of_lt (lt_of_lt_of_eq (hT v.1 hvT) hqb)
          simpa [upper, hvS, hvT] using hle
        · have hle : r v ≤ 1 := by simpa [← hqr v] using (hcube v.1).2
          simpa [upper, hvS, hvT] using hle
  have hprod :
      (∏ i : β, ENNReal.ofReal (upper i - 0)) =
        ENNReal.ofReal (x ^ S.card * y ^ T.card) := by
    let A : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ S)
    let B : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ T)
    have hAcard : A.card = S.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ A) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro v hv
        have hvnot : v ≠ a ∧ v ≠ b := by
          have hva : v ∉ ({a, b} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hSQ hv hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hva
          exact ⟨hva.1, hva.2⟩
        refine ⟨⟨v, hvnot⟩, ?_, rfl⟩
        simp [A, hv]
    have hBcard : B.card = T.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ B) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro v hv
        have hvnot : v ≠ a ∧ v ≠ b := by
          have hva : v ∉ ({a, b} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hTQ hv hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hva
          exact ⟨hva.1, hva.2⟩
        refine ⟨⟨v, hvnot⟩, ?_, rfl⟩
        simp [B, hv]
    have hdisAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact Finset.disjoint_left.mp hST (Finset.mem_filter.mp hiA).2
        (Finset.mem_filter.mp hiB).2
    let f : β → ENNReal := fun i => ENNReal.ofReal (upper i - 0)
    have hfA : ∀ i ∈ A, f i = ENNReal.ofReal x := by
      intro i hi
      have hiS : i.1 ∈ S := (Finset.mem_filter.mp hi).2
      simp [f, upper, hiS]
    have hfB : ∀ i ∈ B, f i = ENNReal.ofReal y := by
      intro i hi
      have hiS : i.1 ∉ S := by
        intro hiS
        exact Finset.disjoint_left.mp hST hiS (Finset.mem_filter.mp hi).2
      have hiT : i.1 ∈ T := (Finset.mem_filter.mp hi).2
      simp [f, upper, hiS, hiT]
    have hfR : ∀ i ∈ ((Finset.univ : Finset β) \ (A ∪ B)), f i = 1 := by
      intro i hi
      have hnot : i ∉ A ∪ B := (Finset.mem_sdiff.mp hi).2
      have hiS : i.1 ∉ S := by
        intro h
        exact hnot (by simp [A, h])
      have hiT : i.1 ∉ T := by
        intro h
        exact hnot (by simp [B, h])
      simp [f, upper, hiS, hiT]
    have hUsub : (A ∪ B) ⊆ (Finset.univ : Finset β) := by
      intro i _hi
      simp
    have hprod_univ : (∏ i : β, f i) = ∏ i ∈ (A ∪ B), f i := by
      have hs := Finset.prod_sdiff (s₁ := (A ∪ B))
        (s₂ := (Finset.univ : Finset β)) (f := f) hUsub
      have hres : (∏ i ∈ ((Finset.univ : Finset β) \ (A ∪ B)), f i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact hfR i hi
      rw [hres, one_mul] at hs
      exact hs.symm
    have hprodU :
        (∏ i ∈ (A ∪ B), f i) =
          (∏ i ∈ A, f i) * (∏ i ∈ B, f i) := by
      rw [Finset.prod_union hdisAB]
    calc
      (∏ i : β, ENNReal.ofReal (upper i - 0)) = ∏ i : β, f i := by simp [f]
      _ = (∏ i ∈ A, f i) * (∏ i ∈ B, f i) := by
        rw [hprod_univ, hprodU]
      _ = (ENNReal.ofReal x) ^ S.card * (ENNReal.ofReal y) ^ T.card := by
        have hprodA : (∏ i ∈ A, f i) = (ENNReal.ofReal x) ^ A.card := by
          trans ∏ i ∈ A, ENNReal.ofReal x
          · exact Finset.prod_congr rfl (by intro i hi; exact hfA i hi)
          · simp
        have hprodB : (∏ i ∈ B, f i) = (ENNReal.ofReal y) ^ B.card := by
          trans ∏ i ∈ B, ENNReal.ofReal y
          · exact Finset.prod_congr rfl (by intro i hi; exact hfB i hi)
          · simp
        rw [hprodA, hprodB, hAcard, hBcard]
      _ = ENNReal.ofReal (x ^ S.card * y ^ T.card) := by
        rw [ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_pow hx0, ENNReal.ofReal_pow hy0]
        · exact pow_nonneg hx0 _
  change
    MeasureTheory.volume
        {r : β → ℝ |
          ∃ q : V → ℝ,
            y ≤ x ∧
              (∀ w : V, w ∈ S → q w < q a) ∧
                (∀ w : V, w ∈ T → q w < q b) ∧
                  (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                    q a = x ∧ q b = y ∧
                      ∀ v : β, q v.1 = r v} ≤
      ENNReal.ofReal (x ^ S.card * y ^ T.card)
  calc
    MeasureTheory.volume
        {r : β → ℝ |
          ∃ q : V → ℝ,
            y ≤ x ∧
              (∀ w : V, w ∈ S → q w < q a) ∧
                (∀ w : V, w ∈ T → q w < q b) ∧
                  (∀ v : V, q v ∈ Set.Icc (0 : ℝ) 1) ∧
                    q a = x ∧ q b = y ∧
                      ∀ v : β, q v.1 = r v} ≤
        MeasureTheory.volume (Set.Icc (fun _ : β => (0 : ℝ)) upper) :=
          MeasureTheory.measure_mono hsub
    _ = ∏ i : β, ENNReal.ofReal (upper i - 0) := by rw [Real.volume_Icc_pi]
    _ = ENNReal.ofReal (x ^ S.card * y ^ T.card) := hprod
