import Tablet.Preamble
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open BigOperators

-- [TABLET NODE: SamplingTwoCoordinateFiberBoxVolume]
theorem SamplingTwoCoordinateFiberBoxVolume
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (BU BT : Finset V)
    (huv : u ≠ v)
    (hBUQ : Disjoint BU ({u, v} : Finset V))
    (hBTQ : Disjoint BT ({u, v} : Finset V))
    (hBT : Disjoint BU BT)
    (a b : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) :
    MeasureTheory.volume
        (Set.pi Set.univ fun w : {w : V // w ≠ u ∧ w ≠ v} =>
          Set.Ico (0 : ℝ)
            (if w.1 ∈ BU then a else if w.1 ∈ BT then b else 1)) =
      ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
-- BODY
  classical
  have _ : u ≠ v := huv
  have _ : b ≤ a := hba
  have _ : a ≤ 1 := ha1
  let β := {w : V // w ≠ u ∧ w ≠ v}
  let upper : β → ℝ :=
    fun w => if w.1 ∈ BU then a else if w.1 ∈ BT then b else 1
  have hprod :
      (∏ i : β, ENNReal.ofReal (upper i - 0)) =
        ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
    let A : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ BU)
    let B : Finset β := Finset.univ.filter (fun i : β => i.1 ∈ BT)
    have hAcard : A.card = BU.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ A) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro w hw
        have hwu : w ≠ u ∧ w ≠ v := by
          have hwQ : w ∉ ({u, v} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hBUQ hw hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hwQ
          exact ⟨hwQ.1, hwQ.2⟩
        refine ⟨⟨w, hwu⟩, ?_, rfl⟩
        simp [A, hw]
    have hBcard : B.card = BT.card := by
      refine Finset.card_bij (fun (i : β) (_ : i ∈ B) => i.1) ?_ ?_ ?_
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i _hi j _hj hij
        exact Subtype.ext hij
      · intro w hw
        have hwu : w ≠ u ∧ w ≠ v := by
          have hwQ : w ∉ ({u, v} : Finset V) :=
            fun hmem => Finset.disjoint_left.mp hBTQ hw hmem
          simp [Finset.mem_insert, Finset.mem_singleton] at hwQ
          exact ⟨hwQ.1, hwQ.2⟩
        refine ⟨⟨w, hwu⟩, ?_, rfl⟩
        simp [B, hw]
    have hdisAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact Finset.disjoint_left.mp hBT (Finset.mem_filter.mp hiA).2
        (Finset.mem_filter.mp hiB).2
    let f : β → ENNReal := fun i => ENNReal.ofReal (upper i - 0)
    have hfA : ∀ i ∈ A, f i = ENNReal.ofReal a := by
      intro i hi
      have hiBU : i.1 ∈ BU := (Finset.mem_filter.mp hi).2
      simp [f, upper, hiBU]
    have hfB : ∀ i ∈ B, f i = ENNReal.ofReal b := by
      intro i hi
      have hiBU : i.1 ∉ BU := by
        intro hiBU
        exact Finset.disjoint_left.mp hBT hiBU (Finset.mem_filter.mp hi).2
      have hiBT : i.1 ∈ BT := (Finset.mem_filter.mp hi).2
      simp [f, upper, hiBU, hiBT]
    have hfR : ∀ i ∈ ((Finset.univ : Finset β) \ (A ∪ B)), f i = 1 := by
      intro i hi
      have hnot : i ∉ A ∪ B := (Finset.mem_sdiff.mp hi).2
      have hiBU : i.1 ∉ BU := by
        intro h
        exact hnot (by simp [A, h])
      have hiBT : i.1 ∉ BT := by
        intro h
        exact hnot (by simp [B, h])
      simp [f, upper, hiBU, hiBT]
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
      _ = (ENNReal.ofReal a) ^ BU.card * (ENNReal.ofReal b) ^ BT.card := by
        have hprodA : (∏ i ∈ A, f i) = (ENNReal.ofReal a) ^ A.card := by
          trans ∏ i ∈ A, ENNReal.ofReal a
          · exact Finset.prod_congr rfl (by intro i hi; exact hfA i hi)
          · simp
        have hprodB : (∏ i ∈ B, f i) = (ENNReal.ofReal b) ^ B.card := by
          trans ∏ i ∈ B, ENNReal.ofReal b
          · exact Finset.prod_congr rfl (by intro i hi; exact hfB i hi)
          · simp
        rw [hprodA, hprodB, hAcard, hBcard]
      _ = ENNReal.ofReal (a ^ BU.card * b ^ BT.card) := by
        rw [ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_pow ha0, ENNReal.ofReal_pow hb0]
        · exact pow_nonneg ha0 _
  change
    MeasureTheory.volume
        (Set.pi Set.univ fun w : β => Set.Ico (0 : ℝ) (upper w)) =
      ENNReal.ofReal (a ^ BU.card * b ^ BT.card)
  rw [Real.volume_pi_Ico]
  exact hprod
