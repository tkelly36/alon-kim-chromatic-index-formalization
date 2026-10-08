import Tablet.Preamble
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Option

open scoped BigOperators

-- [TABLET NODE: FiniteSortedPaddedSlots]
theorem FiniteSortedPaddedSlots {V : Type*} [DecidableEq V]
    (s : Finset V) (w : V → ℝ) (hw : ∀ y ∈ s, 0 ≤ w y) :
    ∃ x : Fin (max 3 s.card) → Option V,
      (∀ j k y, x j = some y → x k = some y → j = k) ∧
      (∀ y, (∃ j, x j = some y) ↔ y ∈ s) ∧
      (∀ j k, j ≤ k → (x k).elim 0 w ≤ (x j).elim 0 w) ∧
      (∀ g : V → ℝ, (∑ j, (x j).elim 0 g) = ∑ y ∈ s, g y) ∧
      (∀ j : Fin 3, x (Fin.castLE (le_max_left _ _) j) = none →
        ∀ y ∈ s, ∃ k : Fin 3, x (Fin.castLE (le_max_left _ _) k) = some y) ∧
      (∀ y ∈ s, (∀ j : Fin 3, x (Fin.castLE (le_max_left _ _) j) ≠ some y) →
        w y ≤ (x (Fin.castLE (le_max_left _ _) 2)).elim 0 w) := by
-- BODY
  classical
  let e : Fin s.card ≃ s := (Finset.equivFinOfCardEq rfl).symm
  let p := Tuple.sort (α := OrderDual ℝ) (fun i : Fin s.card => w (e i))
  let t : Fin s.card ≃ s := p.trans e
  have ht : ∀ i j : Fin s.card, i ≤ j → w (t j) ≤ w (t i) := by
    intro i j hij
    exact Tuple.monotone_sort (α := OrderDual ℝ) (fun i : Fin s.card => w (e i)) hij
  let x : Fin (max 3 s.card) → Option V := fun j =>
    if h : j.val < s.card then some (t ⟨j.val, h⟩).val else none
  have hx (j) (h : j.val < s.card) : x j = some (t ⟨j.val, h⟩).val := by
    simp [x, h]
  have hn (j) (h : ¬ j.val < s.card) : x j = none := by simp [x, h]
  have hreal (j y) (h : x j = some y) :
      ∃ hj : j.val < s.card, (t ⟨j.val, hj⟩).val = y := by
    by_cases hj : j.val < s.card
    · exact ⟨hj, Option.some.inj ((hx j hj).symm.trans h)⟩
    · simp [hn j hj] at h
  have hi : ∀ j k y, x j = some y → x k = some y → j = k := by
    intro j k y hj hk
    obtain ⟨hj', hjy⟩ := hreal j y hj
    obtain ⟨hk', hky⟩ := hreal k y hk
    have hh := t.injective (Subtype.ext (hjy.trans hky.symm))
    exact Fin.ext (congrArg (fun i : Fin s.card => i.val) hh)
  have hc : ∀ y, (∃ j, x j = some y) ↔ y ∈ s := by
    intro y
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨hj', rfl⟩ := hreal j y hj
      exact (t _).property
    · intro hy
      let i := t.symm ⟨y, hy⟩
      refine ⟨⟨i.val, lt_of_lt_of_le i.isLt (le_max_right _ _)⟩, ?_⟩
      simpa [i] using hx ⟨i.val, lt_of_lt_of_le i.isLt (le_max_right _ _)⟩ i.isLt
  have hm : ∀ j k, j ≤ k → (x k).elim 0 w ≤ (x j).elim 0 w := by
    intro j k hjk
    by_cases hk : k.val < s.card
    · have hj : j.val < s.card := lt_of_le_of_lt hjk hk
      simpa [hx j hj, hx k hk] using ht ⟨j.val, hj⟩ ⟨k.val, hk⟩ hjk
    · rw [hn k hk]
      by_cases hj : j.val < s.card
      · simpa [hx j hj] using hw _ (t ⟨j.val, hj⟩).property
      · simp [hn j hj]
  refine ⟨x, hi, hc, hm, ?_, ?_, ?_⟩
  · intro g
    have hu : Finset.univ.biUnion (fun j => (x j).toFinset) = s := by
      ext y
      simpa [Option.mem_def] using hc y
    have hd : (↑(Finset.univ : Finset (Fin (max 3 s.card))) :
        Set (Fin (max 3 s.card))).Pairwise
        (fun j k => Disjoint (x j).toFinset (x k).toFinset) := by
      intro j _ k _ hjk
      apply Finset.disjoint_left.mpr
      intro y hj hk
      exact hjk (hi j k y (by simpa [Option.mem_def] using hj)
        (by simpa [Option.mem_def] using hk))
    conv_rhs => rw [← hu, Finset.sum_biUnion hd]
    apply Finset.sum_congr rfl
    intro j _
    cases x j <;> simp
  · intro j hj y hy
    have hjcard : s.card ≤ j.val := by
      by_contra h
      have hh := hx (Fin.castLE (le_max_left _ _) j) (by simpa using Nat.lt_of_not_ge h)
      rw [hj] at hh
      contradiction
    let i := t.symm ⟨y, hy⟩
    have hi3 : i.val < 3 := lt_of_lt_of_le i.isLt (le_trans hjcard (Nat.le_of_lt j.isLt))
    refine ⟨⟨i.val, hi3⟩, ?_⟩
    simpa [i] using hx (Fin.castLE (le_max_left _ _) ⟨i.val, hi3⟩) i.isLt
  · intro y hy hnot
    obtain ⟨j, hj⟩ := (hc y).mpr hy
    have hj3 : 3 ≤ j.val := by
      by_contra h
      exact hnot ⟨j.val, Nat.lt_of_not_ge h⟩ (by simpa using hj)
    have hh := hm (Fin.castLE (le_max_left _ _) 2) j (by simpa using (show 2 ≤ j.val by omega))
    simpa [hj] using hh
