import Tablet.Preamble

-- [TABLET NODE: KPartiteOrderedTriangleDoubleCount]
theorem KPartiteOrderedTriangleDoubleCount :
    ∀ k : ℕ, ∀ w : Fin k → Fin k → ℝ,
      (∀ i j, 0 ≤ w i j) →
      let T : Fin k → Fin k → Fin k → ℝ :=
        fun i j l => Real.sqrt (w i j * w i l * w j l)
      let U : Finset (Fin k × Fin k × Fin k) :=
        (Finset.univ.filter
          (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).sum
          (fun t => T t.1 t.2.1 t.2.2) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).sum
          (fun t => T t.1 t.2.2 t.2.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).sum
          (fun t => T t.2.1 t.1 t.2.2) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).sum
          (fun t => T t.2.1 t.2.2 t.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).sum
          (fun t => T t.2.2 t.1 t.2.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).sum
          (fun t => T t.2.2 t.2.1 t.1)) =
        6 * U.sum (fun t => T t.1 t.2.1 t.2.2) := by
-- BODY
  intro k w hw
  classical
  intro T U
  let base : Finset (Fin k × Fin k × Fin k) :=
    (Finset.univ.filter
      (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
  have h213 :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).sum
          (fun t => T t.1 t.2.2 t.2.1)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := by
    let s : Finset (Fin k × Fin k × Fin k) :=
      (Finset.univ.filter
        (fun t : Fin k × Fin k × Fin k => t.1 < t.2.2 ∧ t.2.2 < t.2.1))
    change s.sum (fun x => T x.1 x.2.2 x.2.1) =
      base.sum (fun x => T x.1 x.2.1 x.2.2)
    refine Finset.sum_bij' (fun x _hx => (x.1, x.2.2, x.2.1))
      (fun x _hx => (x.1, x.2.2, x.2.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      rfl
  have h132 :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).sum
          (fun t => T t.2.1 t.1 t.2.2)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := by
    let s : Finset (Fin k × Fin k × Fin k) :=
      (Finset.univ.filter
        (fun t : Fin k × Fin k × Fin k => t.2.1 < t.1 ∧ t.1 < t.2.2))
    change s.sum (fun x => T x.2.1 x.1 x.2.2) =
      base.sum (fun x => T x.1 x.2.1 x.2.2)
    refine Finset.sum_bij' (fun x _hx => (x.2.1, x.1, x.2.2))
      (fun x _hx => (x.2.1, x.1, x.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      rfl
  have h231 :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).sum
          (fun t => T t.2.1 t.2.2 t.1)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := by
    let s : Finset (Fin k × Fin k × Fin k) :=
      (Finset.univ.filter
        (fun t : Fin k × Fin k × Fin k => t.2.1 < t.2.2 ∧ t.2.2 < t.1))
    change s.sum (fun x => T x.2.1 x.2.2 x.1) =
      base.sum (fun x => T x.1 x.2.1 x.2.2)
    refine Finset.sum_bij' (fun x _hx => (x.2.1, x.2.2, x.1))
      (fun x _hx => (x.2.2, x.1, x.2.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      rfl
  have h312 :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).sum
          (fun t => T t.2.2 t.1 t.2.1)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := by
    let s : Finset (Fin k × Fin k × Fin k) :=
      (Finset.univ.filter
        (fun t : Fin k × Fin k × Fin k => t.2.2 < t.1 ∧ t.1 < t.2.1))
    change s.sum (fun x => T x.2.2 x.1 x.2.1) =
      base.sum (fun x => T x.1 x.2.1 x.2.2)
    refine Finset.sum_bij' (fun x _hx => (x.2.2, x.1, x.2.1))
      (fun x _hx => (x.2.1, x.2.2, x.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      rfl
  have h321 :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).sum
          (fun t => T t.2.2 t.2.1 t.1)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := by
    let s : Finset (Fin k × Fin k × Fin k) :=
      (Finset.univ.filter
        (fun t : Fin k × Fin k × Fin k => t.2.2 < t.2.1 ∧ t.2.1 < t.1))
    change s.sum (fun x => T x.2.2 x.2.1 x.1) =
      base.sum (fun x => T x.1 x.2.1 x.2.2)
    refine Finset.sum_bij' (fun x _hx => (x.2.2, x.2.1, x.1))
      (fun x _hx => (x.2.2, x.2.1, x.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      simp only [s, base, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      rfl
  have hbase :
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).sum
          (fun t => T t.1 t.2.1 t.2.2)) =
        base.sum (fun t => T t.1 t.2.1 t.2.2) := rfl
  rw [hbase, h213, h132, h231, h312, h321]
  ring
