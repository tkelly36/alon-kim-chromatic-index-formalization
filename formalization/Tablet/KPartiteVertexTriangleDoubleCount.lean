import Tablet.Preamble

set_option maxHeartbeats 2000000

-- [TABLET NODE: KPartiteVertexTriangleDoubleCount]
theorem KPartiteVertexTriangleDoubleCount :
    ∀ k : ℕ, ∀ w : Fin k → Fin k → ℝ,
      let edge : Fin k → Fin k → ℝ :=
        fun a b => if a < b then w a b else if b < a then w b a else 0
      let triples : Finset (Fin k × Fin k × Fin k) :=
        (Finset.univ.filter
          (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (∑ i : Fin k,
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
          (fun p =>
            Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))) =
      3 * triples.sum
        (fun t =>
          Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2)) := by
-- BODY
  intro k w edge triples
  classical
  let flat : Finset (Fin k × Fin k × Fin k) :=
    (Finset.univ.filter
      (fun x : Fin k × Fin k × Fin k =>
        x.2.1 < x.2.2 ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2))
  have hdep_flat :
      (∑ i : Fin k,
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
          (fun p =>
            Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))) =
      flat.sum
        (fun x =>
          Real.sqrt
            (edge x.1 x.2.1 * edge x.1 x.2.2 * edge x.2.1 x.2.2)) := by
    calc
      (∑ i : Fin k,
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
          (fun p =>
            Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))) =
        (∑ x : Sigma (fun i : Fin k => ({j : Fin k // j ≠ i} × {j : Fin k // j ≠ i})),
          if x.2.1 < x.2.2 then
            Real.sqrt
              (edge x.1 x.2.1.1 * edge x.1 x.2.2.1 * edge x.2.1.1 x.2.2.1)
          else 0) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro i hi
          simp only
          rw [Finset.sum_filter]
      _ = flat.sum
          (fun x =>
            Real.sqrt
              (edge x.1 x.2.1 * edge x.1 x.2.2 * edge x.2.1 x.2.2)) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_bij'
          (fun x _hx => (x.1, x.2.1.1, x.2.2.1))
          (fun x hx => ⟨x.1, (⟨x.2.1, by
            simp [flat] at hx
            intro h
            exact hx.2.1 h.symm
          ⟩, ⟨x.2.2, by
            simp [flat] at hx
            intro h
            exact hx.2.2 h.symm
          ⟩)⟩) ?_ ?_ ?_ ?_ ?_
        · intro x hx
          simp [flat] at hx ⊢
          exact ⟨hx, by
            intro h
            exact x.2.1.2 h.symm, by
            intro h
            exact x.2.2.2 h.symm⟩
        · intro x hx
          simp [flat] at hx ⊢
          exact hx.1
        · intro x hx
          ext <;> rfl
        · intro x hx
          simp [flat] at hx
          rfl
        · intro x hx
          rfl
  let f : Fin k × Fin k × Fin k → ℝ :=
    fun x =>
      Real.sqrt (edge x.1 x.2.1 * edge x.1 x.2.2 * edge x.2.1 x.2.2)
  let g : Fin k × Fin k × Fin k → ℝ :=
    fun x =>
      Real.sqrt (w x.1 x.2.1 * w x.1 x.2.2 * w x.2.1 x.2.2)
  let s1 := flat.filter (fun x : Fin k × Fin k × Fin k => x.1 < x.2.1)
  let rest := flat.filter (fun x : Fin k × Fin k × Fin k => ¬ x.1 < x.2.1)
  let s2 := rest.filter (fun x : Fin k × Fin k × Fin k => x.1 < x.2.2)
  let s3 := rest.filter (fun x : Fin k × Fin k × Fin k => ¬ x.1 < x.2.2)
  have hsplit : flat.sum f = s1.sum f + s2.sum f + s3.sum f := by
    have h1 := Finset.sum_filter_add_sum_filter_not
      (s := flat) (p := fun x : Fin k × Fin k × Fin k => x.1 < x.2.1) (f := f)
    have h2 := Finset.sum_filter_add_sum_filter_not
      (s := rest) (p := fun x : Fin k × Fin k × Fin k => x.1 < x.2.2) (f := f)
    have h1' : flat.sum f = s1.sum f + rest.sum f := by
      simpa [s1, rest] using h1.symm
    have h2' : rest.sum f = s2.sum f + s3.sum f := by
      simpa [s2, s3] using h2.symm
    rw [h1', h2']
    ring
  have hs1 : s1.sum f = triples.sum g := by
    change s1.sum f = triples.sum g
    refine Finset.sum_bij' (fun x _hx => x) (fun x _hx => x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp [s1, flat, triples] at hx ⊢
      exact ⟨hx.2, hx.1.1⟩
    · intro x hx
      simp [s1, flat, triples] at hx ⊢
      exact ⟨⟨hx.2, ne_of_lt hx.1, ne_of_lt (lt_trans hx.1 hx.2)⟩, hx.1⟩
    · intro x hx
      rfl
    · intro x hx
      rfl
    · intro x hx
      simp [s1, flat] at hx
      have hil : x.1 < x.2.2 := lt_trans hx.2 hx.1.1
      simp [edge, hx.2, hil, hx.1.1]
  have hs2 : s2.sum f = triples.sum g := by
    change s2.sum f = triples.sum g
    refine Finset.sum_bij' (fun x _hx => (x.2.1, x.1, x.2.2))
      (fun x _hx => (x.2.1, x.1, x.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp [s2, rest, flat, triples] at hx ⊢
      exact ⟨lt_of_le_of_ne hx.1.2 (by
        intro h
        exact hx.1.1.2.1 h.symm), hx.2⟩
    · intro x hx
      simp [s2, rest, flat, triples] at hx ⊢
      exact ⟨⟨⟨lt_trans hx.1 hx.2, by
        intro h
        exact ne_of_lt hx.1 h.symm, by
        intro h
        exact ne_of_lt hx.2 h⟩, le_of_lt hx.1⟩, hx.2⟩
    · intro x hx
      ext <;> rfl
    · intro x hx
      rfl
    · intro x hx
      simp [s2, rest, flat] at hx
      have hji : x.2.1 < x.1 :=
        lt_of_le_of_ne hx.1.2 (by
          intro h
          exact hx.1.1.2.1 h.symm)
      have hnot_ij : ¬ x.1 < x.2.1 := not_lt.mpr hx.1.2
      simp [edge, hx.1.1.1, hji, hx.2, hnot_ij]
      ring_nf
  have hs3 : s3.sum f = triples.sum g := by
    change s3.sum f = triples.sum g
    refine Finset.sum_bij' (fun x _hx => (x.2.1, x.2.2, x.1))
      (fun x _hx => (x.2.2, x.1, x.2.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp [s3, rest, flat, triples] at hx ⊢
      have hli : x.2.2 < x.1 := lt_of_le_of_ne hx.2 (by
        intro h
        exact hx.1.1.2.2 h.symm)
      exact ⟨hx.1.1.1, hli⟩
    · intro x hx
      simp [s3, rest, flat, triples] at hx ⊢
      exact ⟨⟨⟨hx.1, by
        intro h
        exact ne_of_lt (lt_trans hx.1 hx.2) h.symm, by
        intro h
        exact ne_of_lt hx.2 h.symm⟩,
        le_trans (le_of_lt hx.1) (le_of_lt hx.2)⟩, le_of_lt hx.2⟩
    · intro x hx
      ext <;> rfl
    · intro x hx
      rfl
    · intro x hx
      simp [s3, rest, flat] at hx
      have hji : x.2.1 < x.1 :=
        lt_trans hx.1.1.1 (lt_of_le_of_ne hx.2 (by
          intro h
          exact hx.1.1.2.2 h.symm))
      have hli : x.2.2 < x.1 := lt_of_le_of_ne hx.2 (by
        intro h
        exact hx.1.1.2.2 h.symm)
      have hnot_ij : ¬ x.1 < x.2.1 := not_lt.mpr hx.1.2
      have hnot_il : ¬ x.1 < x.2.2 := not_lt.mpr hx.2
      simp [edge, hx.1.1.1, hji, hli, hnot_ij, hnot_il]
      ring_nf
  calc
    (∑ i : Fin k,
      let others := {j : Fin k // j ≠ i}
      let pairsOther : Finset (others × others) :=
        (Finset.univ.filter (fun p : others × others => p.1 < p.2))
      pairsOther.sum
        (fun p =>
          Real.sqrt
            (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1)))
        = flat.sum f := hdep_flat
    _ = s1.sum f + s2.sum f + s3.sum f := hsplit
    _ = triples.sum g + triples.sum g + triples.sum g := by rw [hs1, hs2, hs3]
    _ = 3 * triples.sum g := by ring
