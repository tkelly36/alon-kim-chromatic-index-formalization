import Tablet.Preamble

universe u

-- [TABLET NODE: FiniteEvenTypePairing]
theorem FiniteEvenTypePairing :
    ∀ {α : Type u} [Fintype α], Even (Fintype.card α) →
      ∃ (P : Type u) (_ : Fintype P) (pair : P → Fin 2 → α),
        Function.Bijective (fun x : P × Fin 2 => pair x.1 x.2) := by
-- BODY
  intro α inst hEven
  classical
  rcases hEven with ⟨n, hn⟩
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let P : Type u := ULift.{u, 0} (Fin n)
  let instP : Fintype P := inferInstance
  let pair : P → Fin 2 → α := fun p i => e.symm ⟨2 * p.down.val + i.val, by
    rw [hn]
    have hp : p.down.val < n := p.down.isLt
    have hi : i.val < 2 := i.isLt
    omega⟩
  refine ⟨P, instP, pair, ?_⟩
  constructor
  · rintro ⟨p, i⟩ ⟨q, j⟩ h
    dsimp [pair] at h
    have hfin : (⟨2 * p.down.val + i.val, by
      rw [hn]
      have hp : p.down.val < n := p.down.isLt
      have hi : i.val < 2 := i.isLt
      omega⟩ : Fin (Fintype.card α)) =
        ⟨2 * q.down.val + j.val, by
          rw [hn]
          have hq : q.down.val < n := q.down.isLt
          have hj : j.val < 2 := j.isLt
          omega⟩ := by
      exact e.symm.injective h
    have hnat : 2 * p.down.val + i.val = 2 * q.down.val + j.val := congrArg Fin.val hfin
    have hmod_eq : i.val % 2 = j.val % 2 := by
      have := congrArg (fun m : ℕ => m % 2) hnat
      simpa [Nat.add_mod, Nat.mul_mod_right] using this
    have hmod : i.val = j.val := by
      have hi : i.val < 2 := i.isLt
      have hj : j.val < 2 := j.isLt
      omega
    have hpval : p.down.val = q.down.val := by
      omega
    have hi_eq : i = j := Fin.ext hmod
    have hp_eq : p = q := by
      cases p
      cases q
      congr
      exact Fin.ext hpval
    cases hp_eq
    cases hi_eq
    rfl
  · intro a
    let k : Fin (Fintype.card α) := e a
    have hklt : k.val < 2 * n := by
      have := k.isLt
      omega
    let p : P := ULift.up ⟨k.val / 2, by omega⟩
    let i : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by omega)⟩
    refine ⟨(p, i), ?_⟩
    dsimp [pair, p, i]
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    simp
    omega
