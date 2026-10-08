import Tablet.Preamble

-- [TABLET NODE: SamplingSplitOutsideBlockerCurrentTagSeparation]
theorem SamplingSplitOutsideBlockerCurrentTagSeparation
    {V V' T A : Type*} [DecidableEq V] [DecidableEq V']
    [DecidableEq T] [Fintype A]
    (φ : V → V') (S : Finset V) (S' : Finset V')
    (hS' : S' = S.image φ)
    (s : V → T) (t : V' → T)
    (hs : Function.Injective s) (ht : Function.Injective t)
    (hoverlap : ∀ v v', s v = t v' ↔ v ∈ S ∧ φ v = v')
    (v : V) (hv : v ∉ S) (b : A → V')
    (hb : Function.Injective b) (hprivate : ∀ a, b a ∉ S') :
    let j : Option A → T := fun a => match a with
      | none => s v
      | some a => t (b a)
    let J := Finset.univ.image j
    Function.Injective j ∧
      (∀ y, s y ∈ J ↔ y = v) ∧
      (∀ y', t y' ∈ J ↔ ∃ a, b a = y') ∧
      (∀ y ∈ S, s y ∉ J) := by
-- BODY
  classical
  dsimp only
  let j : Option A → T := fun a => match a with
    | none => s v
    | some a => t (b a)
  have hsource (y') : s v ≠ t y' :=
    fun he => hv ((hoverlap v y').mp he).1
  have htarget (a : A) (y : V) : t (b a) ≠ s y := by
    intro he
    obtain ⟨hy, heq⟩ := (hoverlap y (b a)).mp he.symm
    apply hprivate a
    rw [hS']
    exact Finset.mem_image.mpr ⟨y, hy, heq⟩
  have hsrcmem (y) : s y ∈ Finset.univ.image j ↔ y = v := by
    constructor
    · intro hy
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy
      cases a with
      | none => exact (hs ha).symm
      | some a => exact (htarget a y ha).elim
    · rintro rfl
      exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
  refine ⟨?_, hsrcmem, ?_, ?_⟩
  · intro a a' he
    cases a with
    | none =>
      cases a' with
      | none => rfl
      | some a' => exact (hsource (b a') he).elim
    | some a =>
      cases a' with
      | none => exact (hsource (b a) he.symm).elim
      | some a' => exact congrArg some (hb (ht he))
  · intro y'
    constructor
    · intro hy
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy
      cases a with
      | none => exact (hsource y' ha).elim
      | some a => exact ⟨a, ht ha⟩
    · rintro ⟨a, rfl⟩
      exact Finset.mem_image.mpr ⟨some a, Finset.mem_univ _, rfl⟩
  · intro y hy hmem
    exact hv ((hsrcmem y).mp hmem ▸ hy)
