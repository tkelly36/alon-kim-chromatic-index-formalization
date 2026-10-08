import Tablet.SamplingSplitOutsideBlockerPairedCandidateEvent

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerPairedContextCurrentInvariant]
theorem SamplingSplitOutsideBlockerPairedContextCurrentInvariant
    {V V' : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V']
    (G : SimpleGraph V) (φ : V → V') (r : V) (X : Finset V)
    {n : ℕ} (zAt : Fin n → V) (B : Fin n → Finset V)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (hzAt : Function.Injective zAt) (hβ : Function.Injective β)
    (hOutside : ∀ i, zAt i ∉ insert r X)
    (hFresh : ∀ a, ∀ y ∈ insert r X, β a ≠ φ y)
    (k : Fin n)
    (ζ ξ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)))
    (hsource : ∀ v, v ≠ zAt k →
      (v ∈ ζ.1.1 ↔ v ∈ ξ.1.1) ∧ ζ.1.2 v = ξ.1.2 v)
    (htarget : ∀ v',
      (∀ (x : {x : V // x ∈ X})
        (hz : zAt k ∉ insert r X ∧ G.Adj x.1 (zAt k)),
          v' ≠ β ⟨x, ⟨zAt k, hz⟩⟩) →
      (v' ∈ ζ.2.1 ↔ v' ∈ ξ.2.1) ∧ ζ.2.2 v' = ξ.2.2 v') :
    ∀ x : {x : V // x ∈ X},
      ζ ∈ SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
        (Finset.univ.filter (fun i => i < k))
        (Finset.univ.filter (fun i => k < i)) x ↔
      ξ ∈ SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
        (Finset.univ.filter (fun i => i < k))
        (Finset.univ.filter (fun i => k < i)) x := by
-- BODY
  intro x
  have hlocal (y : V) (hy : y ∈ insert r X) : y ≠ zAt k := by
    intro heq
    exact hOutside k (heq ▸ hy)
  have htlocal (y : V) (hy : y ∈ insert r X) :
      (φ y ∈ ζ.2.1 ↔ φ y ∈ ξ.2.1) ∧ ζ.2.2 (φ y) = ξ.2.2 (φ y) := by
    apply htarget
    intro a hz heq
    exact hFresh ⟨a, ⟨zAt k, hz⟩⟩ y hy heq.symm
  have hsx := hsource x.1 (hlocal x.1 (Finset.mem_insert_of_mem x.2))
  have htx := htlocal x.1 (Finset.mem_insert_of_mem x.2)
  have hsCore :
      (∀ y : V, y ∈ insert r X → y ∈ ζ.1.1 →
        G.Adj x.1 y → ζ.1.2 y < ζ.1.2 x.1) ↔
      (∀ y : V, y ∈ insert r X → y ∈ ξ.1.1 →
        G.Adj x.1 y → ξ.1.2 y < ξ.1.2 x.1) := by
    apply forall_congr'
    intro y
    apply forall_congr'
    intro hy
    rw [(hsource y (hlocal y hy)).1, (hsource y (hlocal y hy)).2, hsx.2]
  have htCore :
      (∀ y : V, y ∈ insert r X → φ y ∈ ζ.2.1 →
        G.Adj x.1 y → ζ.2.2 (φ y) < ζ.2.2 (φ x.1)) ↔
      (∀ y : V, y ∈ insert r X → φ y ∈ ξ.2.1 →
        G.Adj x.1 y → ξ.2.2 (φ y) < ξ.2.2 (φ x.1)) := by
    apply forall_congr'
    intro y
    apply forall_congr'
    intro hy
    rw [(htlocal y hy).1, (htlocal y hy).2, htx.2]
  unfold SamplingSplitOutsideBlockerPairedCandidateEvent
  simp only [Set.mem_setOf_eq, hsx.1, htx.1, hsCore, htCore]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    apply forall_congr'
    intro _
    apply forall_congr'
    intro hz
    have hiLt : i < k := (Finset.mem_filter.mp hi).2
    have htb := htarget (β ⟨x, ⟨zAt i, hz⟩⟩) (by
      intro a hz' heq
      have heqInc := hβ heq
      have hzEq : zAt i = zAt k := congrArg (fun b => b.2.1) heqInc
      exact (ne_of_lt hiLt) (hzAt hzEq))
    rw [htb.1, htb.2, htx.2]
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    apply forall_congr'
    intro _
    have hiGt : k < i := (Finset.mem_filter.mp hi).2
    have hsi := hsource (zAt i) (fun h => (ne_of_gt hiGt) (hzAt h))
    rw [hsi.1, hsi.2, hsx.2]
