import Tablet.Preamble

universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualCoordinatePackage]
theorem SamplingSplitOutsideBlockerActualCoordinatePackage :
    ∀ {V V' : Type u} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ G' : SimpleGraph V', [DecidableRel G'.Adj] →
          ∀ (φ : V → V') (r : V) (X : Finset V),
            Function.Injective φ →
            ∀ (β :
              (Σ x : {x : V // x ∈ X},
                {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V'),
              Function.Injective β →
              (∀ x : V, ∀ hx : x ∈ X,
                ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                ∀ y : V, y ∈ insert r X →
                  β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ ≠ φ y) →
              (∀ x : V, ∀ hx : x ∈ X,
                ∀ z : V, ∀ hz : z ∉ insert r X ∧ G.Adj x z,
                  G'.Adj (φ x)
                    (β ⟨⟨x, hx⟩, ⟨z, hz⟩⟩)) →
              ∃ (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
                (sourceCoord sourceExtensionCoord : Finset V)
                (targetCommonCoord targetExtensionCoord targetCoord : Finset V'),
                (∀ k : Fin n,
                  zAt k ∉ insert r X ∧
                    (∃ x : V, x ∈ X ∧ G.Adj x (zAt k))) ∧
                (∀ z : V, z ∉ insert r X →
                  (∃ x : V, x ∈ X ∧ G.Adj x z) →
                    ∃ k : Fin n, zAt k = z) ∧
                (∀ k : Fin n, ∀ x : V,
                  x ∈ B k ↔ x ∈ X ∧ G.Adj x (zAt k)) ∧
                (∀ k : Fin n, zAt k ∈ sourceExtensionCoord) ∧
                Disjoint sourceCoord sourceExtensionCoord ∧
                (∀ x : V, x ∈ insert r X → x ∈ sourceCoord) ∧
                targetCommonCoord = sourceCoord.image φ ∧
                Disjoint targetCommonCoord targetExtensionCoord ∧
                targetCoord = targetCommonCoord ∪ targetExtensionCoord ∧
                (∀ x : V, x ∈ insert r X → φ x ∈ targetCommonCoord) ∧
                (∀ k : Fin n, ∀ x : V, ∀ hx : x ∈ X,
                  ∀ hz : zAt k ∉ insert r X ∧ G.Adj x (zAt k),
                    β ⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩ ∈ targetExtensionCoord) ∧
                Function.Injective zAt := by
-- BODY
  classical
  intro V V' _ _ _ _ G _ G' _ φ r X hφ β hβ hfresh hadj
  let Z : Finset V :=
    Finset.univ.filter
      (fun z : V => z ∉ insert r X ∧ ∃ x : V, x ∈ X ∧ G.Adj x z)
  let zAt : Fin (Fintype.card {z : V // z ∈ Z}) → V :=
    fun k => ((Fintype.equivFin {z : V // z ∈ Z}).symm k).1
  refine
    ⟨Fintype.card {z : V // z ∈ Z}, zAt,
      (fun k => X.filter (fun x : V => G.Adj x (zAt k))),
      insert r X, Z, (insert r X).image φ, Finset.univ.image β,
      (insert r X).image φ ∪ Finset.univ.image β, ?_⟩
  constructor
  · intro k
    have hzmem : zAt k ∈ Z := ((Fintype.equivFin {z : V // z ∈ Z}).symm k).2
    exact (Finset.mem_filter.mp hzmem).2
  constructor
  · intro z hzoutside hneighbor
    have hzmem : z ∈ Z := by
      change z ∈
        Finset.univ.filter
          (fun z : V => z ∉ insert r X ∧ ∃ x : V, x ∈ X ∧ G.Adj x z)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ z, hzoutside, hneighbor⟩
    refine ⟨(Fintype.equivFin {z : V // z ∈ Z}) ⟨z, hzmem⟩, ?_⟩
    simp [zAt]
  constructor
  · intro k x
    simp [zAt]
  constructor
  · intro k
    exact ((Fintype.equivFin {z : V // z ∈ Z}).symm k).2
  constructor
  · rw [Finset.disjoint_left]
    intro z hzCommon hzExt
    exact (Finset.mem_filter.mp hzExt).2.1 hzCommon
  constructor
  · intro x hx
    exact hx
  constructor
  · rfl
  constructor
  · rw [Finset.disjoint_left]
    intro a haCommon haExt
    rw [Finset.mem_image] at haCommon haExt
    rcases haCommon with ⟨y, hy, rfl⟩
    rcases haExt with ⟨inc, hincMem, hinc⟩
    rcases inc with ⟨x, z⟩
    exact hfresh x.1 x.2 z.1 z.2 y hy hinc
  constructor
  · rfl
  constructor
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  constructor
  · intro k x hx hz
    refine Finset.mem_image.mpr ?_
    exact ⟨⟨⟨x, hx⟩, ⟨zAt k, hz⟩⟩, Finset.mem_univ _, rfl⟩
  · intro i j hij
    dsimp [zAt] at hij
    have hsub :
        (Fintype.equivFin {z : V // z ∈ Z}).symm i =
          (Fintype.equivFin {z : V // z ∈ Z}).symm j :=
      Subtype.ext hij
    have hfin :=
      congrArg (Fintype.equivFin {z : V // z ∈ Z}) hsub
    simpa using hfin
