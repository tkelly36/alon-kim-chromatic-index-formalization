import Tablet.SamplingFiniteCoordinateMarginalCellLaw
import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingNonadjacentPairOrderedChamberMass
import Tablet.SamplingNonadjacentPairOrderedChamberDiagonalNull
import Tablet.SamplingNonadjacentPairOrderedChamberBoundaryNull

open BigOperators

-- [TABLET NODE: SamplingNonadjacentPairOrderedChamberProductLaw]
theorem SamplingNonadjacentPairOrderedChamberProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance))
    (p : ℝ) (u v : V) (uOnly vBlock : Finset V)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (huv : u ≠ v)
    (hu_not : u ∉ uOnly ∪ vBlock)
    (hv_not : v ∉ uOnly ∪ vBlock)
    (hdisj : Disjoint uOnly vBlock)
    (hν_atom : ∀ A : Finset V,
      ν {ω | ω.1 = A} =
        ENNReal.ofReal
          (p ^ A.card *
            (1 - p) ^ ((Finset.univ : Finset V).card - A.card)))
    (hν_cube : ∀ A : Finset V,
      ν {ω | ω.1 = A ∧ ∀ q : V, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1} =
        ν {ω | ω.1 = A})
    (hν_rect : ∀ A : Finset V, ∀ t : V → ℝ,
      (∀ q : V, t q ∈ Set.Icc (0 : ℝ) 1) →
        ν {ω |
          ω.1 = A ∧ ∀ q : V, 0 ≤ ω.2 q ∧ ω.2 q ≤ t q} =
          ν {ω | ω.1 = A} * ENNReal.ofReal (∏ q : V, t q)) :
    ν {ω |
        u ∈ ω.1 ∧ v ∈ ω.1 ∧
          (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
                ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v} =
      ENNReal.ofReal
        (∫ a in (0 : ℝ)..1,
          ∫ b in (0 : ℝ)..a,
            p ^ 2 *
              (((1 - p) + p * a) ^ uOnly.card *
                ((1 - p) + p * b) ^ vBlock.card)) ∧
    ν {ω |
        u ∈ ω.1 ∧ v ∈ ω.1 ∧
          (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
            ω.2 u = ω.2 v} = 0 ∧
    (∀ z : V, z ∈ uOnly ∪ vBlock →
      ν {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧ z ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              (ω.2 z = ω.2 u ∨ ω.2 z = ω.2 v)} = 0) := by
-- BODY
  exact
    ⟨SamplingNonadjacentPairOrderedChamberMass
        ν p u v uOnly vBlock hp0 hp1 huv hu_not hv_not hdisj hν_atom hν_cube hν_rect,
      SamplingNonadjacentPairOrderedChamberDiagonalNull
        ν p u v hp0 hp1 huv hν_atom hν_cube hν_rect,
      SamplingNonadjacentPairOrderedChamberBoundaryNull
        ν p u v uOnly vBlock hp0 hp1 huv hu_not hv_not hν_atom hν_cube hν_rect⟩
