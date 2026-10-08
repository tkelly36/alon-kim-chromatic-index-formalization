import Tablet.FiniteProbabilityMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open BigOperators

-- [TABLET NODE: RandomIndependentSetSampling]
def RandomIndependentSetSampling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (μ : Finset V → ℝ) : Prop :=
-- BODY
  0 < gamma ∧
  ((∀ S : Finset V, 0 ≤ μ S) ∧ (∑ S : Finset V, μ S) = 1 ∧
    (∀ _hregular : ∀ z : V, G.degree z = Delta,
      ∀ u v : V, u ≠ v → ¬ G.Adj u v →
        (∑ S : Finset V, if ({u, v} : Finset V) ⊆ S then μ S else 0) =
          (2 / (Delta : ℝ)^2) *
            ∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 - x / (Delta : ℝ)) ^
                    (Delta -
                      (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) ∧
    ∃ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
      ν Set.univ = 1 ∧
        (∀ A : Finset V,
          ν {ω | ω.1 = A} =
            ENNReal.ofReal
              ((gamma / (Delta : ℝ)) ^ A.card *
                (1 - gamma / (Delta : ℝ)) ^
                  ((Finset.univ : Finset V).card - A.card))) ∧
        (∀ A : Finset V,
          ν {ω | ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
            ν {ω | ω.1 = A}) ∧
        (∀ A : Finset V, ∀ t : V → ℝ,
          (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
            ν {ω |
              ω.1 = A ∧
                ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
              ν {ω | ω.1 = A} *
                ENNReal.ofReal (∏ v : V, t v)) ∧
        (∀ A : Finset V, ∀ v : V, v ∈ A →
          ν {ω |
            ω.1 = A ∧
              (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
                ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
            ν {ω | ω.1 = A} *
              ENNReal.ofReal
                (∫ a in (0 : ℝ)..1,
                  a ^
                    ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))) ∧
        (∀ S : Finset V,
          ENNReal.ofReal (μ S) =
            ν {ω |
              S =
                (Finset.univ.filter fun v : V =>
                  v ∈ ω.1 ∧
                    ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v)}) ∧
        ∀ S : Finset V, μ S ≠ 0 →
          ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v
