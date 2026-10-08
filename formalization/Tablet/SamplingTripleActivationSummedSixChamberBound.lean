import Tablet.RandomIndependentSetSampling
import Tablet.SamplingActivationENNRealWeightedSumConversion
import Tablet.SamplingFiniteSetActivationPartition
import Tablet.SamplingFiniteSetPushForwardEvent
import Tablet.SamplingTripleActivationChamberSum
import Tablet.SamplingTripleFixedActivationSixChamberAssembly

open BigOperators

set_option maxHeartbeats 2000000

-- [TABLET NODE: SamplingTripleActivationSummedSixChamberBound]
theorem SamplingTripleActivationSummedSixChamberBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ) (gamma : ℝ)
    (μ : Finset V → ℝ)
    (hsample : RandomIndependentSetSampling G Delta gamma μ)
    (hDelta_pos : 0 < Delta)
    (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab_ind : ¬ G.Adj a b) (hac_ind : ¬ G.Adj a c) (hbc_ind : ¬ G.Adj b c) :
    let Q : Finset V := {a, b, c}
    let orders : Finset (V × V × V) :=
      {((a, b, c) : V × V × V), (a, c, b), (b, a, c),
        (b, c, a), (c, a, b), (c, b, a)}
    let fullWeight : V × V × V → ℝ := fun t =>
      (1 / (Delta : ℝ) ^ 3) *
        ∫ z in (0 : ℝ)..gamma,
          ∫ y in z..gamma,
            ∫ x in y..gamma,
              (1 - x / (Delta : ℝ)) ^
                  (((Finset.univ : Finset V).filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ G.Adj t.1 w).card) *
                (1 - y / (Delta : ℝ)) ^
                  (((Finset.univ : Finset V).filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                      ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                  (1 - z / (Delta : ℝ)) ^
                    (((Finset.univ : Finset V).filter fun w : V =>
                      w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                        ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧
                          G.Adj t.2.2 w).card)
    ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
      ENNReal.ofReal (∑ t ∈ orders, fullWeight t) := by
-- BODY
  classical
  intro Q orders fullWeight
  rcases hsample.2 with ⟨hsample_left, hν_exists⟩
  rcases hsample_left with ⟨hμ_nonneg, hsample_left⟩
  rcases hsample_left with ⟨_hμ_total, _hpair⟩
  rcases hν_exists with ⟨ν, hν_rest⟩
  rcases hν_rest with ⟨_hν_univ, hν_rest⟩
  rcases hν_rest with ⟨hνatom, hν_rest⟩
  rcases hν_rest with ⟨hcube, hν_rest⟩
  rcases hν_rest with ⟨hlower_rect, hν_rest⟩
  rcases hν_rest with ⟨_hone_vertex, hν_rest⟩
  rcases hν_rest with ⟨hpush, _hind⟩
  let atom : Finset V → ℝ := fun A =>
    (gamma / (Delta : ℝ)) ^ A.card *
      (1 - gamma / (Delta : ℝ)) ^ ((Finset.univ : Finset V).card - A.card)
  let atomWeight : Finset V → V × V × V → ℝ := fun A t =>
    (1 / gamma ^ 3) *
      ∫ z in (0 : ℝ)..gamma,
        ∫ y in z..gamma,
          ∫ x in y..gamma,
            (1 - x / gamma) ^
                ((A.filter fun w : V =>
                  w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧ G.Adj t.1 w).card) *
              (1 - y / gamma) ^
                ((A.filter fun w : V =>
                  w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                    ¬ G.Adj t.1 w ∧ G.Adj t.2.1 w).card) *
                (1 - z / gamma) ^
                  ((A.filter fun w : V =>
                    w ∉ ({t.1, t.2.1, t.2.2} : Finset V) ∧
                      ¬ G.Adj t.1 w ∧ ¬ G.Adj t.2.1 w ∧
                        G.Adj t.2.2 w).card)
  have hgamma_pos : 0 < gamma := hsample.1
  have hgamma_le_delta : gamma ≤ (Delta : ℝ) :=
    RandomIndependentSetSamplingGammaLeDelta (G := G) (Delta := Delta) (gamma := gamma)
      (μ := μ) ⟨a⟩ hDelta_pos hsample
  have hDelta_real_pos : 0 < (Delta : ℝ) := by exact_mod_cast hDelta_pos
  have hatom_nonneg (A : Finset V) : 0 ≤ atom A := by
    have hp : 0 ≤ gamma / (Delta : ℝ) := div_nonneg hgamma_pos.le hDelta_real_pos.le
    have hq : 0 ≤ 1 - gamma / (Delta : ℝ) := by
      rw [sub_nonneg, div_le_one hDelta_real_pos]
      exact hgamma_le_delta
    exact mul_nonneg (pow_nonneg hp _) (pow_nonneg hq _)
  have hpush_Q :
      ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) =
        ν {ω |
          Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} :=
    SamplingFiniteSetPushForwardEvent (G := G) (μ := μ) (ν := ν)
      hμ_nonneg hpush Q
  have hpartition :
      ν {ω |
          Q ⊆
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
        ∑ A : Finset V,
          if Q ⊆ A then
            ν {ω |
              ω.1 = A ∧
                ∀ q : V, q ∈ Q →
                  ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q}
          else 0 :=
    (SamplingFiniteSetActivationPartition (G := G) (ν := ν) Q).1
  have hQmem_a : a ∈ Q := by simp [Q]
  have hQmem_b : b ∈ Q := by simp [Q]
  have hQmem_c : c ∈ Q := by simp [Q]
  have hfixed (A : Finset V) (hQA : Q ⊆ A) :
      ν {ω |
          ω.1 = A ∧
            ∀ q : V, q ∈ Q →
              ∀ w : V, w ∈ A → G.Adj q w → ω.2 w < ω.2 q} ≤
        (∑ t ∈ orders,
          ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)) ∧
        ∀ t ∈ orders, 0 ≤ atomWeight A t := by
    have haA : a ∈ A := hQA hQmem_a
    have hbA : b ∈ A := hQA hQmem_b
    have hcA : c ∈ A := hQA hQmem_c
    simpa [Q, orders, atomWeight] using
      SamplingTripleFixedActivationSixChamberAssembly (G := G) (Delta := Delta)
        (gamma := gamma) (ν := ν) (A := A) (a := a) (b := b) (c := c)
        hgamma_pos haA hbA hcA hab hac hbc hab_ind hac_ind hbc_ind (hcube A)
        (hlower_rect A)
  have hfirst_bound :
      ENNReal.ofReal (∑ S : Finset V, if Q ⊆ S then μ S else 0) ≤
        ∑ A : Finset V,
          if Q ⊆ A then
            ∑ t ∈ orders,
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
          else 0 := by
    rw [hpush_Q, hpartition]
    apply Finset.sum_le_sum
    intro A _hA
    by_cases hQA : Q ⊆ A
    · simpa [hQA] using (hfixed A hQA).1
    · simp [hQA]
  have hsum_comm :
      (∑ A : Finset V,
          if Q ⊆ A then
            ∑ t ∈ orders,
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
          else 0) =
        ∑ t ∈ orders,
          ∑ A : Finset V,
            if Q ⊆ A then
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
            else 0 := by
    calc
      (∑ A : Finset V,
          if Q ⊆ A then
            ∑ t ∈ orders,
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
          else 0)
          = ∑ A : Finset V,
              ∑ t ∈ orders,
                if Q ⊆ A then
                  ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
                else 0 := by
              apply Finset.sum_congr rfl
              intro A _hA
              by_cases hQA : Q ⊆ A <;> simp [hQA]
      _ = ∑ t ∈ orders,
            ∑ A : Finset V,
              if Q ⊆ A then
                ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
              else 0 := by
              rw [Finset.sum_comm]
  have hconverted (t : V × V × V) (ht : t ∈ orders) :
      (∑ A : Finset V,
        if Q ⊆ A then
          ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
        else 0) =
        ENNReal.ofReal
          (∑ A : Finset V,
            if Q ⊆ A then atom A * atomWeight A t else 0) := by
    exact
      SamplingActivationENNRealWeightedSumConversion (ν := ν) (Q := Q)
        (atom := atom) (F := fun A => atomWeight A t)
        (by intro A; simpa [atom] using hνatom A)
        hatom_nonneg
        (by
          intro A hQA
          exact (hfixed A hQA).2 t ht)
  have hchamber (t : V × V × V) (ht : t ∈ orders) :
      (∑ A : Finset V,
        if Q ⊆ A then atom A * atomWeight A t else 0) = fullWeight t := by
    rcases (by simpa [orders] using ht) with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [Q, atom, atomWeight, fullWeight] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos a b c hab hac hbc
    · have hsub (A : Finset V) : ({a, c, b} : Finset V) ⊆ A ↔ Q ⊆ A := by
        simp [Q, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]
      simpa [Q, atom, atomWeight, fullWeight, hsub, or_assoc, or_left_comm, or_comm,
        and_assoc, and_left_comm, and_comm] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos a c b hac hab (Ne.symm hbc)
    · have hsub (A : Finset V) : ({b, a, c} : Finset V) ⊆ A ↔ Q ⊆ A := by
        simp [Q, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]
      simpa [Q, atom, atomWeight, fullWeight, hsub, or_assoc, or_left_comm, or_comm,
        and_assoc, and_left_comm, and_comm] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos b a c (Ne.symm hab) hbc hac
    · have hsub (A : Finset V) : ({b, c, a} : Finset V) ⊆ A ↔ Q ⊆ A := by
        simp [Q, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]
      simpa [Q, atom, atomWeight, fullWeight, hsub, or_assoc, or_left_comm, or_comm,
        and_assoc, and_left_comm, and_comm] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos b c a hbc (Ne.symm hab) (Ne.symm hac)
    · have hsub (A : Finset V) : ({c, a, b} : Finset V) ⊆ A ↔ Q ⊆ A := by
        simp [Q, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]
      simpa [Q, atom, atomWeight, fullWeight, hsub, or_assoc, or_left_comm, or_comm,
        and_assoc, and_left_comm, and_comm] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos c a b (Ne.symm hac) (Ne.symm hbc) hab
    · have hsub (A : Finset V) : ({c, b, a} : Finset V) ⊆ A ↔ Q ⊆ A := by
        simp [Q, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]
      simpa [Q, atom, atomWeight, fullWeight, hsub, or_assoc, or_left_comm, or_comm,
        and_assoc, and_left_comm, and_comm] using
        SamplingTripleActivationChamberSum (G := G) (Delta := Delta) (gamma := gamma)
          (μ := μ) hsample hDelta_pos c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab)
  have hfull_nonneg (t : V × V × V) (ht : t ∈ orders) : 0 ≤ fullWeight t := by
    rw [← hchamber t ht]
    apply Finset.sum_nonneg
    intro A _hA
    by_cases hQA : Q ⊆ A
    · exact by
        simpa [hQA] using mul_nonneg (hatom_nonneg A) ((hfixed A hQA).2 t ht)
    · simp [hQA]
  have hsecond_bound :
      (∑ A : Finset V,
          if Q ⊆ A then
            ∑ t ∈ orders,
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
          else 0) ≤
        ENNReal.ofReal (∑ t ∈ orders, fullWeight t) := by
    rw [hsum_comm]
    calc
      (∑ t ∈ orders,
          ∑ A : Finset V,
            if Q ⊆ A then
              ν {ω | ω.1 = A} * ENNReal.ofReal (atomWeight A t)
            else 0)
          = ∑ t ∈ orders,
              ENNReal.ofReal
                (∑ A : Finset V,
                  if Q ⊆ A then atom A * atomWeight A t else 0) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [hconverted t ht]
      _ = ∑ t ∈ orders, ENNReal.ofReal (fullWeight t) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [hchamber t ht]
      _ = ENNReal.ofReal (∑ t ∈ orders, fullWeight t) := by
              rw [ENNReal.ofReal_sum_of_nonneg]
              intro t ht
              exact hfull_nonneg t ht
      _ ≤ ENNReal.ofReal (∑ t ∈ orders, fullWeight t) := le_rfl
  exact le_trans hfirst_bound hsecond_bound
