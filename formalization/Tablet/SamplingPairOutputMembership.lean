import Tablet.RandomIndependentSetSampling

-- [TABLET NODE: SamplingPairOutputMembership]
theorem SamplingPairOutputMembership {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (π : V → ℝ) (u v : V) :
    ({u, v} : Finset V) ⊆
        (Finset.univ.filter fun z : V =>
          z ∈ A ∧ ∀ w : V, w ∈ A → G.Adj z w → π w < π z) ↔
      u ∈ A ∧ v ∈ A ∧
        (∀ w : V, w ∈ A → G.Adj u w → π w < π u) ∧
          (∀ w : V, w ∈ A → G.Adj v w → π w < π v) := by
-- BODY
  constructor
  · intro hpair
    have huout :
        u ∈
          (Finset.univ.filter fun z : V =>
            z ∈ A ∧ ∀ w : V, w ∈ A → G.Adj z w → π w < π z) := by
      exact hpair (by simp)
    have hvout :
        v ∈
          (Finset.univ.filter fun z : V =>
            z ∈ A ∧ ∀ w : V, w ∈ A → G.Adj z w → π w < π z) := by
      exact hpair (by simp)
    have hu :
        u ∈ A ∧ ∀ w : V, w ∈ A → G.Adj u w → π w < π u := by
      simpa using huout
    have hv :
        v ∈ A ∧ ∀ w : V, w ∈ A → G.Adj v w → π w < π v := by
      simpa using hvout
    exact ⟨hu.1, hv.1, hu.2, hv.2⟩
  · rintro ⟨huA, hvA, husurv, hvsurv⟩ z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨huA, husurv⟩
    · exact ⟨hvA, hvsurv⟩
