import Tablet.RandomIndependentSetSampling
import Tablet.SamplingOneVertexEstimate

open BigOperators

-- [TABLET NODE: SamplingFirstMomentNeighborSetBound]
theorem SamplingFirstMomentNeighborSetBound (eta : ℝ) (heta : 0 < eta) :
    ∃ Delta0 gamma0 : ℕ, ∀ Delta : ℕ, ∀ gamma : ℝ,
      Delta0 ≤ Delta → (gamma0 : ℝ) ≤ gamma →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            ∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) ≤
                (X.card : ℝ) / (Delta : ℝ) + eta := by
-- BODY
  classical
  have h_event := SamplingOneVertexEstimate
  rcases Filter.eventually_atTop.mp h_event with ⟨DeltaOne, hDeltaOne⟩
  rcases exists_nat_gt (4 / eta) with ⟨DeltaErr, hDeltaErr_gt⟩
  refine ⟨max DeltaOne DeltaErr, 0, ?_⟩
  intro Delta gamma hDelta _hgamma V _instFintype _instDecEq G _instDecRel hregular μ hsampling r X hX
  have hDeltaOne_le : DeltaOne ≤ Delta := (le_max_left _ _).trans hDelta
  have hDeltaErr_le : DeltaErr ≤ Delta := (le_max_right _ _).trans hDelta
  have hDelta_pos_nat : 0 < Delta := by
    have hDeltaErr_pos : 0 < DeltaErr := by
      have hpos : (0 : ℝ) < (DeltaErr : ℝ) := by
        exact lt_trans (by positivity) hDeltaErr_gt
      exact_mod_cast hpos
    exact lt_of_lt_of_le hDeltaErr_pos hDeltaErr_le
  have hDelta_pos : 0 < (Delta : ℝ) := by exact_mod_cast hDelta_pos_nat
  have hDelta_ne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_pos
  have hfour_div_le : 4 / eta < (Delta : ℝ) := by
    exact lt_of_lt_of_le hDeltaErr_gt (by exact_mod_cast hDeltaErr_le)
  have htwo_over_le : 2 / (Delta : ℝ) ≤ eta := by
    have hpos4 : 0 < (4 : ℝ) := by norm_num
    have heta_pos : 0 < eta := heta
    have hmul : (4 / eta) * eta < (Delta : ℝ) * eta :=
      mul_lt_mul_of_pos_right hfour_div_le heta_pos
    have hfour_lt : (4 : ℝ) < (Delta : ℝ) * eta := by
      simpa [div_mul_cancel₀ _ (ne_of_gt heta_pos)] using hmul
    have htwo_lt : (2 : ℝ) < (Delta : ℝ) * eta := by linarith
    exact le_of_lt ((div_lt_iff₀ hDelta_pos).2 (by simpa [mul_comm] using htwo_lt))
  have hX_card_le_nat : X.card ≤ Delta := by
    have hsubset : X ⊆ G.neighborFinset r := by
      intro x hx
      simpa [SimpleGraph.mem_neighborFinset] using hX x hx
    have hcard_le := Finset.card_le_card hsubset
    simpa [hregular r] using hcard_le
  have hX_card_le : (X.card : ℝ) ≤ (Delta : ℝ) := by exact_mod_cast hX_card_le_nat
  have hOne := hDeltaOne Delta hDeltaOne_le gamma G hregular μ hsampling
  have hpoint :
      ∀ x : V, x ∈ X →
        (∑ S : Finset V, if x ∈ S then μ S else 0) ≤
          1 / (Delta : ℝ) + 2 / (Delta : ℝ)^2 := by
    intro x hx
    rcases hOne x with ⟨_hexact, habs⟩
    have hle_abs :
        (∑ S : Finset V, if x ∈ S then μ S else 0) -
            (1 - Real.exp (-gamma)) / (Delta : ℝ) ≤
          2 / (Delta : ℝ)^2 := by
      exact (le_abs_self _).trans habs
    have hexp_nonneg : 0 ≤ Real.exp (-gamma) := le_of_lt (Real.exp_pos _)
    have hone_minus_le : 1 - Real.exp (-gamma) ≤ 1 := by linarith
    have hbase_le : (1 - Real.exp (-gamma)) / (Delta : ℝ) ≤ 1 / (Delta : ℝ) := by
      exact div_le_div_of_nonneg_right hone_minus_le (le_of_lt hDelta_pos)
    linarith
  have hcard_decomp :
      (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ)) =
        X.sum (fun x => ∑ S : Finset V, (if x ∈ S then μ S else 0)) := by
    calc
      (∑ S : Finset V, μ S * ((S ∩ X).card : ℝ))
          = ∑ S : Finset V, μ S * X.sum (fun x => if x ∈ S then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro S _hS
            have hcount :
                ((S ∩ X).card : ℝ) = X.sum (fun x => if x ∈ S then (1 : ℝ) else 0) := by
              have hfilter : X.filter (fun x => x ∈ S) = S ∩ X := by
                ext x
                simp [and_comm]
              rw [← Finset.sum_filter]
              rw [hfilter]
              simp
            rw [hcount]
      _ = ∑ S : Finset V, X.sum (fun x => μ S * (if x ∈ S then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro S _hS
            rw [Finset.mul_sum]
      _ = X.sum (fun x => ∑ S : Finset V, (μ S * (if x ∈ S then (1 : ℝ) else 0))) := by
            rw [Finset.sum_comm]
      _ = X.sum (fun x => ∑ S : Finset V, (if x ∈ S then μ S else 0)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            apply Finset.sum_congr rfl
            intro S _hS
            by_cases hmem : x ∈ S <;> simp [hmem]
  have hsum_bound :
      X.sum (fun x => ∑ S : Finset V, (if x ∈ S then μ S else 0)) ≤
        X.sum (fun _x => 1 / (Delta : ℝ) + 2 / (Delta : ℝ)^2) := by
    exact Finset.sum_le_sum (fun x hx => hpoint x hx)
  have hconst :
      X.sum (fun _x => 1 / (Delta : ℝ) + 2 / (Delta : ℝ)^2) =
        (X.card : ℝ) / (Delta : ℝ) + (X.card : ℝ) * (2 / (Delta : ℝ)^2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hextra : (X.card : ℝ) * (2 / (Delta : ℝ)^2) ≤ eta := by
    calc
      (X.card : ℝ) * (2 / (Delta : ℝ)^2)
          ≤ (Delta : ℝ) * (2 / (Delta : ℝ)^2) := by
            exact mul_le_mul_of_nonneg_right hX_card_le (by positivity)
      _ = 2 / (Delta : ℝ) := by field_simp [hDelta_ne]
      _ ≤ eta := htwo_over_le
  rw [hcard_decomp]
  calc
    X.sum (fun x => ∑ S : Finset V, (if x ∈ S then μ S else 0))
        ≤ X.sum (fun _x => 1 / (Delta : ℝ) + 2 / (Delta : ℝ)^2) := hsum_bound
    _ = (X.card : ℝ) / (Delta : ℝ) + (X.card : ℝ) * (2 / (Delta : ℝ)^2) := hconst
    _ ≤ (X.card : ℝ) / (Delta : ℝ) + eta := by linarith
