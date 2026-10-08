import Tablet.Preamble
import Tablet.KPartiteIncidentWeightDoubleCount
import Tablet.KPartiteOrderedTriangleDoubleCount
import Tablet.KPartiteFixedVertexCauchyEstimate
import Tablet.KPartiteFixedVertexReducedEstimate
import Tablet.KPartiteFixedVertexTotalEstimate
import Tablet.KPartiteIncidentTotalBounds
import Tablet.KPartiteVertexTriangleDoubleCount
import Tablet.KPartiteTriangleCoefficientIdentity
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 2000000

-- [TABLET NODE: KPartiteWeightedTriangleInequality]
theorem KPartiteWeightedTriangleInequality :
    ∀ k : ℕ, 3 ≤ k →
      ∀ w : Fin k → Fin k → ℝ,
        (∀ i j, 0 ≤ w i j) →
        (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
            (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).sum
            (fun t =>
              Real.sqrt
                (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2)))
          ≤ (Nat.choose k 3 : ℝ) *
              (((((Finset.univ : Finset (Fin k × Fin k)).filter
                    (fun p => p.1 < p.2)).sum
                    (fun p => w p.1 p.2)) /
              (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
-- BODY
  intro k hk w hw
  classical
  let triples : Finset (Fin k × Fin k × Fin k) :=
    (Finset.univ.filter
      (fun t : Fin k × Fin k × Fin k => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
  let pairs : Finset (Fin k × Fin k) :=
    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
  have incident_weight_double_count :
      (∑ i : Fin k, ∑ j : Fin k,
          if i < j then w i j else if j < i then w j i else 0) =
        2 * pairs.sum (fun p : Fin k × Fin k => w p.1 p.2) := by
    simpa [pairs] using KPartiteIncidentWeightDoubleCount k w
  have ordered_triangle_double_count :
      let T : Fin k → Fin k → Fin k → ℝ :=
        fun i j l => Real.sqrt (w i j * w i l * w j l)
      (((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).sum
          (fun t => T t.1 t.2.1 t.2.2) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).sum
          (fun t => T t.1 t.2.2 t.2.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).sum
          (fun t => T t.2.1 t.1 t.2.2) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).sum
          (fun t => T t.2.1 t.2.2 t.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).sum
          (fun t => T t.2.2 t.1 t.2.1) +
        ((Finset.univ : Finset (Fin k × Fin k × Fin k)).filter
          (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).sum
          (fun t => T t.2.2 t.2.1 t.1)) =
        6 * triples.sum (fun t => T t.1 t.2.1 t.2.2) := by
    simpa [triples] using KPartiteOrderedTriangleDoubleCount k w hw
  have fixed_vertex_cauchy :
      ∀ i : Fin k,
        let s : Finset (Fin k × Fin k) :=
          (Finset.univ.filter
            (fun p : Fin k × Fin k => p.1 < p.2 ∧ p.1 ≠ i ∧ p.2 ≠ i))
        s.sum (fun p =>
            Real.sqrt (w i p.1 * w i p.2 * w p.1 p.2)) ≤
          Real.sqrt (s.sum (fun p => w i p.1 * w i p.2)) *
            Real.sqrt (s.sum (fun p => w p.1 p.2)) := by
    intro i
    simpa using KPartiteFixedVertexCauchyEstimate k i w hw
  have fixed_vertex_reduced :
      ∀ i : Fin k,
        let edge : Fin k → Fin k → ℝ :=
          fun a b => if a < b then w a b else if b < a then w b a else 0
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
            (fun p =>
              Real.sqrt
                (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1)) ≤
          (∑ j : others, edge i j.1) *
            Real.sqrt
              ((((Fintype.card others : ℝ) - 1) /
                    (2 * (Fintype.card others : ℝ))) *
                pairsOther.sum (fun p => edge p.1.1 p.2.1)) := by
    intro i edge others pairsOther
    have hedge_nonneg : ∀ a b : Fin k, 0 ≤ edge a b := by
      intro a b
      dsimp [edge]
      by_cases hab : a < b
      · simp [hab, hw a b]
      · by_cases hba : b < a
        · simp [hab, hba, hw b a]
        · simp [hab, hba]
    have hothers_nonempty : Nonempty others := by
      have hfin_card : 1 < Fintype.card (Fin k) := by
        simpa [Fintype.card_fin] using (by omega : 1 < k)
      obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hfin_card i
      exact ⟨⟨j, hji⟩⟩
    have hothers_card_pos : 0 < Fintype.card others :=
      Fintype.card_pos_iff.mpr hothers_nonempty
    simpa [edge, others, pairsOther] using
      (KPartiteFixedVertexReducedEstimate
        (u := fun j : others => edge i j.1)
        (v := fun a b : others => edge a.1 b.1)
        (by
          intro j
          exact hedge_nonneg i j.1)
        (by
          intro a b
          exact hedge_nonneg a.1 b.1)
        hothers_card_pos)
  have fixed_vertex_total :
      ∀ i : Fin k,
        let edge : Fin k → Fin k → ℝ :=
          fun a b => if a < b then w a b else if b < a then w b a else 0
        let pairs : Finset (Fin k × Fin k) :=
          (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
        let M : ℝ := pairs.sum (fun p => edge p.1 p.2)
        let Mi : ℝ := ∑ j : Fin k, edge i j
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
            (fun p =>
              Real.sqrt
                (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1)) ≤
          Mi * Real.sqrt
            ((((k : ℝ) - 2) / (2 * ((k : ℝ) - 1))) * (M - Mi)) := by
    intro i
    simpa using KPartiteFixedVertexTotalEstimate k hk i w hw
  have hk_pos_nat : 0 < k := by
    omega
  have hk_pos_real : (0 : ℝ) < k := by
    exact_mod_cast hk_pos_nat
  have hchoose_two_pos : (0 : ℝ) < (Nat.choose k 2 : ℝ) := by
    have htwo : 2 ≤ k := by omega
    have hpos : 0 < Nat.choose k 2 := Nat.choose_pos htwo
    exact_mod_cast hpos
  have hpair_sum_nonneg :
      0 ≤ pairs.sum (fun p : Fin k × Fin k => w p.1 p.2) := by
    exact Finset.sum_nonneg (by
      intro p hp
      exact hw p.1 p.2)
  have htriangle_terms_nonneg :
      ∀ t : Fin k × Fin k × Fin k,
        0 ≤ Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2) := by
    intro t
    exact Real.sqrt_nonneg _
  have htriangle_sum_nonneg :
      0 ≤ triples.sum
        (fun t : Fin k × Fin k × Fin k =>
          Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2)) := by
    exact Finset.sum_nonneg (by
      intro t ht
      exact htriangle_terms_nonneg t)
  let edge : Fin k → Fin k → ℝ :=
    fun a b => if a < b then w a b else if b < a then w b a else 0
  let M : ℝ := pairs.sum (fun p : Fin k × Fin k => edge p.1 p.2)
  let Mi : Fin k → ℝ := fun i => ∑ j : Fin k, edge i j
  have vertex_triangle_double_count :
      (∑ i : Fin k,
        let others := {j : Fin k // j ≠ i}
        let pairsOther : Finset (others × others) :=
          (Finset.univ.filter (fun p : others × others => p.1 < p.2))
        pairsOther.sum
          (fun p =>
            Real.sqrt
              (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))) =
      3 * triples.sum
        (fun t : Fin k × Fin k × Fin k =>
          Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2)) := by
    simpa [edge, triples] using KPartiteVertexTriangleDoubleCount k w
  have hM_eq_pair_sum :
      M = pairs.sum (fun p : Fin k × Fin k => w p.1 p.2) := by
    dsimp [M, edge, pairs]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp at hp
    simp [hp]
  have hM_nonneg : 0 ≤ M := by
    rw [hM_eq_pair_sum]
    exact hpair_sum_nonneg
  have incident_total_bounds :
      (∀ i : Fin k, 0 ≤ Mi i) ∧
        (∀ i : Fin k, Mi i ≤ M) ∧
          (∑ i : Fin k, Mi i) = 2 * M := by
    simpa [edge, pairs, M, Mi] using KPartiteIncidentTotalBounds k w hw
  have hMi_nonneg : ∀ i : Fin k, 0 ≤ Mi i := incident_total_bounds.1
  have hMi_le_M : ∀ i : Fin k, Mi i ≤ M := incident_total_bounds.2.1
  have hMi_sum : (∑ i : Fin k, Mi i) = 2 * M := incident_total_bounds.2.2
  have normalized_vertex_hypotheses :
      0 < M →
        (∀ i : Fin k, 0 ≤ Mi i / M) ∧
          (∀ i : Fin k, Mi i / M ≤ 1) ∧
            (∑ i : Fin k, Mi i / M) = 2 := by
    intro hM_pos
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    constructor
    · intro i
      exact div_nonneg (hMi_nonneg i) (le_of_lt hM_pos)
    constructor
    · intro i
      exact (div_le_one hM_pos).mpr (hMi_le_M i)
    · calc
        (∑ i : Fin k, Mi i / M) = (∑ i : Fin k, Mi i) / M := by
          rw [Finset.sum_div]
        _ = (2 * M) / M := by
          rw [hMi_sum]
        _ = 2 := by
          field_simp [hM_ne]
  have finite_cauchy :
      ∀ {ι : Type} [Fintype ι] (x : ι → ℝ),
        (∑ i : ι, x i) ^ 2 ≤
          (Fintype.card ι : ℝ) * (∑ i : ι, x i ^ 2) := by
    intro ι _ x
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := x))
  have sqrt_cauchy :
      ∀ {ι : Type} (s : Finset ι) (f g : ι → ℝ),
        (∀ i, 0 ≤ f i) →
        (∀ i, 0 ≤ g i) →
        (∑ i ∈ s, Real.sqrt (f i) * Real.sqrt (g i)) ≤
          Real.sqrt (∑ i ∈ s, f i) * Real.sqrt (∑ i ∈ s, g i) := by
    intro ι s f g hf hg
    simpa using
      (Real.sum_sqrt_mul_sqrt_le s (f := f) (g := g) hf hg)
  have vertex_optimization :
      ∀ x : Fin k → ℝ,
        (∀ i, 0 ≤ x i) →
        (∀ i, x i ≤ 1) →
        (∑ i : Fin k, x i) = 2 →
        (∑ i : Fin k, x i * Real.sqrt (1 - x i)) ≤
          2 * Real.sqrt (((k : ℝ) - 2) / k) := by
    intro x hx0 hx1 hxsum
    have hx_compl_nonneg : ∀ i, 0 ≤ 1 - x i := by
      intro i
      linarith [hx1 i]
    have hx_weight_nonneg : ∀ i, 0 ≤ x i * (1 - x i) := by
      intro i
      exact mul_nonneg (hx0 i) (hx_compl_nonneg i)
    have hweighted_cs :
        (∑ i : Fin k,
          Real.sqrt (x i) * Real.sqrt (x i * (1 - x i))) ≤
          Real.sqrt (∑ i : Fin k, x i) *
            Real.sqrt (∑ i : Fin k, x i * (1 - x i)) := by
      simpa using
        (sqrt_cauchy (Finset.univ : Finset (Fin k))
          (fun i : Fin k => x i)
          (fun i : Fin k => x i * (1 - x i)) hx0 hx_weight_nonneg)
    have hsq_lower :
        (∑ i : Fin k, x i) ^ 2 ≤
          (k : ℝ) * (∑ i : Fin k, x i ^ 2) := by
      simpa [Fintype.card_fin] using finite_cauchy (ι := Fin k) x
    have hterm_eq :
        ∀ i : Fin k,
          x i * Real.sqrt (1 - x i) =
            Real.sqrt (x i) * Real.sqrt (x i * (1 - x i)) := by
      intro i
      have hsqrt_x_sq : Real.sqrt (x i) * Real.sqrt (x i) = x i := by
        simpa [sq] using Real.sq_sqrt (hx0 i)
      calc
        x i * Real.sqrt (1 - x i)
            = (Real.sqrt (x i) * Real.sqrt (x i)) * Real.sqrt (1 - x i) := by
                rw [hsqrt_x_sq]
        _ = Real.sqrt (x i) * (Real.sqrt (x i) * Real.sqrt (1 - x i)) := by
                ring
        _ = Real.sqrt (x i) * Real.sqrt (x i * (1 - x i)) := by
                rw [Real.sqrt_mul (hx0 i) (1 - x i)]
    have hsum_rewrite :
        (∑ i : Fin k, x i * Real.sqrt (1 - x i)) =
          (∑ i : Fin k,
            Real.sqrt (x i) * Real.sqrt (x i * (1 - x i))) := by
      exact Finset.sum_congr rfl (by
        intro i hi
        exact hterm_eq i)
    have hsq_sum_lower : 4 / (k : ℝ) ≤ ∑ i : Fin k, x i ^ 2 := by
      have hsq_lower' : 4 ≤ (k : ℝ) * (∑ i : Fin k, x i ^ 2) := by
        have hsq_lower'' : (2 : ℝ) ^ 2 ≤ (k : ℝ) * (∑ i : Fin k, x i ^ 2) := by
          simpa [hxsum] using hsq_lower
        norm_num at hsq_lower''
        exact hsq_lower''
      exact (div_le_iff₀ hk_pos_real).mpr (by
        simpa [mul_comm] using hsq_lower')
    have hcomp_sum_eq :
        (∑ i : Fin k, x i * (1 - x i)) =
          2 - ∑ i : Fin k, x i ^ 2 := by
      calc
        (∑ i : Fin k, x i * (1 - x i))
            = ∑ i : Fin k, (x i - x i ^ 2) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i : Fin k, x i) - ∑ i : Fin k, x i ^ 2 := by
                rw [Finset.sum_sub_distrib]
        _ = 2 - ∑ i : Fin k, x i ^ 2 := by
                rw [hxsum]
    have hcomp_sum_le :
        (∑ i : Fin k, x i * (1 - x i)) ≤ 2 * (((k : ℝ) - 2) / k) := by
      rw [hcomp_sum_eq]
      calc
        2 - (∑ i : Fin k, x i ^ 2) ≤ 2 - 4 / (k : ℝ) := by
          linarith
        _ = 2 * (((k : ℝ) - 2) / k) := by
          field_simp [ne_of_gt hk_pos_real]
          ring
    have htarget_nonneg : 0 ≤ (((k : ℝ) - 2) / k) := by
      have hk_two_real : (2 : ℝ) ≤ k := by
        exact_mod_cast (by omega : 2 ≤ k)
      exact div_nonneg (sub_nonneg.mpr hk_two_real) (le_of_lt hk_pos_real)
    have hsqrt_comp_le :
        Real.sqrt (∑ i : Fin k, x i * (1 - x i)) ≤
          Real.sqrt (2 * (((k : ℝ) - 2) / k)) := by
      exact Real.sqrt_le_sqrt hcomp_sum_le
    have hafter_cs :
        (∑ i : Fin k, x i * Real.sqrt (1 - x i)) ≤
          Real.sqrt 2 *
            Real.sqrt (2 * (((k : ℝ) - 2) / k)) := by
      rw [hsum_rewrite]
      calc
        (∑ i : Fin k,
            Real.sqrt (x i) * Real.sqrt (x i * (1 - x i)))
            ≤ Real.sqrt (∑ i : Fin k, x i) *
                Real.sqrt (∑ i : Fin k, x i * (1 - x i)) := hweighted_cs
        _ = Real.sqrt 2 *
                Real.sqrt (∑ i : Fin k, x i * (1 - x i)) := by
              rw [hxsum]
        _ ≤ Real.sqrt 2 * Real.sqrt (2 * (((k : ℝ) - 2) / k)) := by
              exact mul_le_mul_of_nonneg_left hsqrt_comp_le (Real.sqrt_nonneg 2)
    have hsqrt_mul :
        Real.sqrt 2 * Real.sqrt (2 * (((k : ℝ) - 2) / k)) =
          2 * Real.sqrt (((k : ℝ) - 2) / k) := by
      calc
        Real.sqrt 2 * Real.sqrt (2 * (((k : ℝ) - 2) / k))
            = Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt (((k : ℝ) - 2) / k)) := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)
                  (((k : ℝ) - 2) / k)]
        _ = (Real.sqrt 2 * Real.sqrt 2) *
              Real.sqrt (((k : ℝ) - 2) / k) := by
                ring
        _ = 2 * Real.sqrt (((k : ℝ) - 2) / k) := by
                have hsqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                  simp
                rw [hsqrt_two_sq]
    exact hafter_cs.trans_eq hsqrt_mul
  have vertex_optimization_for_incident_totals :
      0 < M →
        (∑ i : Fin k, (Mi i / M) * Real.sqrt (1 - Mi i / M)) ≤
          2 * Real.sqrt (((k : ℝ) - 2) / k) := by
    intro hM_pos
    rcases normalized_vertex_hypotheses hM_pos with ⟨hx0, hx1, hxsum⟩
    exact vertex_optimization (fun i : Fin k => Mi i / M) hx0 hx1 hxsum
  let S : ℝ :=
    triples.sum
      (fun t : Fin k × Fin k × Fin k =>
        Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2))
  let T : Fin k → ℝ := fun i =>
    let others := {j : Fin k // j ≠ i}
    let pairsOther : Finset (others × others) :=
      (Finset.univ.filter (fun p : others × others => p.1 < p.2))
    pairsOther.sum
      (fun p =>
        Real.sqrt
          (edge i p.1.1 * edge i p.2.1 * edge p.1.1 p.2.1))
  let c : ℝ := (((k : ℝ) - 2) / (2 * ((k : ℝ) - 1)))
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using htriangle_sum_nonneg
  have hT_sum : (∑ i : Fin k, T i) = 3 * S := by
    simpa [T, S] using vertex_triangle_double_count
  have hT_le :
      ∀ i : Fin k, T i ≤ Mi i * Real.sqrt (c * (M - Mi i)) := by
    intro i
    simpa [T, c, edge, pairs, M, Mi] using fixed_vertex_total i
  by_cases hM_pos : 0 < M
  · have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      have hk_two_real : (2 : ℝ) ≤ k := by
        exact_mod_cast (by omega : 2 ≤ k)
      have hk_one_real : (1 : ℝ) < k := by
        exact_mod_cast (by omega : 1 < k)
      exact div_nonneg (sub_nonneg.mpr hk_two_real)
        (mul_nonneg (by norm_num) (le_of_lt (by linarith : (0 : ℝ) < (k : ℝ) - 1)))
    have hsumT_le :
        (∑ i : Fin k, T i) ≤
          ∑ i : Fin k, Mi i * Real.sqrt (c * (M - Mi i)) := by
      exact Finset.sum_le_sum (by
        intro i hi
        exact hT_le i)
    have hterm_rewrite :
        ∀ i : Fin k,
          Mi i * Real.sqrt (c * (M - Mi i)) =
            (M * Real.sqrt M) * Real.sqrt c *
              ((Mi i / M) * Real.sqrt (1 - Mi i / M)) := by
      intro i
      have hMi_nonneg_i : 0 ≤ Mi i := hMi_nonneg i
      have hMi_le_i : Mi i ≤ M := hMi_le_M i
      have hdiff_nonneg : 0 ≤ M - Mi i := by
        linarith
      have hx_nonneg : 0 ≤ Mi i / M := div_nonneg hMi_nonneg_i (le_of_lt hM_pos)
      have hx_le_one : Mi i / M ≤ 1 := (div_le_one hM_pos).mpr hMi_le_i
      have hcomp_nonneg : 0 ≤ 1 - Mi i / M := by
        linarith
      have hdiff_eq : M - Mi i = M * (1 - Mi i / M) := by
        field_simp [ne_of_gt hM_pos]
      have hsqrt_diff :
          Real.sqrt (M - Mi i) =
            Real.sqrt M * Real.sqrt (1 - Mi i / M) := by
        rw [hdiff_eq, Real.sqrt_mul (le_of_lt hM_pos) (1 - Mi i / M)]
      have hsqrt_c :
          Real.sqrt (c * (M - Mi i)) =
            Real.sqrt c * Real.sqrt (M - Mi i) := by
        rw [Real.sqrt_mul hc_nonneg (M - Mi i)]
      calc
        Mi i * Real.sqrt (c * (M - Mi i))
            = Mi i * (Real.sqrt c *
                (Real.sqrt M * Real.sqrt (1 - Mi i / M))) := by
                rw [hsqrt_c, hsqrt_diff]
        _ = (M * Real.sqrt M) * Real.sqrt c *
              ((Mi i / M) * Real.sqrt (1 - Mi i / M)) := by
                field_simp [ne_of_gt hM_pos]
    have hsum_rewrite :
        (∑ i : Fin k, Mi i * Real.sqrt (c * (M - Mi i))) =
          (M * Real.sqrt M) * Real.sqrt c *
            (∑ i : Fin k, (Mi i / M) * Real.sqrt (1 - Mi i / M)) := by
      calc
        (∑ i : Fin k, Mi i * Real.sqrt (c * (M - Mi i)))
            = ∑ i : Fin k,
                (M * Real.sqrt M) * Real.sqrt c *
                  ((Mi i / M) * Real.sqrt (1 - Mi i / M)) := by
                exact Finset.sum_congr rfl (by
                  intro i hi
                  rw [hterm_rewrite i])
        _ = (M * Real.sqrt M) * Real.sqrt c *
              (∑ i : Fin k, (Mi i / M) * Real.sqrt (1 - Mi i / M)) := by
              rw [Finset.mul_sum]
    have hvertex_bound :=
      vertex_optimization_for_incident_totals hM_pos
    have hsum_bound :
        (∑ i : Fin k, T i) ≤
          (M * Real.sqrt M) * Real.sqrt c *
            (2 * Real.sqrt (((k : ℝ) - 2) / k)) := by
      calc
        (∑ i : Fin k, T i)
            ≤ ∑ i : Fin k, Mi i * Real.sqrt (c * (M - Mi i)) := hsumT_le
        _ = (M * Real.sqrt M) * Real.sqrt c *
              (∑ i : Fin k, (Mi i / M) * Real.sqrt (1 - Mi i / M)) := hsum_rewrite
        _ ≤ (M * Real.sqrt M) * Real.sqrt c *
              (2 * Real.sqrt (((k : ℝ) - 2) / k)) := by
              exact mul_le_mul_of_nonneg_left hvertex_bound
                (mul_nonneg
                  (mul_nonneg (le_of_lt hM_pos) (Real.sqrt_nonneg M))
                  (Real.sqrt_nonneg c))
    have hthreeS_bound :
        3 * S ≤
          (M * Real.sqrt M) * Real.sqrt c *
            (2 * Real.sqrt (((k : ℝ) - 2) / k)) := by
      simpa [hT_sum] using hsum_bound
    have hS_bound :
        S ≤
          (((2 : ℝ) / 3) * Real.sqrt c *
            Real.sqrt (((k : ℝ) - 2) / k)) * (M * Real.sqrt M) := by
      have hdiv :
          S ≤ ((M * Real.sqrt M) * Real.sqrt c *
              (2 * Real.sqrt (((k : ℝ) - 2) / k))) / 3 := by
        nlinarith
      calc
        S ≤ ((M * Real.sqrt M) * Real.sqrt c *
              (2 * Real.sqrt (((k : ℝ) - 2) / k))) / 3 := hdiv
        _ = (((2 : ℝ) / 3) * Real.sqrt c *
              Real.sqrt (((k : ℝ) - 2) / k)) * (M * Real.sqrt M) := by
              ring
    have hcoeff :
        (((2 : ℝ) / 3) * Real.sqrt c *
            Real.sqrt (((k : ℝ) - 2) / k)) =
          (Nat.choose k 3 : ℝ) /
            (Nat.choose k 2 : ℝ) ^ ((3 : ℝ) / 2) := by
      simpa [c] using KPartiteTriangleCoefficientIdentity k hk
    have hM_rpow :
        M ^ ((3 : ℝ) / 2) = M * Real.sqrt M := by
      calc
        M ^ ((3 : ℝ) / 2) = M ^ (1 + (1 / 2 : ℝ)) := by
          norm_num
        _ = M * (M ^ (1 / 2 : ℝ)) := by
          rw [Real.rpow_add hM_pos]
          simp
        _ = M * Real.sqrt M := by
          rw [Real.sqrt_eq_rpow]
    have hC_nonneg : 0 ≤ (Nat.choose k 2 : ℝ) := le_of_lt hchoose_two_pos
    have htarget_rhs :
        (Nat.choose k 3 : ℝ) *
            ((M / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) =
          (((2 : ℝ) / 3) * Real.sqrt c *
            Real.sqrt (((k : ℝ) - 2) / k)) * (M * Real.sqrt M) := by
      rw [Real.div_rpow (le_of_lt hM_pos) hC_nonneg]
      rw [hM_rpow, hcoeff]
      ring
    calc
      triples.sum
          (fun t : Fin k × Fin k × Fin k =>
            Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2))
          = S := by rfl
      _ ≤ (((2 : ℝ) / 3) * Real.sqrt c *
            Real.sqrt (((k : ℝ) - 2) / k)) * (M * Real.sqrt M) := hS_bound
      _ = (Nat.choose k 3 : ℝ) *
            ((M / (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := htarget_rhs.symm
      _ = (Nat.choose k 3 : ℝ) *
            (((pairs.sum (fun p : Fin k × Fin k => w p.1 p.2)) /
              (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
            rw [hM_eq_pair_sum]
  · have hM_zero : M = 0 := by
      exact le_antisymm (le_of_not_gt hM_pos) hM_nonneg
    have hpair_zero :
        ∀ p ∈ pairs, w p.1 p.2 = 0 := by
      have hsum_zero :
          pairs.sum (fun p : Fin k × Fin k => w p.1 p.2) = 0 := by
        rw [← hM_eq_pair_sum, hM_zero]
      have hzero_iff :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := pairs)
          (f := fun p : Fin k × Fin k => w p.1 p.2)
          (by
            intro p hp
            exact hw p.1 p.2)).mp hsum_zero
      intro p hp
      exact hzero_iff p hp
    have hS_zero : S = 0 := by
      dsimp [S]
      apply Finset.sum_eq_zero
      intro t ht
      have ht' : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
        simpa [triples] using ht
      have hp12 : (t.1, t.2.1) ∈ pairs := by
        dsimp [pairs]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ht'.1
      have hp13 : (t.1, t.2.2) ∈ pairs := by
        dsimp [pairs]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_trans ht'.1 ht'.2
      have hp23 : (t.2.1, t.2.2) ∈ pairs := by
        dsimp [pairs]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ht'.2
      rw [hpair_zero (t.1, t.2.1) hp12,
        hpair_zero (t.1, t.2.2) hp13,
        hpair_zero (t.2.1, t.2.2) hp23]
      simp
    calc
      triples.sum
          (fun t : Fin k × Fin k × Fin k =>
            Real.sqrt (w t.1 t.2.1 * w t.1 t.2.2 * w t.2.1 t.2.2))
          = S := by rfl
      _ = 0 := hS_zero
      _ ≤ (Nat.choose k 3 : ℝ) *
            (((pairs.sum (fun p : Fin k × Fin k => w p.1 p.2)) /
              (Nat.choose k 2 : ℝ)) ^ ((3 : ℝ) / 2)) := by
            exact mul_nonneg (by positivity)
              (Real.rpow_nonneg
                (div_nonneg hpair_sum_nonneg (le_of_lt hchoose_two_pos)) _)
