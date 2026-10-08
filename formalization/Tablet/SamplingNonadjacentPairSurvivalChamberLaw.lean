import Tablet.SamplingActivationPriorityPushForwardSupport
import Tablet.SamplingFiniteCoordinateMarginalCellLaw
import Tablet.SamplingFinitePriorityOneCoordinateIntervalMass
import Tablet.SamplingNonadjacentPairOrderedChamberProductLaw
import Tablet.SamplingNonadjacentPairActivationAvoidanceProduct
import Tablet.SamplingNonadjacentPairChamberIntegrandNonnegative
import Tablet.SamplingNonadjacentPairNeighborClassProduct
import Tablet.SamplingNonadjacentPairOrderedPriorityAffineIntegral
import Tablet.SamplingTwoCoordinateOutsideSliceVolumeBound

open BigOperators

universe u

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

-- [TABLET NODE: SamplingNonadjacentPairSurvivalChamberLaw]
theorem SamplingNonadjacentPairSurvivalChamberLaw :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
        ∀ Delta : ℕ, ∀ gamma : ℝ,
          ∀ ν : @MeasureTheory.Measure (Finset V × (V → ℝ)) (MeasurableSpace.prod ⊤ inferInstance),
            0 < gamma →
            gamma ≤ (Delta : ℝ) →
            (∀ z : V, G.degree z = Delta) →
            ν Set.univ = 1 →
            (∀ A : Finset V,
              ν {ω | ω.1 = A} =
                ENNReal.ofReal
                  ((gamma / (Delta : ℝ)) ^ A.card *
                    (1 - gamma / (Delta : ℝ)) ^
                      ((Finset.univ : Finset V).card - A.card))) →
            (∀ A : Finset V,
              ν {ω | ω.1 = A ∧ ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1} =
                ν {ω | ω.1 = A}) →
            (∀ A : Finset V, ∀ t : V → ℝ,
              (∀ v : V, t v ∈ Set.Icc (0 : ℝ) 1) →
                ν {ω |
                  ω.1 = A ∧
                    ∀ v : V, 0 ≤ ω.2 v ∧ ω.2 v ≤ t v} =
                  ν {ω | ω.1 = A} *
                    ENNReal.ofReal (∏ v : V, t v)) →
            (∀ A : Finset V, ∀ v : V, v ∈ A →
              ν {ω |
                ω.1 = A ∧
                  (∀ u : V, u ∈ A → ω.2 u ∈ Set.Icc (0 : ℝ) 1) ∧
                    ∀ u : V, u ∈ A → G.Adj v u → ω.2 u < ω.2 v} =
                ν {ω | ω.1 = A} *
                  ENNReal.ofReal
                    (∫ a in (0 : ℝ)..1,
                      a ^
                        ((Finset.univ.filter fun u : V => u ∈ A ∧ G.Adj v u).card))) →
            ∀ u v : V, u ≠ v → ¬ G.Adj u v →
              ν {ω |
                u ∈
                    (Finset.univ.filter fun z : V =>
                      z ∈ ω.1 ∧
                        ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
                  v ∈
                    (Finset.univ.filter fun z : V =>
                      z ∈ ω.1 ∧
                        ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
                ENNReal.ofReal
                  ((2 / (Delta : ℝ)^2) *
                    ∫ x in (0 : ℝ)..gamma,
                      ∫ y in x..gamma,
                        (1 - x / (Delta : ℝ)) ^
                            (Delta -
                              (G.neighborFinset u ∩ G.neighborFinset v).card) *
                          (1 - y / (Delta : ℝ)) ^ Delta) := by
-- BODY
  classical
  intro V _ _ G _ Delta gamma ν hgamma_pos hgamma_le hregular hν_univ
    hactivation hcube hrect hone_vertex u v huv hnonadj
  letI : MeasurableSpace (Finset V × (V → ℝ)) := MeasurableSpace.prod ⊤ inferInstance
  have hDelta_real_pos : (0 : ℝ) < (Delta : ℝ) := by
    linarith
  have hDelta_pos : 0 < Delta := by
    exact_mod_cast hDelta_real_pos
  have hDelta_real_ne : (Delta : ℝ) ≠ 0 := ne_of_gt hDelta_real_pos
  have hactivation_param_nonneg : 0 ≤ gamma / (Delta : ℝ) := by
    exact le_of_lt (div_pos hgamma_pos hDelta_real_pos)
  have hactivation_param_le_one : gamma / (Delta : ℝ) ≤ 1 := by
    exact (div_le_one hDelta_real_pos).2 hgamma_le
  have hactivation_complement_nonneg : 0 ≤ 1 - gamma / (Delta : ℝ) := by
    linarith
  have hu_degree_card : (G.neighborFinset u).card = Delta := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hregular u
  have hv_degree_card : (G.neighborFinset v).card = Delta := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hregular v
  have hcommon_le_u :
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ Delta := by
    rw [← hu_degree_card]
    exact Finset.card_le_card (Finset.inter_subset_left)
  have hcommon_le_v :
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ Delta := by
    rw [← hv_degree_card]
    exact Finset.card_le_card (Finset.inter_subset_right)
  have hu_only_card :
      (G.neighborFinset u \ G.neighborFinset v).card =
        Delta - (G.neighborFinset u ∩ G.neighborFinset v).card := by
    rw [← hu_degree_card, ← Finset.card_sdiff_add_card_inter (G.neighborFinset u)
      (G.neighborFinset v)]
    exact (Nat.add_sub_cancel_right
      (G.neighborFinset u \ G.neighborFinset v).card
      (G.neighborFinset u ∩ G.neighborFinset v).card).symm
  have hv_only_card :
      (G.neighborFinset v \ G.neighborFinset u).card =
        Delta - (G.neighborFinset u ∩ G.neighborFinset v).card := by
    rw [← hv_degree_card, Finset.inter_comm (G.neighborFinset u) (G.neighborFinset v),
      ← Finset.card_sdiff_add_card_inter (G.neighborFinset v) (G.neighborFinset u)]
    exact (Nat.add_sub_cancel_right
      (G.neighborFinset v \ G.neighborFinset u).card
      (G.neighborFinset v ∩ G.neighborFinset u).card).symm
  have hu_not_mem_v_neighbors : u ∉ G.neighborFinset v := by
    simpa [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm] using hnonadj
  have hv_not_mem_u_neighbors : v ∉ G.neighborFinset u := by
    simpa [SimpleGraph.mem_neighborFinset] using hnonadj
  have hmandatory_atom :
      ν {ω : Finset V × (V → ℝ) | ω.1 = ({u, v} : Finset V)} =
        ENNReal.ofReal
          ((gamma / (Delta : ℝ)) ^ ({u, v} : Finset V).card *
            (1 - gamma / (Delta : ℝ)) ^
              ((Finset.univ : Finset V).card - ({u, v} : Finset V).card)) := by
    simpa using hactivation ({u, v} : Finset V)
  have hpair_card : ({u, v} : Finset V).card = 2 := by
    simp [huv]
  have hmandatory_atom_two :
      ν {ω : Finset V × (V → ℝ) | ω.1 = ({u, v} : Finset V)} =
        ENNReal.ofReal
          ((gamma / (Delta : ℝ)) ^ 2 *
            (1 - gamma / (Delta : ℝ)) ^
              ((Finset.univ : Finset V).card - 2)) := by
    simpa [hpair_card] using hmandatory_atom
  have hneighbor_factor_product (x y : ℝ) :
      (∏ _w ∈ (G.neighborFinset u \ G.neighborFinset v),
          (1 - x / (Delta : ℝ))) *
        (∏ _w ∈ G.neighborFinset v, (1 - y / (Delta : ℝ))) =
          (1 - x / (Delta : ℝ)) ^
              (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
            (1 - y / (Delta : ℝ)) ^ Delta := by
    exact SamplingNonadjacentPairNeighborClassProduct G Delta hregular u v huv hnonadj x y
  have hactivation_avoidance_product (x y : ℝ) :
      (∏ _w ∈ (G.neighborFinset u \ G.neighborFinset v),
          ((1 - gamma / (Delta : ℝ)) +
            (gamma / (Delta : ℝ)) * (1 - x / gamma))) *
        (∏ _w ∈ G.neighborFinset v,
          ((1 - gamma / (Delta : ℝ)) +
            (gamma / (Delta : ℝ)) * (1 - y / gamma))) =
          (∏ _w ∈ (G.neighborFinset u \ G.neighborFinset v),
            (1 - x / (Delta : ℝ))) *
            (∏ _w ∈ G.neighborFinset v, (1 - y / (Delta : ℝ))) := by
    exact SamplingNonadjacentPairActivationAvoidanceProduct
      (G.neighborFinset u \ G.neighborFinset v) (G.neighborFinset v)
      Delta gamma x y (ne_of_gt hgamma_pos)
  have hchamber_integrand_nonneg (x y : ℝ)
      (hx_nonneg : 0 ≤ x) (hxy : x ≤ y) (hy_le_gamma : y ≤ gamma) :
      0 ≤
        (1 - x / (Delta : ℝ)) ^
            (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
          (1 - y / (Delta : ℝ)) ^ Delta := by
    exact
      SamplingNonadjacentPairChamberIntegrandNonnegative Delta gamma
        (G.neighborFinset u ∩ G.neighborFinset v).card x y hgamma_pos hgamma_le
        hcommon_le_u hx_nonneg hxy hy_le_gamma
  let uOnly : Finset V := G.neighborFinset u \ G.neighborFinset v
  let vBlock : Finset V := G.neighborFinset v
  have hsurvival_event_normal_form :
      {ω : Finset V × (V → ℝ) |
        u ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
          v ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
        {ω : Finset V × (V → ℝ) |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
              ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v} := by
    ext ω
    constructor
    · intro hω
      have hu_mem :
          u ∈ ω.1 ∧
            ∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u := by
        simpa using (Finset.mem_filter.mp hω.1).2
      have hv_mem :
          v ∈ ω.1 ∧
            ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v := by
        simpa using (Finset.mem_filter.mp hω.2).2
      exact ⟨hu_mem.1, hv_mem.1, hu_mem.2, hv_mem.2⟩
    · intro hω
      constructor
      · exact Finset.mem_filter.mpr ⟨by simp, hω.1, hω.2.2.1⟩
      · exact Finset.mem_filter.mpr ⟨by simp, hω.2.1, hω.2.2.2⟩
  have hordered_shifted_priority_affine_integral :
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ uOnly.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ vBlock.card)) =
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / gamma ^ 2) *
              ((gamma / (Delta : ℝ)) ^ 2 *
                (((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card)) := by
    have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
    let p : ℝ := gamma / (Delta : ℝ)
    let c : ℝ := p ^ 2
    let F : ℝ → ℝ := fun a => ((1 - p) + p * a) ^ uOnly.card
    let H : ℝ → ℝ := fun b => ((1 - p) + p * b) ^ vBlock.card
    have h_subst (K : ℝ → ℝ) (a : ℝ) :
        ∫ t in a..gamma, K (1 - t / gamma) =
          gamma * ∫ r in (0 : ℝ)..(1 - a / gamma), K r := by
      have h := intervalIntegral.integral_comp_sub_div
        (f := K) (a := a) (b := gamma) (c := gamma) hgamma_ne (d := (1 : ℝ))
      simpa [sub_self, div_self hgamma_ne, mul_comm, mul_left_comm, mul_assoc] using h
    have h_rhs :
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            c * (F (1 - x / gamma) * H (1 - y / gamma))) =
          gamma ^ 2 *
            (∫ a in (0 : ℝ)..1,
              ∫ b in (0 : ℝ)..a,
                c * (F a * H b)) := by
      calc
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            c * (F (1 - x / gamma) * H (1 - y / gamma)))
            =
            ∫ x in (0 : ℝ)..gamma,
              gamma *
                (c * (F (1 - x / gamma) *
                  ∫ b in (0 : ℝ)..(1 - x / gamma), H b)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hy_subst := h_subst (K := fun b : ℝ =>
            c * (F (1 - x / gamma) * H b)) x
          simpa [mul_assoc, mul_left_comm, mul_comm] using hy_subst
        _ =
            gamma *
              (∫ x in (0 : ℝ)..gamma,
                c * (F (1 - x / gamma) *
                  ∫ b in (0 : ℝ)..(1 - x / gamma), H b)) := by
          rw [intervalIntegral.integral_const_mul]
        _ =
            gamma *
              (gamma *
                (∫ a in (0 : ℝ)..1,
                  ∫ b in (0 : ℝ)..a,
                    c * (F a * H b))) := by
          congr 1
          have hx_subst := h_subst (K := fun a : ℝ =>
            ∫ b in (0 : ℝ)..a, c * (F a * H b)) (0 : ℝ)
          simpa [zero_div, sub_zero, mul_assoc, mul_left_comm, mul_comm] using hx_subst
        _ =
            gamma ^ 2 *
              (∫ a in (0 : ℝ)..1,
                ∫ b in (0 : ℝ)..a,
                  c * (F a * H b)) := by
          ring
    have hscaled :
        (1 / gamma ^ 2) *
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              c * (F (1 - x / gamma) * H (1 - y / gamma))) =
          (∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              c * (F a * H b)) := by
      rw [h_rhs]
      field_simp [hgamma_ne]
    calc
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ uOnly.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ vBlock.card))
          =
          (∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              c * (F a * H b)) := by
        simp [F, H, c, p]
      _ =
          (1 / gamma ^ 2) *
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                c * (F (1 - x / gamma) * H (1 - y / gamma))) := by
        rw [hscaled]
      _ =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / gamma ^ 2) *
                ((gamma / (Delta : ℝ)) ^ 2 *
                  (((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card)) := by
        symm
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        change
          (∫ y in x..gamma,
            (1 / gamma ^ 2) *
              (c * (F (1 - x / gamma) * H (1 - y / gamma)))) =
            (1 / gamma ^ 2) *
              ∫ y in x..gamma,
                c * (F (1 - x / gamma) * H (1 - y / gamma))
        rw [intervalIntegral.integral_const_mul]
  have hsurvival_event_ordered_split :
      {ω : Finset V × (V → ℝ) |
        u ∈ ω.1 ∧ v ∈ ω.1 ∧
          (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
            ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v} =
        {ω : Finset V × (V → ℝ) |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
                ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v} ∪
          {ω : Finset V × (V → ℝ) |
            u ∈ ω.1 ∧ v ∈ ω.1 ∧
              ω.2 u ≤ ω.2 v ∧
                (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
                  ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v} := by
    ext ω
    constructor
    · intro hω
      rcases le_total (ω.2 v) (ω.2 u) with hle | hle
      · exact Or.inl ⟨hω.1, hω.2.1, hle, hω.2.2.1, hω.2.2.2⟩
      · exact Or.inr ⟨hω.1, hω.2.1, hle, hω.2.2.1, hω.2.2.2⟩
    · intro hω
      rcases hω with hω | hω
      · exact ⟨hω.1, hω.2.1, hω.2.2.2.1, hω.2.2.2.2⟩
      · exact ⟨hω.1, hω.2.1, hω.2.2.2.1, hω.2.2.2.2⟩
  have hsurvival_measure_ordered_union :
      ν {ω |
        u ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
          v ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)} =
        ν ({ω : Finset V × (V → ℝ) |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
                ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v} ∪
          {ω : Finset V × (V → ℝ) |
            u ∈ ω.1 ∧ v ∈ ω.1 ∧
              ω.2 u ≤ ω.2 v ∧
                (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
                  ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v}) := by
    rw [hsurvival_event_normal_form, hsurvival_event_ordered_split]
  have hu_not_uOnly_vBlock : u ∉ uOnly ∪ vBlock := by
    intro huS
    rcases Finset.mem_union.mp huS with huU | huV
    · have huu : G.Adj u u := by
        simpa [uOnly, SimpleGraph.mem_neighborFinset] using
          (Finset.mem_sdiff.mp huU).1
      exact G.loopless.irrefl u huu
    · have hvu : G.Adj v u := by
        simpa [vBlock, SimpleGraph.mem_neighborFinset] using huV
      exact hnonadj hvu.symm
  have hv_not_uOnly_vBlock : v ∉ uOnly ∪ vBlock := by
    intro hvS
    rcases Finset.mem_union.mp hvS with hvU | hvV
    · have huv_adj : G.Adj u v := by
        simpa [uOnly, SimpleGraph.mem_neighborFinset] using
          (Finset.mem_sdiff.mp hvU).1
      exact hnonadj huv_adj
    · have hvv : G.Adj v v := by
        simpa [vBlock, SimpleGraph.mem_neighborFinset] using hvV
      exact G.loopless.irrefl v hvv
  have huOnly_vBlock_disjoint : Disjoint uOnly vBlock := by
    rw [Finset.disjoint_left]
    intro z hzu hzv
    have hzu' : z ∈ G.neighborFinset u \ G.neighborFinset v := by
      simpa [uOnly] using hzu
    have hzv' : z ∈ G.neighborFinset v := by
      simpa [vBlock] using hzv
    exact (Finset.mem_sdiff.mp hzu').2 hzv'
  have hordered_product :=
    SamplingNonadjacentPairOrderedChamberProductLaw
      (ν := ν) (p := gamma / (Delta : ℝ)) (u := u) (v := v)
      (uOnly := uOnly) (vBlock := vBlock)
      hactivation_param_nonneg hactivation_param_le_one huv
      hu_not_uOnly_vBlock hv_not_uOnly_vBlock huOnly_vBlock_disjoint
      hactivation hcube hrect
  have hordered_product_integral_density :
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ uOnly.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ vBlock.card)) =
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta) := by
    calc
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ uOnly.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ vBlock.card))
          =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / gamma ^ 2) *
                ((gamma / (Delta : ℝ)) ^ 2 *
                  (((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card)) :=
        hordered_shifted_priority_affine_integral
      _ =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) gamma := by
          simpa [Set.uIcc_of_le hgamma_pos.le] using hx
        apply intervalIntegral.integral_congr
        intro y hy
        have hyIcc : y ∈ Set.Icc x gamma := by
          simpa [Set.uIcc_of_le hxIcc.2] using hy
        have hprod_shift :
            (((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                ((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card) =
              (∏ _w ∈ uOnly,
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - x / gamma))) *
                (∏ _w ∈ vBlock,
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - y / gamma))) := by
          simp [Finset.prod_const]
        have hprod_paper :
            (((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                ((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card) =
              (1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta := by
          calc
            (((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                ((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card)
                =
                (∏ _w ∈ uOnly,
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - x / gamma))) *
                  (∏ _w ∈ vBlock,
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - y / gamma))) := hprod_shift
            _ =
                (∏ _w ∈ uOnly, (1 - x / (Delta : ℝ))) *
                  (∏ _w ∈ vBlock, (1 - y / (Delta : ℝ))) := by
              rw [hactivation_avoidance_product x y]
            _ =
                (1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta := by
              simpa [uOnly, vBlock] using hneighbor_factor_product x y
        change
          (1 / gamma ^ 2) *
              ((gamma / (Delta : ℝ)) ^ 2 *
                (((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ uOnly.card *
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ vBlock.card)) =
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta)
        rw [hprod_paper]
        field_simp [ne_of_gt hgamma_pos, hDelta_real_ne]
  have hfirst_ordered_bridge_density_measure :
      ν {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              ω.2 v ≤ ω.2 u ∧
                (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
                  ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v} =
        ENNReal.ofReal
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) := by
    calc
      ν {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              ω.2 v ≤ ω.2 u ∧
                (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
                  ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v}
          =
          ENNReal.ofReal
            (∫ a in (0 : ℝ)..1,
              ∫ b in (0 : ℝ)..a,
                (gamma / (Delta : ℝ)) ^ 2 *
                  (((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * a) ^ uOnly.card *
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * b) ^ vBlock.card)) := hordered_product.1
      _ =
          ENNReal.ofReal
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 / (Delta : ℝ) ^ 2) *
                  ((1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta)) := by
        rw [hordered_product_integral_density]
  have hfirst_ordered_bridge_diagonal_zero :
      ν {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              ω.2 u = ω.2 v} = 0 := by
    exact hordered_product.2.1
  let fullCube : Set (Finset V × (V → ℝ)) :=
    {ω | ∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1}
  have hfullCube_compl_null : ν fullCubeᶜ = 0 := by
    let atom : Finset V → Set (Finset V × (V → ℝ)) := fun A => {ω | ω.1 = A}
    let cubeAtom : Finset V → Set (Finset V × (V → ℝ)) :=
      fun A => {ω | ω.1 = A ∧ ∀ q : V, q ∈ A → ω.2 q ∈ Set.Icc (0 : ℝ) 1}
    have hcube_subset_atom (A : Finset V) : cubeAtom A ⊆ atom A := by
      intro ω hω
      exact hω.1
    have hatom_finite (A : Finset V) : ν (atom A) ≠ ⊤ := by
      have hle : ν (atom A) ≤ ν Set.univ := by
        exact MeasureTheory.measure_mono (by intro ω _hω; trivial)
      rw [hν_univ] at hle
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hcube_finite (A : Finset V) : ν (cubeAtom A) ≠ ⊤ := by
      rw [show ν (cubeAtom A) = ν (atom A) by simpa [cubeAtom, atom] using hcube A]
      exact hatom_finite A
    have hdiff_null (A : Finset V) : ν (atom A \ cubeAtom A) = 0 := by
      rw [MeasureTheory.measure_diff (hcube_subset_atom A)
        (show MeasureTheory.NullMeasurableSet (cubeAtom A) ν from by
          have hfirst :
              MeasurableSet ({ω : Finset V × (V → ℝ) | ω.1 = A}) := by
            letI : MeasurableSpace (Finset V) := ⊤
            change MeasurableSet (Prod.fst ⁻¹' ({A} : Set (Finset V)))
            exact (show MeasurableSet ({A} : Set (Finset V)) from trivial).preimage
              measurable_fst
          have hcoords :
              MeasurableSet
                ({ω : Finset V × (V → ℝ) |
                  ∀ v : V, v ∈ A → ω.2 v ∈ Set.Icc (0 : ℝ) 1}) := by
            have hcoord (v : V) :
                Measurable (fun ω : Finset V × (V → ℝ) => ω.2 v) := by
              exact Measurable.eval (a := v) measurable_snd
            convert Finset.measurableSet_biInter A (fun v _hv => by
              show MeasurableSet
                ((fun ω : Finset V × (V → ℝ) => ω.2 v) ⁻¹'
                  Set.Icc (0 : ℝ) 1)
              exact measurableSet_Icc.preimage (hcoord v)) using 1
            ext ω
            simp
          have hcubeAtom_meas : MeasurableSet (cubeAtom A) := by
            dsimp [cubeAtom]
            exact hfirst.inter hcoords
          exact hcubeAtom_meas.nullMeasurableSet)
        (hcube_finite A)]
      rw [show ν (cubeAtom A) = ν (atom A) by simpa [cubeAtom, atom] using hcube A]
      exact tsub_self _
    have hcover :
        fullCubeᶜ ⊆ ⋃ A : Finset V, atom A \ cubeAtom A := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff]
        at hω ⊢
      refine ⟨ω.1, rfl, ?_⟩
      intro hcubeω
      exact hω hcubeω.2
    have hunion_null : ν (⋃ A : Finset V, atom A \ cubeAtom A) = 0 := by
      rw [MeasureTheory.measure_iUnion_null_iff]
      intro A
      exact hdiff_null A
    exact le_antisymm ((MeasureTheory.measure_mono hcover).trans_eq hunion_null) bot_le
  let firstWeak : Set (Finset V × (V → ℝ)) :=
    {ω |
      u ∈ ω.1 ∧ v ∈ ω.1 ∧
        ω.2 v ≤ ω.2 u ∧
          (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
            ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v}
  let secondWeak : Set (Finset V × (V → ℝ)) :=
    {ω |
      u ∈ ω.1 ∧ v ∈ ω.1 ∧
        ω.2 u ≤ ω.2 v ∧
          (∀ w : V, w ∈ ω.1 → G.Adj u w → ω.2 w < ω.2 u) ∧
            ∀ w : V, w ∈ ω.1 → G.Adj v w → ω.2 w < ω.2 v}
  let firstBridge : Set (Finset V × (V → ℝ)) :=
    {ω |
      u ∈ ω.1 ∧ v ∈ ω.1 ∧
        (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
          ω.2 v ≤ ω.2 u ∧
            (∀ z : V, z ∈ uOnly → z ∈ ω.1 → ω.2 z < ω.2 u) ∧
              ∀ z : V, z ∈ vBlock → z ∈ ω.1 → ω.2 z < ω.2 v}
  have hfirst_inter_cube : firstWeak ∩ fullCube = firstBridge := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hfirst, hcubeω⟩
      refine ⟨hfirst.1, hfirst.2.1, ?_, hfirst.2.2.1, ?_, ?_⟩
      · simpa [fullCube] using hcubeω
      · intro z hzu hzA
        have hzu_adj : G.Adj u z := by
          simpa [uOnly, SimpleGraph.mem_neighborFinset] using
            (Finset.mem_sdiff.mp hzu).1
        exact hfirst.2.2.2.1 z hzA hzu_adj
      · intro z hzv hzA
        have hzv_adj : G.Adj v z := by
          simpa [vBlock, SimpleGraph.mem_neighborFinset] using hzv
        exact hfirst.2.2.2.2 z hzA hzv_adj
    · intro hω
      constructor
      · refine ⟨hω.1, hω.2.1, hω.2.2.2.1, ?_, ?_⟩
        · intro w hwA huw
          by_cases hwv : G.Adj v w
          · have hwv_mem : w ∈ vBlock := by
              simpa [vBlock, SimpleGraph.mem_neighborFinset] using hwv
            exact lt_of_lt_of_le (hω.2.2.2.2.2 w hwv_mem hwA) hω.2.2.2.1
          · have hwuOnly : w ∈ uOnly := by
              simp [uOnly, SimpleGraph.mem_neighborFinset, huw, hwv]
            exact hω.2.2.2.2.1 w hwuOnly hwA
        · intro w hwA hvw
          have hwvBlock : w ∈ vBlock := by
            simpa [vBlock, SimpleGraph.mem_neighborFinset] using hvw
          exact hω.2.2.2.2.2 w hwvBlock hwA
      · simpa [fullCube] using hω.2.2.1
  have hfirstWeak_measure :
      ν firstWeak =
        ENNReal.ofReal
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) := by
    calc
      ν firstWeak = ν (firstWeak ∩ fullCube) := by
        exact (MeasureTheory.measure_inter_conull hfullCube_compl_null).symm
      _ = ν firstBridge := by rw [hfirst_inter_cube]
      _ =
        ENNReal.ofReal
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) := by
        simpa [firstBridge] using hfirst_ordered_bridge_density_measure
  have hvOnly_uBlock_disjoint :
      Disjoint (G.neighborFinset v \ G.neighborFinset u) (G.neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro z hzv hzu
    exact (Finset.mem_sdiff.mp hzv).2 hzu
  have hv_not_swapped_blocks :
      v ∉ (G.neighborFinset v \ G.neighborFinset u) ∪ G.neighborFinset u := by
    intro hvS
    rcases Finset.mem_union.mp hvS with hvV | hvU
    · have hvv : G.Adj v v := by
        simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp hvV).1
      exact G.loopless.irrefl v hvv
    · have huv_adj : G.Adj u v := by
        simpa [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm] using hvU
      exact hnonadj huv_adj
  have hu_not_swapped_blocks :
      u ∉ (G.neighborFinset v \ G.neighborFinset u) ∪ G.neighborFinset u := by
    intro huS
    rcases Finset.mem_union.mp huS with huV | huU
    · have hvu : G.Adj v u := by
        simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp huV).1
      exact hnonadj hvu.symm
    · have huu : G.Adj u u := by
        simpa [SimpleGraph.mem_neighborFinset] using huU
      exact G.loopless.irrefl u huu
  have hordered_product_swapped :=
    SamplingNonadjacentPairOrderedChamberProductLaw
      (ν := ν) (p := gamma / (Delta : ℝ)) (u := v) (v := u)
      (uOnly := G.neighborFinset v \ G.neighborFinset u)
      (vBlock := G.neighborFinset u)
      hactivation_param_nonneg hactivation_param_le_one (Ne.symm huv)
      hv_not_swapped_blocks hu_not_swapped_blocks hvOnly_uBlock_disjoint
      hactivation hcube hrect
  let secondBridge : Set (Finset V × (V → ℝ)) :=
    {ω |
      v ∈ ω.1 ∧ u ∈ ω.1 ∧
        (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
          ω.2 u ≤ ω.2 v ∧
            (∀ z : V, z ∈ G.neighborFinset v \ G.neighborFinset u →
              z ∈ ω.1 → ω.2 z < ω.2 v) ∧
              ∀ z : V, z ∈ G.neighborFinset u → z ∈ ω.1 → ω.2 z < ω.2 u}
  have hsecond_inter_cube : secondWeak ∩ fullCube = secondBridge := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨hsecond, hcubeω⟩
      refine ⟨hsecond.2.1, hsecond.1, ?_, hsecond.2.2.1, ?_, ?_⟩
      · simpa [fullCube] using hcubeω
      · intro z hzv hzA
        have hzv_adj : G.Adj v z := by
          simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp hzv).1
        exact hsecond.2.2.2.2 z hzA hzv_adj
      · intro z hzu hzA
        have hzu_adj : G.Adj u z := by
          simpa [SimpleGraph.mem_neighborFinset] using hzu
        exact hsecond.2.2.2.1 z hzA hzu_adj
    · intro hω
      constructor
      · refine ⟨hω.2.1, hω.1, hω.2.2.2.1, ?_, ?_⟩
        · intro w hwA huw
          have hwuBlock : w ∈ G.neighborFinset u := by
            simpa [SimpleGraph.mem_neighborFinset] using huw
          exact hω.2.2.2.2.2 w hwuBlock hwA
        · intro w hwA hvw
          by_cases huw : G.Adj u w
          · have hwuBlock : w ∈ G.neighborFinset u := by
              simpa [SimpleGraph.mem_neighborFinset] using huw
            exact lt_of_lt_of_le (hω.2.2.2.2.2 w hwuBlock hwA) hω.2.2.2.1
          · have hwvOnly : w ∈ G.neighborFinset v \ G.neighborFinset u := by
              simp [SimpleGraph.mem_neighborFinset, hvw, huw]
            exact hω.2.2.2.2.1 w hwvOnly hwA
      · simpa [fullCube] using hω.2.2.1
  have hshifted_priority_affine_integral_general (A B : Finset V) :
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ A.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ B.card)) =
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / gamma ^ 2) *
              ((gamma / (Delta : ℝ)) ^ 2 *
                (((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ A.card *
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ B.card)) := by
    have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
    let p : ℝ := gamma / (Delta : ℝ)
    let c : ℝ := p ^ 2
    let F : ℝ → ℝ := fun a => ((1 - p) + p * a) ^ A.card
    let H : ℝ → ℝ := fun b => ((1 - p) + p * b) ^ B.card
    have h_subst (K : ℝ → ℝ) (a : ℝ) :
        ∫ t in a..gamma, K (1 - t / gamma) =
          gamma * ∫ r in (0 : ℝ)..(1 - a / gamma), K r := by
      have h := intervalIntegral.integral_comp_sub_div
        (f := K) (a := a) (b := gamma) (c := gamma) hgamma_ne (d := (1 : ℝ))
      simpa [sub_self, div_self hgamma_ne, mul_comm, mul_left_comm, mul_assoc] using h
    have h_rhs :
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            c * (F (1 - x / gamma) * H (1 - y / gamma))) =
          gamma ^ 2 *
            (∫ a in (0 : ℝ)..1,
              ∫ b in (0 : ℝ)..a,
                c * (F a * H b)) := by
      calc
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            c * (F (1 - x / gamma) * H (1 - y / gamma)))
            =
            ∫ x in (0 : ℝ)..gamma,
              gamma *
                (c * (F (1 - x / gamma) *
                  ∫ b in (0 : ℝ)..(1 - x / gamma), H b)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hy_subst := h_subst (K := fun b : ℝ =>
            c * (F (1 - x / gamma) * H b)) x
          simpa [mul_assoc, mul_left_comm, mul_comm] using hy_subst
        _ =
            gamma *
              (∫ x in (0 : ℝ)..gamma,
                c * (F (1 - x / gamma) *
                  ∫ b in (0 : ℝ)..(1 - x / gamma), H b)) := by
          rw [intervalIntegral.integral_const_mul]
        _ =
            gamma *
              (gamma *
                (∫ a in (0 : ℝ)..1,
                  ∫ b in (0 : ℝ)..a,
                    c * (F a * H b))) := by
          congr 1
          have hx_subst := h_subst (K := fun a : ℝ =>
            ∫ b in (0 : ℝ)..a, c * (F a * H b)) (0 : ℝ)
          simpa [zero_div, sub_zero, mul_assoc, mul_left_comm, mul_comm] using hx_subst
        _ =
            gamma ^ 2 *
              (∫ a in (0 : ℝ)..1,
                ∫ b in (0 : ℝ)..a,
                  c * (F a * H b)) := by
          ring
    have hscaled :
        (1 / gamma ^ 2) *
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              c * (F (1 - x / gamma) * H (1 - y / gamma))) =
          (∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              c * (F a * H b)) := by
      rw [h_rhs]
      field_simp [hgamma_ne]
    calc
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^ A.card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^ B.card))
          =
          (∫ a in (0 : ℝ)..1,
            ∫ b in (0 : ℝ)..a,
              c * (F a * H b)) := by
        simp [F, H, c, p]
      _ =
          (1 / gamma ^ 2) *
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                c * (F (1 - x / gamma) * H (1 - y / gamma))) := by
        rw [hscaled]
      _ =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / gamma ^ 2) *
                ((gamma / (Delta : ℝ)) ^ 2 *
                  (((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^ A.card *
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^ B.card)) := by
        symm
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        change
          (∫ y in x..gamma,
            (1 / gamma ^ 2) *
              (c * (F (1 - x / gamma) * H (1 - y / gamma)))) =
            (1 / gamma ^ 2) *
              ∫ y in x..gamma,
                c * (F (1 - x / gamma) * H (1 - y / gamma))
        rw [intervalIntegral.integral_const_mul]
  have hswapped_density :
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^
                  (G.neighborFinset v \ G.neighborFinset u).card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^
                  (G.neighborFinset u).card)) =
        ∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta) := by
    have hshift :=
      hshifted_priority_affine_integral_general
        (G.neighborFinset v \ G.neighborFinset u) (G.neighborFinset u)
    have hprod (x y : ℝ) :
        (((1 - gamma / (Delta : ℝ)) +
              (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^
              (G.neighborFinset v \ G.neighborFinset u).card *
            ((1 - gamma / (Delta : ℝ)) +
              (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^
              (G.neighborFinset u).card) =
          (1 - x / (Delta : ℝ)) ^
              (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
            (1 - y / (Delta : ℝ)) ^ Delta := by
      have havoid :=
        SamplingNonadjacentPairActivationAvoidanceProduct
          (G.neighborFinset v \ G.neighborFinset u) (G.neighborFinset u)
          Delta gamma x y (ne_of_gt hgamma_pos)
      have hneighbor :
          (∏ _w ∈ (G.neighborFinset v \ G.neighborFinset u),
              (1 - x / (Delta : ℝ))) *
            (∏ _w ∈ G.neighborFinset u, (1 - y / (Delta : ℝ))) =
              (1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta := by
        have h :=
          SamplingNonadjacentPairNeighborClassProduct G Delta hregular
            v u (Ne.symm huv) (by simpa [SimpleGraph.adj_comm] using hnonadj) x y
        simpa [Finset.inter_comm] using h
      calc
        (((1 - gamma / (Delta : ℝ)) +
              (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^
              (G.neighborFinset v \ G.neighborFinset u).card *
            ((1 - gamma / (Delta : ℝ)) +
              (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^
              (G.neighborFinset u).card)
            =
            (∏ _w ∈ (G.neighborFinset v \ G.neighborFinset u),
                ((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - x / gamma))) *
              (∏ _w ∈ G.neighborFinset u,
                ((1 - gamma / (Delta : ℝ)) +
                  (gamma / (Delta : ℝ)) * (1 - y / gamma))) := by
          simp [Finset.prod_const]
        _ =
            (∏ _w ∈ (G.neighborFinset v \ G.neighborFinset u),
                (1 - x / (Delta : ℝ))) *
              (∏ _w ∈ G.neighborFinset u, (1 - y / (Delta : ℝ))) := by
          rw [havoid]
        _ =
            (1 - x / (Delta : ℝ)) ^
                (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
              (1 - y / (Delta : ℝ)) ^ Delta := hneighbor
    calc
      (∫ a in (0 : ℝ)..1,
        ∫ b in (0 : ℝ)..a,
          (gamma / (Delta : ℝ)) ^ 2 *
            (((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * a) ^
                  (G.neighborFinset v \ G.neighborFinset u).card *
              ((1 - gamma / (Delta : ℝ)) +
                (gamma / (Delta : ℝ)) * b) ^
                  (G.neighborFinset u).card))
          =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / gamma ^ 2) *
                ((gamma / (Delta : ℝ)) ^ 2 *
                  (((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^
                        (G.neighborFinset v \ G.neighborFinset u).card *
                    ((1 - gamma / (Delta : ℝ)) +
                      (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^
                        (G.neighborFinset u).card)) := hshift
      _ =
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply intervalIntegral.integral_congr
        intro y hy
        change
          (1 / gamma ^ 2) *
              ((gamma / (Delta : ℝ)) ^ 2 *
                (((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - x / gamma)) ^
                      (G.neighborFinset v \ G.neighborFinset u).card *
                  ((1 - gamma / (Delta : ℝ)) +
                    (gamma / (Delta : ℝ)) * (1 - y / gamma)) ^
                      (G.neighborFinset u).card)) =
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta)
        rw [hprod x y]
        field_simp [ne_of_gt hgamma_pos, hDelta_real_ne]
  have hsecondWeak_measure :
      ν secondWeak =
        ENNReal.ofReal
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) := by
    calc
      ν secondWeak = ν (secondWeak ∩ fullCube) := by
        exact (MeasureTheory.measure_inter_conull hfullCube_compl_null).symm
      _ = ν secondBridge := by rw [hsecond_inter_cube]
      _ =
        ENNReal.ofReal
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) := by
        calc
          ν secondBridge =
              ENNReal.ofReal
                (∫ a in (0 : ℝ)..1,
                  ∫ b in (0 : ℝ)..a,
                    (gamma / (Delta : ℝ)) ^ 2 *
                      (((1 - gamma / (Delta : ℝ)) +
                          (gamma / (Delta : ℝ)) * a) ^
                            (G.neighborFinset v \ G.neighborFinset u).card *
                        ((1 - gamma / (Delta : ℝ)) +
                          (gamma / (Delta : ℝ)) * b) ^
                            (G.neighborFinset u).card)) := by
            simpa [secondBridge] using hordered_product_swapped.1
          _ =
              ENNReal.ofReal
                (∫ x in (0 : ℝ)..gamma,
                  ∫ y in x..gamma,
                    (1 / (Delta : ℝ) ^ 2) *
                      ((1 - x / (Delta : ℝ)) ^
                          (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                        (1 - y / (Delta : ℝ)) ^ Delta)) := by
            rw [hswapped_density]
  have hoverlap_null : ν (firstWeak ∩ secondWeak) = 0 := by
    have hsubset : firstWeak ∩ secondWeak ⊆
        {ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              ω.2 u = ω.2 v} ∪ fullCubeᶜ := by
      intro ω hω
      by_cases hcubeω : ω ∈ fullCube
      · left
        have hdiag : ω.2 u = ω.2 v := le_antisymm hω.2.2.2.1 hω.1.2.2.1
        exact ⟨hω.1.1, hω.1.2.1, by simpa [fullCube] using hcubeω, hdiag⟩
      · right
        exact hcubeω
    have htarget_null :
        ν ({ω |
          u ∈ ω.1 ∧ v ∈ ω.1 ∧
            (∀ q : V, q ∈ ω.1 → ω.2 q ∈ Set.Icc (0 : ℝ) 1) ∧
              ω.2 u = ω.2 v} ∪ fullCubeᶜ) = 0 := by
      exact MeasureTheory.measure_union_null hfirst_ordered_bridge_diagonal_zero
        hfullCube_compl_null
    exact MeasureTheory.measure_mono_null hsubset htarget_null
  have hordered_union_measure :
      ν (firstWeak ∪ secondWeak) =
        ENNReal.ofReal
          (2 *
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 / (Delta : ℝ) ^ 2) *
                  ((1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta))) := by
    let firstPiece : Finset V → Set (Finset V × (V → ℝ)) :=
      fun A =>
        {ω |
          ω.1 = A ∧ u ∈ A ∧ v ∈ A ∧
            ω.2 v ≤ ω.2 u ∧
              (∀ w : V, w ∈ A → G.Adj u w → ω.2 w < ω.2 u) ∧
                ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v}
    let secondPiece : Finset V → Set (Finset V × (V → ℝ)) :=
      fun A =>
        {ω |
          ω.1 = A ∧ u ∈ A ∧ v ∈ A ∧
            ω.2 u ≤ ω.2 v ∧
              (∀ w : V, w ∈ A → G.Adj u w → ω.2 w < ω.2 u) ∧
                ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v}
    have hcoord_meas (z : V) :
        Measurable (fun ω : Finset V × (V → ℝ) => ω.2 z) := by
      exact Measurable.eval (a := z) measurable_snd
    have hcuts_u_meas (A : Finset V) :
        MeasurableSet
          ({ω : Finset V × (V → ℝ) |
            ∀ w : V, w ∈ A → G.Adj u w → ω.2 w < ω.2 u}) := by
      let T : Finset V := A.filter fun w => G.Adj u w
      convert Finset.measurableSet_biInter T (fun w _hw => by
        exact measurableSet_lt (hcoord_meas w) (hcoord_meas u)) using 1
      ext ω
      simp [T]
    have hcuts_v_meas (A : Finset V) :
        MeasurableSet
          ({ω : Finset V × (V → ℝ) |
            ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v}) := by
      let T : Finset V := A.filter fun w => G.Adj v w
      convert Finset.measurableSet_biInter T (fun w _hw => by
        exact measurableSet_lt (hcoord_meas w) (hcoord_meas v)) using 1
      ext ω
      simp [T]
    have hfirstPiece_meas (A : Finset V) : MeasurableSet (firstPiece A) := by
      have hfirst :
          MeasurableSet ({ω : Finset V × (V → ℝ) | ω.1 = A}) := by
        letI : MeasurableSpace (Finset V) := ⊤
        change MeasurableSet (Prod.fst ⁻¹' ({A} : Set (Finset V)))
        exact (show MeasurableSet ({A} : Set (Finset V)) from trivial).preimage
          measurable_fst
      have horder :
          MeasurableSet ({ω : Finset V × (V → ℝ) | ω.2 v ≤ ω.2 u}) := by
        exact measurableSet_le (hcoord_meas v) (hcoord_meas u)
      by_cases huA : u ∈ A
      · by_cases hvA : v ∈ A
        · have hmeas :
              MeasurableSet
                ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩
                  ({ω : Finset V × (V → ℝ) | ω.2 v ≤ ω.2 u} ∩
                    ({ω : Finset V × (V → ℝ) |
                      ∀ w : V, w ∈ A → G.Adj u w → ω.2 w < ω.2 u} ∩
                      {ω : Finset V × (V → ℝ) |
                        ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v}))) :=
            hfirst.inter (horder.inter ((hcuts_u_meas A).inter (hcuts_v_meas A)))
          convert hmeas using 1
          ext ω
          simp [firstPiece, huA, hvA, and_assoc]
        · simp [firstPiece, hvA]
      · simp [firstPiece, huA]
    have hsecondPiece_meas (A : Finset V) : MeasurableSet (secondPiece A) := by
      have hfirst :
          MeasurableSet ({ω : Finset V × (V → ℝ) | ω.1 = A}) := by
        letI : MeasurableSpace (Finset V) := ⊤
        change MeasurableSet (Prod.fst ⁻¹' ({A} : Set (Finset V)))
        exact (show MeasurableSet ({A} : Set (Finset V)) from trivial).preimage
          measurable_fst
      have horder :
          MeasurableSet ({ω : Finset V × (V → ℝ) | ω.2 u ≤ ω.2 v}) := by
        exact measurableSet_le (hcoord_meas u) (hcoord_meas v)
      by_cases huA : u ∈ A
      · by_cases hvA : v ∈ A
        · have hmeas :
              MeasurableSet
                ({ω : Finset V × (V → ℝ) | ω.1 = A} ∩
                  ({ω : Finset V × (V → ℝ) | ω.2 u ≤ ω.2 v} ∩
                    ({ω : Finset V × (V → ℝ) |
                      ∀ w : V, w ∈ A → G.Adj u w → ω.2 w < ω.2 u} ∩
                      {ω : Finset V × (V → ℝ) |
                        ∀ w : V, w ∈ A → G.Adj v w → ω.2 w < ω.2 v}))) :=
            hfirst.inter (horder.inter ((hcuts_u_meas A).inter (hcuts_v_meas A)))
          convert hmeas using 1
          ext ω
          simp [secondPiece, huA, hvA, and_assoc]
        · simp [secondPiece, hvA]
      · simp [secondPiece, huA]
    have hfirst_eq :
        firstWeak =
          ⋃ A ∈ (Finset.univ : Finset (Finset V)), firstPiece A := by
      ext ω
      constructor
      · intro hω
        rw [Set.mem_iUnion]
        refine ⟨ω.1, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨by simp, ?_⟩
        simpa [firstPiece, firstWeak] using hω
      · intro hω
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨A, hω⟩
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨_hA, hω⟩
        rcases hω with ⟨hωA, huA, hvA, horder, huCuts, hvCuts⟩
        subst A
        exact ⟨huA, hvA, horder, huCuts, hvCuts⟩
    have hsecond_eq :
        secondWeak =
          ⋃ A ∈ (Finset.univ : Finset (Finset V)), secondPiece A := by
      ext ω
      constructor
      · intro hω
        rw [Set.mem_iUnion]
        refine ⟨ω.1, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨by simp, ?_⟩
        simpa [secondPiece, secondWeak] using hω
      · intro hω
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨A, hω⟩
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨_hA, hω⟩
        rcases hω with ⟨hωA, huA, hvA, horder, huCuts, hvCuts⟩
        subst A
        exact ⟨huA, hvA, horder, huCuts, hvCuts⟩
    have hmeas_first : MeasurableSet firstWeak := by
      rw [hfirst_eq]
      exact Finset.measurableSet_biUnion (Finset.univ : Finset (Finset V))
        (fun A _hA => hfirstPiece_meas A)
    have hmeas_second : MeasurableSet secondWeak := by
      rw [hsecond_eq]
      exact Finset.measurableSet_biUnion (Finset.univ : Finset (Finset V))
        (fun A _hA => hsecondPiece_meas A)
    have hsum :
        ν (firstWeak ∪ secondWeak) = ν firstWeak + ν secondWeak := by
      have h :=
        MeasureTheory.measure_union_add_inter (μ := ν) (t := secondWeak) firstWeak
          hmeas_second
      simpa [hoverlap_null] using h
    rw [hsum, hfirstWeak_measure, hsecondWeak_measure]
    have hintegral_nonneg :
        0 ≤
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta) := by
      refine intervalIntegral.integral_nonneg hgamma_pos.le ?_
      intro x hx
      refine intervalIntegral.integral_nonneg hx.2 ?_
      intro y hy
      exact mul_nonneg (by positivity)
        (hchamber_integrand_nonneg x y hx.1 hy.1 hy.2)
    rw [← ENNReal.ofReal_add hintegral_nonneg hintegral_nonneg]
    ring_nf
  have hconst_integral :
      2 *
          (∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) =
        (2 / (Delta : ℝ)^2) *
          ∫ x in (0 : ℝ)..gamma,
            ∫ y in x..gamma,
                (1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta := by
    have hinner :
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta)) =
          (1 / (Delta : ℝ) ^ 2) *
            ∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta := by
      calc
        (∫ x in (0 : ℝ)..gamma,
          ∫ y in x..gamma,
            (1 / (Delta : ℝ) ^ 2) *
              ((1 - x / (Delta : ℝ)) ^
                  (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                (1 - y / (Delta : ℝ)) ^ Delta))
            =
            ∫ x in (0 : ℝ)..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ∫ y in x..gamma,
                  (1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta := by
          apply intervalIntegral.integral_congr
          intro x hx
          change
            (∫ y in x..gamma,
              (1 / (Delta : ℝ) ^ 2) *
                ((1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta)) =
              (1 / (Delta : ℝ) ^ 2) *
                ∫ y in x..gamma,
                  (1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta
          rw [intervalIntegral.integral_const_mul]
        _ =
            (1 / (Delta : ℝ) ^ 2) *
              ∫ x in (0 : ℝ)..gamma,
                ∫ y in x..gamma,
                  (1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta := by
          rw [intervalIntegral.integral_const_mul]
    rw [hinner]
    ring
  calc
    ν {ω |
        u ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z) ∧
          v ∈
            (Finset.univ.filter fun z : V =>
              z ∈ ω.1 ∧
                ∀ w : V, w ∈ ω.1 → G.Adj z w → ω.2 w < ω.2 z)}
        = ν (firstWeak ∪ secondWeak) := by
          simpa [firstWeak, secondWeak] using hsurvival_measure_ordered_union
    _ =
        ENNReal.ofReal
          (2 *
            (∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 / (Delta : ℝ) ^ 2) *
                  ((1 - x / (Delta : ℝ)) ^
                      (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                    (1 - y / (Delta : ℝ)) ^ Delta))) := hordered_union_measure
    _ =
        ENNReal.ofReal
          ((2 / (Delta : ℝ)^2) *
            ∫ x in (0 : ℝ)..gamma,
              ∫ y in x..gamma,
                (1 - x / (Delta : ℝ)) ^
                    (Delta - (G.neighborFinset u ∩ G.neighborFinset v).card) *
                  (1 - y / (Delta : ℝ)) ^ Delta) := by
          rw [hconst_integral]
