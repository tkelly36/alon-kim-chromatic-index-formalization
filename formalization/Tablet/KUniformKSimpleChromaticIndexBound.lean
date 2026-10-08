import Tablet.ChromaticIndexAtMostReal
import Tablet.GeneralColoringTheorem
import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.KUniformKSimpleBParameterEstimate
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.ProperEdgeColoring
import Tablet.SubhypergraphOf
import Tablet.SubhypergraphInheritance
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph
import Tablet.LocalBParameterRealFloorTransfer

-- [TABLET NODE: KUniformKSimpleChromaticIndexBound]
theorem KUniformKSimpleChromaticIndexBound :
    ∀ iota : ℝ, 0 < iota → ∀ k : ℕ, 0 < k →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) k k D →
            ChromaticIndexAtMostReal H
              ((1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
                  (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
                    (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ)) + iota) *
                (k : ℝ) * (D : ℝ)) := by
-- BODY
  classical
  intro iota hiota k hk
  by_cases hkone : k = 1
  · subst k
    refine ⟨1, ?_⟩
    intro D hD V E _ _ _ H hH
    rcases hH with ⟨huni, hsimple, hdeg⟩
    have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
    let order : E ≃ Fin (Fintype.card E) := Fintype.equivFin E
    let fiber : E → Finset E := fun e => Finset.univ.filter (fun f => H.edge f = H.edge e)
    let color : E → Fin D := fun e =>
      ⟨(fiber e).filter (fun f => order f < order e) |>.card, by
        have hsub : fiber e ⊆ Finset.univ.filter (fun f => (Finset.card_eq_one.mp (huni e)).choose ∈ H.edge f) := by
          intro f hf
          have heq := (Finset.mem_filter.mp hf).2
          have hcarde := Finset.card_eq_one.mp (huni e)
          have hmem : hcarde.choose ∈ H.edge e := by
            have hs : ({hcarde.choose} : Finset V) ⊆ H.edge e := by
              rw [← hcarde.choose_spec]
            exact hs (Finset.mem_singleton_self _)
          simpa [heq] using hmem
        have hle : (fiber e).card ≤ (Finset.univ.filter (fun f => (Finset.card_eq_one.mp (huni e)).choose ∈ H.edge f)).card := Finset.card_le_card hsub
        have hd := hdeg (Finset.card_eq_one.mp (huni e)).choose
        have hcard : (Finset.univ.filter (fun f => (Finset.card_eq_one.mp (huni e)).choose ∈ H.edge f)).card ≤ D := by simpa [HypergraphDegree] using hd
        have hlt : (fiber e).filter (fun f => order f < order e) ⊂ fiber e := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro heq
          have hnot : e ∉ (fiber e).filter (fun f => order f < order e) := by
            dsimp [fiber]
            simp
          apply hnot
          rw [heq]
          dsimp [fiber]
          simp
        exact lt_of_lt_of_le (Finset.card_lt_card hlt) (le_trans hle hcard)⟩
    · dsimp [ChromaticIndexAtMostReal]
      refine ⟨D, ?_, ?_⟩
      · have hDr : (0 : ℝ) ≤ D := by positivity
        nlinarith
      · refine ⟨color, ?_⟩
        intro e f hef hmeet heq
        have hedge : H.edge e = H.edge f := by
          have he := (Finset.card_eq_one.mp (huni e)).choose_spec
          have hf := (Finset.card_eq_one.mp (huni f)).choose_spec
          obtain ⟨x, hx⟩ := hmeet
          have xe := (Finset.mem_inter.mp hx).1
          have xf := (Finset.mem_inter.mp hx).2
          rw [he] at xe
          rw [hf] at xf
          have hxe : x = (Finset.card_eq_one.mp (huni e)).choose := Finset.mem_singleton.mp xe
          have hxf : x = (Finset.card_eq_one.mp (huni f)).choose := Finset.mem_singleton.mp xf
          have hce : (Finset.card_eq_one.mp (huni e)).choose =
              (Finset.card_eq_one.mp (huni f)).choose := hxe.symm.trans hxf
          exact he.trans ((congrArg (fun z : V => ({z} : Finset V)) hce).trans hf.symm)
        have hfib : f ∈ fiber e := by simp [fiber, hedge]
        have hlt : order e < order f ∨ order f < order e := lt_or_gt_of_ne (fun h => hef (order.injective h))
        rcases hlt with hlt | hlt
        · have hcard : (color e).val < (color f).val := by
            dsimp [color]
            have hfib_eq : fiber f = fiber e := by ext g; simp [fiber, hedge]
            rw [hfib_eq]
            apply Finset.card_lt_card
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨?_, ?_⟩
            · intro g hg
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
                lt_trans (Finset.mem_filter.mp hg).2 hlt⟩
            · intro heq'
              have hmem : e ∈ (fiber e).filter (fun g => order g < order f) := by simp [hlt, fiber]
              have hh := (Finset.mem_filter.mp (heq' ▸ hmem)).2
              omega
          exact (by omega)
        · have hcard : (color f).val < (color e).val := by
            dsimp [color]
            have hefib : fiber e = fiber f := by ext g; simp [fiber, hedge]
            rw [hefib]
            apply Finset.card_lt_card
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨?_, ?_⟩
            · intro g hg
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
                lt_trans (Finset.mem_filter.mp hg).2 hlt⟩
            · intro heq'
              have hmem : f ∈ (fiber f).filter (fun g => order g < order e) := by simp [hlt, fiber]
              have hh := (Finset.mem_filter.mp (heq' ▸ hmem)).2
              omega
          exact (by omega)
  · have hk2 : 2 ≤ k := by omega
    let c : ℝ := 1 - ((k : ℝ) - 1) / (2 * (k : ℝ) ^ 2) +
      (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
        (6 * (k : ℝ) ^ 3 * Real.sqrt (k : ℝ))
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
    have hcpos : 0 < c := by
      dsimp [c]
      have hsmall : ((k : ℝ) - 1) / (2 * (k : ℝ)^2) < 1 := by
        apply (div_lt_iff₀ (by positivity)).2
        nlinarith
      have hnon : 0 ≤ (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
          (6 * (k : ℝ)^3 * Real.sqrt (k : ℝ)) := by
        have hkminus : 0 ≤ (k : ℝ) - 2 := by exact_mod_cast (Nat.zero_le (k - 2))
        exact div_nonneg (mul_nonneg (by linarith) hkminus) (le_of_lt (by positivity))
      linarith
    have hclt : c < 1 := by
      dsimp [c]
      have hden : 0 < (6 : ℝ) * (k : ℝ)^3 * Real.sqrt (k : ℝ) := by positivity
      have hk2real : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hkminus : 0 < (k : ℝ) - 1 := by linarith
      have hpos : 0 < ((k : ℝ) - 1) / (2 * (k : ℝ)^2) := by positivity
      have hterm : (((k : ℝ) - 1) * ((k : ℝ) - 2)) /
          (6 * (k : ℝ)^3 * Real.sqrt (k : ℝ)) <
          ((k : ℝ) - 1) / (2 * (k : ℝ)^2) := by
        apply (div_lt_iff₀ hden).2
        have hsquare : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := Real.sq_sqrt (le_of_lt hkreal)
        have hsqrt1 : 1 ≤ Real.sqrt (k : ℝ) := by nlinarith
        field_simp [ne_of_gt hkreal, ne_of_gt hsqrt]
        nlinarith [sq_nonneg (Real.sqrt (k : ℝ) - 1)]
      linarith
    let eps : ℝ := min (iota / 2) ((1 - c) / 2)
    let theta : ℝ := c + eps
    have heps : 0 < eps := lt_min (by linarith) (by linarith)
    have htheta : 0 < theta := by dsimp [theta]; linarith
    have htheta1 : theta < 1 := by
      have he : eps ≤ (1 - c) / 2 := min_le_right _ _
      dsimp [theta]
      linarith
    obtain ⟨Dg, hg⟩ := GeneralColoringTheorem eps k heps hk
    obtain ⟨Db, hb⟩ := KUniformKSimpleBParameterEstimate eps heps k hk
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (3 * ((Db : ℝ) + 1)) / eps < N :=
      exists_nat_gt (3 * ((Db : ℝ) + 1) / eps)
    refine ⟨max Dg N, ?_⟩
    intro D hD V E _ _ _ H hH
    have hDg : Dg ≤ D := le_trans (Nat.le_max_left _ _) hD
    have hDn : N ≤ D := le_trans (Nat.le_max_right _ _) hD
    have hbound : (theta + eps) * (k : ℝ) * (D : ℝ) ≤
        (c + iota) * (k : ℝ) * (D : ℝ) := by
      have he : eps ≤ iota / 2 := min_le_left _ _
      have hcoef : theta + eps ≤ c + iota := by
        dsimp [theta]
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)
    have hout := hg (D : ℝ) (by exact_mod_cast hDg) theta htheta htheta1 H hH.1
      (fun v => by exact_mod_cast hH.2.2 v) (by
      intro (F : Type 0) _ _ D' hD' H' hsub hmax e
      have hcross : 3 * ((Db : ℝ) + 1) < eps * (N : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ heps).mp hN
      have hDreal : (N : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDn
      have hDbreal : (Db : ℝ) + 1 ≤ D' := by
        have hmono : eps * (N : ℝ) ≤ eps * (D : ℝ) :=
          mul_le_mul_of_nonneg_left hDreal (le_of_lt heps)
        nlinarith
      have hDbnat : Db ≤ ⌊D'⌋₊ := Nat.le_floor (by linarith)
      have hinherit := SubhypergraphInheritance H' H hsub
      have hu' := hinherit.1 k hH.1
      have hfloor := LocalBParameterRealFloorTransfer H' hk hu'
        (by have := Nat.cast_nonneg (α := ℝ) Db; linarith) hmax e
      refine hfloor.trans ((hb ⌊D'⌋₊ hDbnat H' ?_ e).trans ?_)
      · exact ⟨hu', hinherit.2.1 k hH.2.1, RealDegreeFloorBound H' hmax⟩
      · simpa [c, theta]
      )
    rcases hout with ⟨q, hq, hcol⟩
    exact ⟨q, by simpa [c] using le_trans hq hbound, hcol⟩
