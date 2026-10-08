import Tablet.Preamble
import Tablet.SaturatedEdgeStructure
import Tablet.SaturatedLineGraphPairBound
import Tablet.TablePairBound

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleSmallPairsBound]
theorem ThreeUniformTwoSimpleSmallPairsBound :
    ∀ D : ℕ, ∀ C P : ℝ,
      C = (D : ℝ) ^ ((2 : ℝ) / 3) →
      ∀ {V E : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
          ∀ f : E, ∀ v : Fin 3 → V,
            (∀ i : Fin 3, v i ∈ H.edge f) →
            (∀ y : V, y ∈ H.edge f → ∃ i : Fin 3, v i = y) →
            (((Finset.univ : Finset E).filter
                (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)).card =
              3 * (D - 1)) →
            ∀ X Xs Xb : Finset V, ∀ a : Fin 3 → V → ℝ, ∀ w : Finset V → ℝ,
              (∀ x : V, x ∈ X ↔
                x ∉ H.edge f ∧ ∃ e : E, e ≠ f ∧ x ∈ H.edge e ∧
                  (H.edge e ∩ H.edge f).Nonempty) →
              (∀ e : E, e ≠ f → (H.edge e ∩ H.edge f).Nonempty →
                (H.edge e ∩ H.edge f).card = 1) →
              (∀ x ∈ X, (∑ i : Fin 3, a i x) ≤ (D : ℝ)) →
              (∀ i : Fin 3, (∑ x ∈ X, a i x) = 2 * ((D : ℝ) - 1)) →
              (∀ i x, 0 ≤ a i x) →
              Xs = X.filter (fun x => (∑ i : Fin 3, a i x) < C) →
              Xb = X \ Xs →
              (∀ Y : Finset V, Y ⊆ X →
                w Y = ∑ x ∈ Y, ∑ i : Fin 3, ∑ j : Fin 3,
                  (if i < j then a i x * a j x else 0)) →
              P ≥ 3 * (D : ℝ) ^ (2 : ℕ) - 6 * (D : ℝ) + 3 - w X →
              w Xs ≤ 2 * (D : ℝ) ^ ((5 : ℝ) / 3) ∧
                P ≥ 3 * (D : ℝ) ^ (2 : ℕ) - 6 * (D : ℝ) + 3 -
                  w Xb - 2 * (D : ℝ) ^ ((5 : ℝ) / 3) := by
-- BODY
  classical
  intro D C P hC V E _ _ _ _ H hH f v hv hcover hsat
    X Xs Xb a w hX hone hcol hrow hnonneg hXs hXb hw hP
  have hD : (1 : ℝ) ≤ D := by
    have h := Finset.sum_nonneg (s := X) (fun x _ => hnonneg (0 : Fin 3) x)
    rw [hrow] at h
    linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have hCpos : 0 < C := hC.symm ▸ Real.rpow_pos_of_pos hDpos _
  have hs : Xs ⊆ X := by rw [hXs]; exact Finset.filter_subset _ _
  have hb : Xb ⊆ X := by rw [hXb]; exact Finset.sdiff_subset
  let e := (Finset.equivFin Xs).symm
  have hsum (g : V → ℝ) : (∑ j : Fin Xs.card, g (e j).1) = ∑ x ∈ Xs, g x := by
    calc
      _ = ∑ x : Xs, g x.1 := e.sum_comp (fun x : Xs => g x.1)
      _ = _ := Finset.sum_coe_sort Xs g
  have htotal : (∑ i : Fin 3, ∑ j : Fin Xs.card, a i (e j).1) ≤ 6 * (D : ℝ) := by
    simp_rw [hsum]
    calc
      _ ≤ ∑ i : Fin 3, ∑ x ∈ X, a i x := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ => hnonneg i x)
      _ = 6 * ((D : ℝ) - 1) := by simp [hrow]; ring
      _ ≤ _ := by linarith
  have hbound := TablePairBound (k := 3) (n := Xs.card) (by decide) C
    (6 * (D : ℝ)) (fun i j => a i (e j).1) hCpos (by positivity)
    (fun i j => hnonneg i (e j).1)
    (fun j => by
      have hj := (e j).2
      have hj' : (e j).1 ∈ X.filter (fun x => (∑ i : Fin 3, a i x) < C) :=
        hXs ▸ hj
      exact (Finset.mem_filter.mp hj').2.le) htotal
  have hpower : (D : ℝ) * C = (D : ℝ) ^ ((5 : ℝ) / 3) := by
    rw [hC]
    have hp := Real.rpow_add hDpos (1 : ℝ) ((2 : ℝ) / 3)
    norm_num at hp
    exact hp.symm
  have hsmall : w Xs ≤ 2 * (D : ℝ) ^ ((5 : ℝ) / 3) := by
    rw [hsum (fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      if i < j then a i x * a j x else 0)] at hbound
    rw [hw Xs hs]
    calc
      _ ≤ (((3 : ℝ) - 1) / (2 * 3)) * (6 * (D : ℝ)) * C := hbound
      _ = 2 * ((D : ℝ) * C) := by ring
      _ = _ := by rw [hpower]
  have hadd : w X = w Xb + w Xs := by
    rw [hw X (Finset.Subset.refl X), hw Xb hb, hw Xs hs, hXb]
    exact (Finset.sum_sdiff hs).symm
  exact ⟨hsmall, by rw [hadd] at hP; linarith⟩
