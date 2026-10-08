import Tablet.SaturatedLineGraphEdgeCount
import Tablet.TablePairBound
import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformSaturatedEdgeStructure

-- [TABLET NODE: ThreeUniformThreeSimplePairLowerBound]
theorem ThreeUniformThreeSimplePairLowerBound :
    ∀ D : ℕ, ∀ {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E],
      ∀ F : MultiHypergraph V E, ∀ f : E,
        ∀ S : ThreeUniformThreeSimpleLocalSetup D F f,
          S.P ≥ (D : ℝ) ^ (2 : ℕ) - 9 * (D : ℝ) + S.Y := by
-- BODY
  classical
  intro D V E _ _ _ _ F f S
  obtain ⟨a, b, c, hab, hac, hbc, hf⟩ :=
    Finset.card_eq_three.mp (S.class_mem.1 f)
  let d : V → V → ℝ := fun v x =>
    ((Finset.univ.filter (fun g : E => v ∈ F.edge g ∧ x ∈ F.edge g)).card : ℝ)
  let w : V → ℝ := fun x => d a x * d b x + d a x * d c x + d b x * d c x
  have hpairs : (Finset.univ : Finset (Finset V)).filter
      (fun p => p.card = 2 ∧ p ⊆ F.edge f) = {{a,b}, {a,c}, {b,c}} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf]
    constructor
    · rintro ⟨hcard, hsub⟩
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      have hu := hsub (by simp : u ∈ ({u,v} : Finset V))
      have hv := hsub (by simp : v ∈ ({u,v} : Finset V))
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv ⊢
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        simp_all [Finset.pair_comm]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl) <;> simp [hab, hac, hbc]
  have habac : ({a,b} : Finset V) ≠ {a,c} := by
    intro h
    have : b ∈ ({a,c} : Finset V) := h ▸ (by simp)
    simp_all
  have habbc : ({a,b} : Finset V) ≠ {b,c} := by
    intro h
    have : a ∈ ({b,c} : Finset V) := h ▸ (by simp)
    simp_all
  have hacbc : ({a,c} : Finset V) ≠ {b,c} := by
    intro h
    have : a ∈ ({b,c} : Finset V) := h ▸ (by simp)
    simp_all
  have hweight (x : V) :
      (∑ p ∈ (Finset.univ : Finset (Finset V)).filter
        (fun p => p.card = 2 ∧ p ⊆ F.edge f), ∏ v ∈ p, d v x) = w x := by
    rw [hpairs]
    simp [w, habac, habbc, hacbc, hab, hac, hbc, add_assoc]
  have hW : S.W = ∑ x ∈ S.X, w x := by
    rw [S.W_split, S.WXs_is_weight_of_Xs, S.WXb_is_weight_of_Xb]
    rw [← Finset.sum_union S.Xs_disjoint_Xb, S.X_partition]
    exact Finset.sum_congr rfl (fun x _ => hweight x)
  let e := (Finset.equivFin S.X).symm
  have hsum (g : V → ℝ) : (∑ j : Fin S.X.card, g (e j).1) = ∑ x ∈ S.X, g x := by
    calc
      _ = ∑ x : S.X, g x.1 := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := Finset.sum_coe_sort S.X g
  let A : Fin 3 → Fin S.X.card → ℝ := fun i j => d (![a,b,c] i) (e j).1
  have hcol (j : Fin S.X.card) : (∑ i : Fin 3, A i j) = S.vertexDegreeIntoF (e j).1 := by
    rw [S.vertexDegreeIntoF_eq, hf]
    simp [A, Fin.sum_univ_succ, hab, hac, hbc, d, add_assoc]
    rfl
  have htotal : (∑ i : Fin 3, ∑ j : Fin S.X.card, A i j) = 6 * ((D : ℝ) - 1) := by
    rw [Finset.sum_comm]
    simp_rw [hcol]
    rw [hsum, ← S.totalX_eq_sum, S.totalX_value]
  have hD : (100 : ℝ) ≤ D := by exact_mod_cast S.D_large
  have hbound := TablePairBound (k := 3) (by decide) (D : ℝ)
    (6 * ((D : ℝ) - 1)) A (by linarith) (by linarith)
    (fun i j => Nat.cast_nonneg _) (fun j => (hcol j).trans_le (S.column_bound _ (e j).2))
    htotal.le
  have hpair (j : Fin S.X.card) :
      (∑ i : Fin 3, ∑ i' : Fin 3, if i < i' then A i j * A i' j else 0) = w (e j).1 := by
    simp [A, w, Fin.sum_univ_succ, add_assoc]
  simp_rw [hpair] at hbound
  rw [hsum, ← hW] at hbound
  norm_num at hbound
  have hid := S.pair_identity
  nlinarith
