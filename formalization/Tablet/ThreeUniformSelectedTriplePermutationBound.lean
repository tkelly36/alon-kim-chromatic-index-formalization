import Tablet.ThreeUniformIndependentTripleRootLabeling
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

-- [TABLET NODE: ThreeUniformSelectedTriplePermutationBound]
theorem ThreeUniformSelectedTriplePermutationBound
    {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (f : E) (v : Fin 3 → V)
    (hcover : ∀ y ∈ H.edge f, ∃ i, v i = y)
    (x : Fin 3 → Option V) (b : Fin 3 → Fin 3 → ℝ)
    (hb : ∀ i j, b i j = (x j).elim 0 (fun y =>
      (((Finset.univ : Finset E).filter
        (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)))
    (T : Finset (Finset E))
    (hT : ∀ S ∈ T, S.card = 3 ∧
      (∀ e ∈ S, (H.edge e ∩ H.edge f).Nonempty) ∧
      (∀ e ∈ S, ∀ g ∈ S, e ≠ g → ¬ (LineGraphOfHypergraph H).Adj e g))
    (hselected : ∀ S ∈ T, ∀ e ∈ S, ∃ j y, x j = some y ∧ y ∈ H.edge e) :
    (T.card : ℝ) ≤
      ∑ p : Equiv.Perm (Fin 3), b 0 (p 0) * b 1 (p 1) * b 2 (p 2) := by
-- BODY
  classical
  have hlabel (S : T) : ∃ q : Fin 3 → E, Finset.univ.image q = S.val ∧
      (∀ i, v i ∈ H.edge (q i)) ∧
      (∀ i e, e ∈ S.val → v i ∈ H.edge e → e = q i) := by
    have h := hT S S.property
    exact ThreeUniformIndependentTripleRootLabeling H f v hcover S h.1 h.2.1 h.2.2
  choose q hq using hlabel
  have hqmem (S : T) (i : Fin 3) : q S i ∈ S.val := by
    rw [← (hq S).1]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hqinj (S : T) : Function.Injective (q S) := by
    have hi : Set.InjOn (q S) ↑(Finset.univ : Finset (Fin 3)) :=
      Finset.card_image_iff.mp (by rw [(hq S).1, (hT S S.property).1]; simp)
    exact fun i j hij => hi (Finset.mem_univ _) (Finset.mem_univ _) hij
  have hchoose (S : T) (i : Fin 3) : ∃ j y, x j = some y ∧ y ∈ H.edge (q S i) :=
    hselected S S.property (q S i) (hqmem S i)
  choose r y hr hy using hchoose
  have hrinj (S : T) : Function.Injective (r S) := by
    intro i j hij
    by_contra hne
    have he := hqinj S |>.ne hne
    have hyij : y S i = y S j := Option.some.inj ((hr S i).symm.trans
      (hij ▸ hr S j))
    exact (hT S S.property).2.2 _ (hqmem S i) _ (hqmem S j) he
      ⟨he, ⟨y S i, Finset.mem_inter.mpr ⟨hy S i, hyij ▸ hy S j⟩⟩⟩
  let p (S : T) : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective (r S) ((Finite.injective_iff_bijective).mp (hrinj S))
  let F (p : Equiv.Perm (Fin 3)) (i : Fin 3) : Finset E :=
    Finset.univ.filter (fun e => v i ∈ H.edge e ∧
      ∃ y, x (p i) = some y ∧ y ∈ H.edge e)
  let R := Finset.univ.sigma (fun p : Equiv.Perm (Fin 3) => Fintype.piFinset (F p))
  have hmem (S : T) : (⟨p S, q S⟩ : (p : Equiv.Perm (Fin 3)) × (Fin 3 → E)) ∈ R := by
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hq S).2.1 i,
      y S i, hr S i, hy S i⟩
  let Q : T → R := fun S => ⟨⟨p S, q S⟩, hmem S⟩
  have hinj : Function.Injective Q := by
    intro S U heq
    apply Subtype.ext
    have hqu : q S = q U := congrArg (fun z : R => z.val.2) heq
    rw [← (hq S).1, ← (hq U).1, hqu]
  have hc : T.card ≤ R.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective Q hinj
  have hF (p : Equiv.Perm (Fin 3)) (i : Fin 3) : ((F p i).card : ℝ) = b i (p i) := by
    rw [hb]
    cases hx : x (p i) with
    | none => simp [F, hx]
    | some y => simp [F, hx]
  have hR : (R.card : ℝ) =
      ∑ p : Equiv.Perm (Fin 3), b 0 (p 0) * b 1 (p 1) * b 2 (p 2) := by
    simp only [R, Finset.card_sigma, Fintype.card_piFinset, Nat.cast_sum, Nat.cast_prod]
    simp_rw [hF]
    apply Finset.sum_congr rfl
    intro p hp
    simp [Fin.prod_univ_succ, mul_assoc]
  rw [← hR]
  exact_mod_cast hc
