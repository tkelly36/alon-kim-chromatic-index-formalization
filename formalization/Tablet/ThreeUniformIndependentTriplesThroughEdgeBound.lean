import Tablet.ThreeUniformIndependentTripleRootLabeling
import Tablet.HypergraphDegree
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

-- [TABLET NODE: ThreeUniformIndependentTriplesThroughEdgeBound]
theorem ThreeUniformIndependentTriplesThroughEdgeBound
    {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : MultiHypergraph V E) (f : E) (v : Fin 3 → V)
    (hcover : ∀ y ∈ H.edge f, ∃ i, v i = y)
    (D : ℕ) (hdegree : ∀ i, HypergraphDegree H (v i) = D)
    (T : Finset (Finset E))
    (hT : ∀ S ∈ T, S.card = 3 ∧
      (∀ e ∈ S, (H.edge e ∩ H.edge f).Nonempty) ∧
      (∀ e ∈ S, ∀ g ∈ S, e ≠ g → ¬ (LineGraphOfHypergraph H).Adj e g))
    (g : E) (i : Fin 3) (hgi : v i ∈ H.edge g) :
    (T.filter (fun S => g ∈ S)).card ≤ D ^ 2 := by
-- BODY
  classical
  let U := T.filter (fun S => g ∈ S)
  have hlabel (S : U) : ∃ q : Fin 3 → E, Finset.univ.image q = S.val ∧
      (∀ j, v j ∈ H.edge (q j)) ∧
      (∀ j e, e ∈ S.val → v j ∈ H.edge e → e = q j) := by
    have h := hT S.val (Finset.mem_filter.mp S.property).1
    exact ThreeUniformIndependentTripleRootLabeling H f v hcover S.val h.1 h.2.1 h.2.2
  choose q hq using hlabel
  let F : Fin 3 → Finset E := fun j =>
    if j = i then {g} else Finset.univ.filter (fun e => v j ∈ H.edge e)
  have hmem (S : U) : q S ∈ Fintype.piFinset F := by
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hji : j = i
    · subst j
      have hg := (hq S).2.2 i g (Finset.mem_filter.mp S.property).2 hgi
      simp [F, ← hg]
    · simp [F, hji, (hq S).2.1 j]
  let Q : U → Fintype.piFinset F := fun S => ⟨q S, hmem S⟩
  have hinj : Function.Injective Q := by
    intro S R heq
    apply Subtype.ext
    have hqr : q S = q R := congrArg Subtype.val heq
    rw [← (hq S).1, ← (hq R).1, hqr]
  have hc := Fintype.card_le_of_injective Q hinj
  have hF : (Fintype.piFinset F).card = D ^ 2 := by
    rw [Fintype.card_piFinset]
    have hf (j : Fin 3) : (F j).card = if j = i then 1 else D := by
      by_cases hji : j = i
      · simp [F, hji]
      · simpa [F, hji, HypergraphDegree] using hdegree j
    simp_rw [hf]
    fin_cases i <;> simp [Fin.prod_univ_succ, pow_two]
  simpa only [Fintype.card_coe, hF] using hc
