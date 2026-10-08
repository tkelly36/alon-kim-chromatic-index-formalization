import Tablet.IndependentSetSamplingBound
import Tablet.SamplingRegularGraphSamplingLawExists
import Tablet.FiniteSimpleRegularCompletion
import Tablet.HypergraphClass
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.HypergraphDegree
import Tablet.SubhypergraphOf
import Tablet.NibbleResidualDegreeBoundedDifference
import Tablet.NibbleRegularCompletionsExist
import Tablet.NibbleExpectationBounds
import Tablet.NibbleConcentrationBounds
import Tablet.NibbleCompletedDependencyBound
import Tablet.NibbleFiniteLocalLemma
import Tablet.NibbleNumericalThresholds
import Tablet.NibbleDeterministicExtraction

-- [TABLET NODE: OneNibblePartialColoring]
theorem OneNibblePartialColoring (A k : ℕ) (iota : ℝ) (hiota : 0 < iota) :
    ∃ gamma0 : ℕ, ∀ gamma : ℕ, gamma0 ≤ gamma →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            UniformHypergraph H k → MaxDegreeAtMost H D →
            ∀ L : E → Finset (Fin (A * D)),
            (∀ e : E,
              Int.ceil ((k : ℝ) * (D : ℝ) / (gamma : ℝ)) ≤ ((L e).card : ℤ)) →
            ∀ b : ℝ,
              (∀ e : E,
                @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                  (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) e ≤ b) →
              ∃ C : Finset E,
              ∃ c : {e : E // e ∈ C} → Fin (A * D),
                (∀ e : {e : E // e ∈ C}, c e ∈ L e.1) ∧
                (∀ e f : {e : E // e ∈ C}, e ≠ f →
                  (H.edge e.1 ∩ H.edge f.1).Nonempty → c e ≠ c f) ∧
                ∃ (F : Type*) (_ : Fintype F) (_ : DecidableEq F),
                ∃ embed : F → E,
                ∃ Hc : MultiHypergraph V F,
                ∃ Lc : F → Finset (Fin (A * D)),
                  (∀ f : F, Hc.edge f = H.edge (embed f)) ∧
                  (∀ e : E, e ∉ C ↔ ∃ f : F, embed f = e) ∧
                  (∀ f : F, ∀ alpha : Fin (A * D),
                    alpha ∈ Lc f ↔
                      alpha ∈ L (embed f) ∧
                        ∀ e : {e : E // e ∈ C},
                          c e = alpha → ¬ (H.edge e.1 ∩ H.edge (embed f)).Nonempty) ∧
                  (∀ v : V,
                    (HypergraphDegree Hc v : ℝ) ≤
                      (1 - (1 - iota) / (gamma : ℝ)) * (D : ℝ)) ∧
                  (∀ f : F,
                    (1 - b - iota) *
                        (Int.ceil ((k : ℝ) * (D : ℝ) / (gamma : ℝ)) : ℝ) ≤
                      ((Lc f).card : ℝ)) := by
-- BODY
  classical
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, ?_⟩
    intro gamma hg
    refine ⟨1, ?_⟩
    intro D hD V E instE instDE instDV H hu hd L hL b hb
    have hedge (e : E) : H.edge e = ∅ := Finset.card_eq_zero.mp (hu e)
    let c : {e : E // e ∈ (∅ : Finset E)} → Fin (A * D) :=
      fun e => False.elim (Finset.notMem_empty e.val e.property)
    let eqv := Fintype.equivFin E
    refine ⟨∅, c, ?_, ?_, ULift (Fin (Fintype.card E)), inferInstance, inferInstance,
      (fun f => eqv.symm f.down), ⟨fun _ => ∅⟩,
      (fun f => L (eqv.symm f.down)), ?_, ?_, ?_, ?_, ?_⟩
    · intro e
      exact False.elim (Finset.notMem_empty e.val e.property)
    · intro e
      exact False.elim (Finset.notMem_empty e.val e.property)
    · intro f
      exact (hedge _).symm
    · intro e
      constructor
      · intro _
        exact ⟨⟨eqv e⟩, eqv.symm_apply_apply e⟩
      · intro _
        exact Finset.notMem_empty e
    · intro f a
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, and_true]
    · intro x
      simp only [HypergraphDegree, Finset.notMem_empty, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero]
      have hgR : (1 : ℝ) ≤ gamma := by exact_mod_cast hg
      have hgpos : (0 : ℝ) < gamma := by linarith
      have hdiv : (1 - iota) / (gamma : ℝ) ≤ 1 :=
        (div_le_one hgpos).mpr (by linarith)
      exact mul_nonneg (sub_nonneg.mpr hdiv) (Nat.cast_nonneg D)
    · intro f
      simp
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  by_cases hA0 : A = 0
  · subst A
    refine ⟨1, ?_⟩
    intro gamma hg
    refine ⟨1, ?_⟩
    intro D hD V E instE instDE instDV H hu hd L hL b hb
    have hempty : IsEmpty E := by
      constructor
      intro e
      have hpos : 0 < Int.ceil ((k : ℝ) * D / gamma) := by positivity
      have he := hL e
      have hcard : (L e).card = 0 := by
        have hem : L e = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a _
          have := a.isLt
          omega
        simp [hem]
      rw [hcard] at he
      omega
    letI := hempty
    refine ⟨∅, (fun e => isEmptyElim e.val), ?_, ?_,
      ULift (Fin 0), inferInstance, inferInstance, (fun f => Fin.elim0 f.down),
      ⟨fun _ => ∅⟩, (fun _ => ∅), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun e => isEmptyElim e.val
    · exact fun e => isEmptyElim e.val
    · exact fun f => Fin.elim0 f.down
    · exact fun e => isEmptyElim e
    · exact fun f => Fin.elim0 f.down
    · intro x
      simp only [HypergraphDegree, Finset.notMem_empty, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero]
      have hgR : (1 : ℝ) ≤ gamma := by exact_mod_cast hg
      have hgpos : (0 : ℝ) < gamma := by linarith
      have hdiv : (1 - iota) / (gamma : ℝ) ≤ 1 :=
        (div_le_one hgpos).mpr (by linarith)
      exact mul_nonneg (sub_nonneg.mpr hdiv) (Nat.cast_nonneg D)
    · exact fun f => Fin.elim0 f.down
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr hA0
  obtain ⟨Ds, gs, hs⟩ := NibbleExpectationBounds (iota / 2) (by linarith)
  obtain ⟨gn, hgn, hn⟩ := NibbleNumericalThresholds A k hA hk iota hiota
  refine ⟨max gs gn, ?_⟩
  intro gamma hg
  have hgg : gn ≤ gamma := (le_max_right _ _).trans hg
  have hgpos : 0 < gamma := lt_of_lt_of_le Nat.zero_lt_one (hgn.trans hgg)
  have hgR : 0 < (gamma : ℝ) := by exact_mod_cast hgpos
  obtain ⟨Dn, hDn, hnD⟩ := hn gamma hgg
  refine ⟨max Ds Dn, ?_⟩
  intro D hD V E instE instDE instDV H hu hd L hL b hb
  have hDDn : Dn ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 ≤ D := hDn.trans hDDn
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD1
  let ell := Nat.ceil ((k : ℝ) * D / gamma)
  obtain ⟨hgDelta, hell, hpow, htail1, htail2, hsmall⟩ := hnD D hDDn
  have hnonneg : 0 ≤ (k : ℝ) * D / gamma := by positivity
  have hceil : (ell : ℤ) = Int.ceil ((k : ℝ) * D / gamma) :=
    Int.natCast_ceil_eq_ceil hnonneg
  have hlist (e : E) : ell ≤ (L e).card := by
    have hh := hL e
    rw [← hceil] at hh
    exact_mod_cast hh
  choose M hML hM using fun e => Finset.exists_subset_card_eq (hlist e)
  obtain ⟨Q⟩ := NibbleRegularCompletionsExist H M k D hu hd
  let ν := NibbleProductMeasure (T := Sigma fun a => Fin (Q.size a))
    ((gamma : ℝ) / (k * D : ℕ))
  let d : ℝ := (1 - (1 - iota) / gamma) * D
  let z : ℝ := (b + iota) * ell
  have hd0 : 0 ≤ d := by
    dsimp [d]
    have hg1 : (1 : ℝ) ≤ gamma := by exact_mod_cast hgn.trans hgg
    have : (1 - iota) / (gamma : ℝ) ≤ 1 :=
      (div_le_one hgR).mpr (by linarith)
    exact mul_nonneg (sub_nonneg.mpr this) hDR.le
  have hgDeltaR : (gamma : ℝ) ≤ (k * D : ℕ) := by exact_mod_cast hgDelta
  have hDs : Ds ≤ k * D :=
    ((le_max_left _ _).trans hD).trans (by nlinarith)
  have hgs : (gs : ℝ) ≤ gamma := by
    exact_mod_cast (le_max_left gs gn).trans hg
  have hline (e : E) : ((LineGraphOfHypergraph H).neighborSet e).ncard ≤ k * D := by
    have hh := (UniformHypergraphLineDegreeBound H hu hd e).trans
      (Nat.mul_le_mul_left k (Nat.sub_le D 1))
    rw [Set.ncard_eq_toFinset_card']
    simpa only [Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree] using hh
  obtain ⟨hEY, hEZ⟩ := hs (k * D) D ell gamma hDs hgs hgR hgDeltaR
    H M hd hM hline b hb Q
  have hmargin (x : V) :
      (∫ ω, (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) ∂ν) ≤
        d - iota * D / (2 * gamma) := by
    have hh := (hEY x).trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hDR))
    convert hh using 1 <;> dsimp [d] <;> ring
  obtain ⟨hconY, hconZ⟩ := NibbleConcentrationBounds Q gamma iota
    (iota * D / (2 * gamma)) d b hgR hgDeltaR hiota (by positivity)
    (by simpa using Nat.mul_pos (by omega : 0 < A) (by omega : 0 < D)) ell hell hM
  obtain ⟨hmeas, S, hdet, _, _, hdep⟩ :=
    NibbleCompletedDependencyBound A k D hk hD1 H hu hd M Q d z
  have hprob (j : {x : V // x ∈ (Finset.univ : Finset E).biUnion H.edge} ⊕ E) :
      ν (NibbleBadEvent Q d z j) ≤ ENNReal.ofReal (Real.exp (-(Real.log D)^2)) := by
    cases j with
    | inl x =>
        have ht := hconY x.val (hmargin x.val)
        have hexp : Real.exp (-2 * (iota * D / (2 * gamma))^2 /
            Fintype.card (Fin (A * D))) =
            Real.exp (-(iota^2 / (2 * (gamma : ℝ)^2 * A)) * D) := by
          congr 1
          simp only [Fintype.card_fin, Nat.cast_mul]
          field_simp
          <;> ring
        exact ht.trans (by rw [hexp]; exact ENNReal.ofReal_le_ofReal htail1)
    | inr e =>
        exact (hconZ e (hEZ e)).trans (ENNReal.ofReal_le_ofReal htail2)
  obtain ⟨_, ω, hgood⟩ := NibbleFiniteLocalLemma
    ((gamma : ℝ) / (k * D : ℕ)) (Real.exp (-(Real.log D)^2))
    (by positivity) ((div_le_one (by positivity)).mpr hgDeltaR)
    (Real.exp_pos _).le (4 * A * (k + 1) * k^4 * D^6)
    (by apply Nat.succ_le_of_lt; positivity) hsmall (NibbleBadEvent Q d z) S hmeas hdet hprob hdep
  have hYgood (x : V) : (NibbleResidualDegree H (NibbleSelectedEdges Q ω) x : ℝ) ≤ d := by
    by_cases hx : x ∈ (Finset.univ : Finset E).biUnion H.edge
    · exact le_of_not_gt (hgood (Sum.inl ⟨x, hx⟩))
    · have he : ∀ e : E, x ∉ H.edge e := by
        intro e he
        exact hx (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, he⟩)
      simpa [NibbleResidualDegree, he] using hd0
  have hZgood (e : E) :
      ((NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e).card : ℝ) < z :=
    lt_of_not_ge (hgood (Sum.inr e))
  have hind := (NibbleProductSamplingLaw Q gamma hgR hgDeltaR).2.2.2.2.1 ω
  obtain ⟨C, c, hC, hcL, hcproper, Lc, hLc, hdegree, hLcsize⟩ :=
    NibbleDeterministicExtraction H L M (NibbleSelectedEdges Q ω) hML
      (by
        intro a e he
        obtain ⟨ha, _⟩ := (Finset.mem_filter.mp he).2
        exact ha) hind
  let F0 := {e // e ∉ C}
  let equivF := Fintype.equivFin F0
  refine ⟨C, c, hcL, hcproper, ULift (Fin (Fintype.card F0)), inferInstance, inferInstance,
    (fun f => (equivF.symm f.down).val), ⟨fun f => H.edge (equivF.symm f.down).val⟩,
    (fun f => Lc (equivF.symm f.down)), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rfl
  · intro e
    constructor
    · intro he
      refine ⟨⟨equivF ⟨e, he⟩⟩, ?_⟩
      simp
    · rintro ⟨f, rfl⟩
      exact (equivF.symm f.down).property
  · intro f a
    exact hLc (equivF.symm f.down) a
  · intro x
    have hcard : HypergraphDegree
        (⟨fun f : ULift (Fin (Fintype.card F0)) => H.edge (equivF.symm f.down).val⟩ :
          MultiHypergraph V (ULift (Fin (Fintype.card F0)))) x =
        HypergraphDegree (⟨fun f : F0 => H.edge f.val⟩ : MultiHypergraph V F0) x := by
      unfold HypergraphDegree
      apply Finset.card_bij (fun f _ => equivF.symm f.down)
      · intro f hf
        simpa using hf
      · intro f _ g _ h
        exact ULift.ext _ _ (equivF.symm.injective h)
      · intro f hf
        refine ⟨⟨equivF f⟩, ?_, ?_⟩ <;> simpa using hf
    rw [hcard, hdegree]
    exact hYgood x
  · intro f
    let f0 := equivF.symm f.down
    have hdel : (NibbleDeletedColors H M (NibbleSelectedEdges Q ω) f0.val).card ≤ ell := by
      rw [← hM f0.val]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hc : (ell : ℝ) - (NibbleDeletedColors H M (NibbleSelectedEdges Q ω) f0.val).card ≤
        (Lc f0).card := by
      have hh := hLcsize f0
      rw [hM f0.val] at hh
      have hhR := (Nat.cast_le (α := ℝ)).mpr hh
      rwa [Nat.cast_sub hdel] at hhR
    have hz := hZgood f0.val
    rw [← hceil]
    push_cast
    dsimp [z] at hz
    nlinarith
