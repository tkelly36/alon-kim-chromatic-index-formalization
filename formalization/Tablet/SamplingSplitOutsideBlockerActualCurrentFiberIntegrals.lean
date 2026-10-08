import Tablet.SamplingFiniteProductContextSlicing
import Tablet.SamplingSplitOutsideBlockerProductRealization
import Tablet.SamplingSplitOutsideBlockerProductAtomContextInvariant
import Tablet.SamplingSplitOutsideBlockerPairedContextCurrentInvariant
import Tablet.SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer
import Tablet.SamplingSplitOutsideBlockerCurrentTagSeparation

open MeasureTheory
universe u

-- [TABLET NODE: SamplingSplitOutsideBlockerActualCurrentFiberIntegrals]
theorem SamplingSplitOutsideBlockerActualCurrentFiberIntegrals
    {V V' Ω : Type u} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] [Fintype Ω]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph V') [DecidableRel G'.Adj]
    (φ : V → V') (r : V) (X : Finset V)
    (n : ℕ) (zAt : Fin n → V) (B : Fin n → Finset V)
    (hOutside : ∀ i : Fin n, zAt i ∉ insert r X)
    (β : (Σ x : {x : V // x ∈ X},
      {z : V // z ∉ insert r X ∧ G.Adj x.1 z}) → V')
    (cell : Ω → Set (Finset V × (V → ℝ)))
    (targetCell : Ω → Set (Finset V' × (V' → ℝ))) (w : Ω → ℝ)
    (surface : SamplingSplitOutsideBlockerPairedMixedMeasureSurface
      G G' φ r X n zAt B hOutside β cell targetCell w)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (product : SamplingSplitOutsideBlockerProductRealization
      p φ surface.sourceCoord surface.pairedMeasure)
    (hβ : Function.Injective β)
    (hFresh : ∀ a, ∀ y ∈ insert r X, β a ≠ φ y)
    (hcurrent : ∀ i, zAt i ∉ surface.sourceCoord)
    (hprivate : ∀ i (x : {x : V // x ∈ X})
      (hz : zAt i ∉ insert r X ∧ G.Adj x.1 (zAt i)),
      β ⟨x, ⟨zAt i, hz⟩⟩ ∉ surface.targetCommonCoord)
    (hcell : ∀ ω, @MeasurableSet (Finset V × (V → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance) (cell ω))
    (hcell' : ∀ ω, @MeasurableSet (Finset V' × (V' → ℝ))
      (MeasurableSpace.prod ⊤ inferInstance) (targetCell ω))
    (htransport : ∀ ω η η',
      η'.1 ∩ surface.targetCommonCoord = (η.1 ∩ surface.sourceCoord).image φ →
      (∀ v ∈ surface.sourceCoord, η'.2 (φ v) = η.2 v) →
        (η ∈ cell ω ↔ η' ∈ targetCell ω))
    (hpaired : ∀ ω, surface.pairedCell ω =
      {ζ : (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) |
        ζ.1 ∈ cell ω ∧ ζ.2 ∈ targetCell ω ∧
        ζ.2.1 ∩ surface.targetCommonCoord =
          (ζ.1.1 ∩ surface.sourceCoord).image φ ∧
        ∀ v ∈ surface.sourceCoord, ζ.2.2 (φ v) = ζ.1.2 v})
    (k : Fin n) (ω : Ω) :
    letI : Fintype product.Tag := product.finiteTag
    letI : DecidableEq product.Tag := Classical.decEq _
    letI : MeasurableSpace (Finset V) := ⊤
    letI : MeasurableSpace (Finset V') := ⊤
    let A := {x : {x : V // x ∈ X} // x.1 ∈ B k}
    let j : Option A → product.Tag := fun a => match a with
      | none => product.sourceTag (zAt k)
      | some a => product.targetTag (β ⟨a.1, ⟨zAt k,
          hOutside k, ((surface.candidate_sets k a.1.1).mp a.2).2⟩⟩)
    let J := Finset.univ.image j
    let ρ := (ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))
    let τ := Measure.pi (fun _ : {i : product.Tag // i ∉ J} => ρ)
    let κ := Measure.pi (fun _ : Option A => ρ)
    let d := fun (t : {i : product.Tag // i ∉ J} → ℝ × ℝ) =>
      SamplingSplitOutsideBlockerProductDecode product.sourceTag product.targetTag
        (fun i => if hi : i ∈ J then (0, 0) else t ⟨i, hi⟩)
    let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
      (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
    let U := {ζ | ∃ x : {x : V // x ∈ X}, x.1 ∉ B k ∧ ζ ∈ C x}
    let K := fun t => @Finset.filter A (fun a => d t ∈ C a.1)
      (Classical.decPred _) Finset.univ
    let q := fun t (a : A) => (d t).1.2 a.1.1
    let gate := {t | d t ∈ surface.pairedCell ω ∧ d t ∉ U}
    let L := fun t => {f : Option A → ℝ × ℝ | ∃ a ∈ K t,
      ¬ ((f none).1 = 1 ∧ q t a < (f none).2 ∧
        (f none).2 ∈ Set.Icc (0 : ℝ) 1)}
    let R := fun t => {f : Option A → ℝ × ℝ | ∃ a ∈ K t,
      ¬ ((f (some a)).1 = 1 ∧ q t a < (f (some a)).2 ∧
        (f (some a)).2 ∈ Set.Icc (0 : ℝ) 1)}
    MeasurableSet (surface.pairedCell ω) ∧
      (∀ᵐ t ∂τ, ∀ a : A, q t a ∈ Set.Icc (0 : ℝ) 1) ∧
      surface.pairedMeasure ((surface.mixedStage k ω \ U) ∩ surface.pairedCell ω) =
        ∫⁻ t, gate.indicator (fun t => κ (L t)) t ∂τ ∧
      surface.pairedMeasure ((surface.mixedStage (k.val + 1) ω \ U) ∩
          surface.pairedCell ω) =
        ∫⁻ t, gate.indicator (fun t => κ (R t)) t ∂τ := by
-- BODY
  classical
  letI : Fintype product.Tag := product.finiteTag
  letI : DecidableEq product.Tag := Classical.decEq _
  letI : MeasurableSpace (Finset V) := ⊤
  letI : MeasurableSpace (Finset V') := ⊤
  dsimp only
  let A := {x : {x : V // x ∈ X} // x.1 ∈ B k}
  let b : A → V' := fun a => β ⟨a.1, ⟨zAt k,
    hOutside k, ((surface.candidate_sets k a.1.1).mp a.2).2⟩⟩
  have hb : Function.Injective b := by
    intro a a' he
    apply Subtype.ext
    exact congrArg (fun c => c.1) (hβ he)
  obtain ⟨hj, hsource, htarget, hcommon⟩ :=
    SamplingSplitOutsideBlockerCurrentTagSeparation φ
      surface.sourceCoord surface.targetCommonCoord surface.targetCommonCoord_eq
      product.sourceTag product.targetTag product.source_injective
      product.target_injective product.overlap (zAt k) (hcurrent k) b hb
      (fun a => hprivate k a.1 _)
  let j : Option A → product.Tag := fun a => match a with
    | none => product.sourceTag (zAt k)
    | some a => product.targetTag (b a)
  let J := Finset.univ.image j
  let ρ := (ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1))
  let τ := Measure.pi (fun _ : {i : product.Tag // i ∉ J} => ρ)
  let κJ := Measure.pi (fun _ : {i : product.Tag // i ∈ J} => ρ)
  let F := fun (t : {i : product.Tag // i ∉ J} → ℝ × ℝ)
    (c : {i : product.Tag // i ∈ J} → ℝ × ℝ) (i : product.Tag) =>
      if hi : i ∈ J then c ⟨i, hi⟩ else t ⟨i, hi⟩
  let D := SamplingSplitOutsideBlockerProductDecode product.sourceTag product.targetTag
  obtain ⟨hF, hF0, hμ, hτ, hκJ, hsupp, hslice⟩ :=
    SamplingFiniteProductContextSlicing p hp hp' J
  have hcandidate (x : {x : V // x ∈ X}) : product.sourceTag x.1 ∉ J :=
    hcommon x.1 (surface.sourceCoord_contains_embedded x.1
      (Finset.mem_insert_of_mem x.2))
  have hQ : MeasurableSet (surface.pairedCell ω) := by
    rw [hpaired]
    apply MeasurableSet.inter ((hcell ω).preimage measurable_fst)
    apply MeasurableSet.inter ((hcell' ω).preimage measurable_snd)
    apply MeasurableSet.inter
    · have hm : Measurable (fun ζ : (Finset V × (V → ℝ)) ×
          (Finset V' × (V' → ℝ)) => (ζ.1.1, ζ.2.1)) :=
        measurable_fst.fst.prodMk measurable_snd.fst
      exact (MeasurableSet.of_discrete : MeasurableSet
        {a : Finset V × Finset V' | a.2 ∩ surface.targetCommonCoord =
          (a.1 ∩ surface.sourceCoord).image φ}).preimage hm
    · exact (Measurable.forall fun v => Measurable.forall fun _ =>
        (measurableSet_eq_fun ((measurable_pi_apply (φ v)).comp measurable_snd.snd)
          ((measurable_pi_apply v).comp measurable_fst.snd)).mem).setOf
  have hzero (t) (c) (i) (hi : i ∉ J) :
      F t c i = F t (fun _ => (0, 0)) i := by
    simp only [F, dif_neg hi]
  have hQfiber (t) (c) :
      D (F t c) ∈ surface.pairedCell ω ↔
        D (F t (fun _ => (0, 0))) ∈ surface.pairedCell ω := by
    rw [hpaired]
    exact (SamplingSplitOutsideBlockerProductAtomContextInvariant φ
      surface.sourceCoord surface.targetCommonCoord surface.targetCommonCoord_eq
      product.sourceTag product.targetTag product.overlap
      (cell ω) (targetCell ω) (htransport ω)).2 _ _
        (fun v hv => hzero t c _ (hcommon v hv))
  let C := SamplingSplitOutsideBlockerPairedCandidateEvent G φ r X zAt B β
    (Finset.univ.filter (fun i => i < k)) (Finset.univ.filter (fun i => k < i))
  have hCfiber (t) (c) (x) :
      D (F t c) ∈ C x ↔ D (F t (fun _ => (0, 0))) ∈ C x := by
    apply SamplingSplitOutsideBlockerPairedContextCurrentInvariant G φ r X zAt B β
      surface.zAt_injective hβ hOutside hFresh k
    · intro v hv
      have he := hzero t c _ (fun h => hv ((hsource v).mp h))
      simp only [D, SamplingSplitOutsideBlockerProductDecode, Finset.mem_filter,
        Finset.mem_univ, true_and, he, and_self]
    · intro v' hv'
      have hn : product.targetTag v' ∉ J := by
        intro h
        obtain ⟨a, ha⟩ := (htarget v').mp h
        exact hv' a.1 _ ha.symm
      have he := hzero t c _ hn
      simp only [D, SamplingSplitOutsideBlockerProductDecode, Finset.mem_filter,
        Finset.mem_univ, true_and, he, and_self]
  let e : Option A ≃ {i : product.Tag // i ∈ J} :=
    Equiv.ofBijective (fun a => ⟨j a, Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, rfl⟩⟩) ⟨fun a a' h => hj (congrArg Subtype.val h), by
        intro i
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp i.2
        exact ⟨a, Subtype.ext ha⟩⟩
  have hρ : ρ Set.univ = 1 := by
    let activation := ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)
    have ha : activation Set.univ = 1 := by
      simp [activation, ← ENNReal.ofReal_add hp (sub_nonneg.mpr hp')]
    letI : IsProbabilityMeasure activation := ⟨ha⟩
    letI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      ⟨by simp⟩
    exact @measure_univ _ _ (activation.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) _
  letI : IsProbabilityMeasure ρ := ⟨hρ⟩
  have hreindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Option A => ℝ × ℝ) e.symm)
      κJ (Measure.pi (fun _ : Option A => ρ)) :=
    measurePreserving_piCongrLeft (fun _ : Option A => ρ) e.symm
  let P := MeasurableEquiv.piCongrLeft (fun _ : Option A => ℝ × ℝ) e.symm
  have hP (c : {i : product.Tag // i ∈ J} → ℝ × ℝ) (a : Option A) :
      P c a = F (fun _ => (0, 0)) c (j a) := by
    have hjmem : j a ∈ J := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have he := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Option A => ℝ × ℝ)
      e.symm c (e a)
    simp only [Equiv.symm_apply_apply] at he
    exact he.trans (by simp only [F, dif_pos hjmem]; rfl)
  let d := fun t => D (F t (fun _ => (0, 0)))
  let U := {ζ | ∃ x : {x : V // x ∈ X}, x.1 ∉ B k ∧ ζ ∈ C x}
  let K := fun t => Finset.univ.filter (fun a : A => d t ∈ C a.1)
  let q := fun t (a : A) => (d t).1.2 a.1.1
  let gate := {t | d t ∈ surface.pairedCell ω ∧ d t ∉ U}
  let L := fun t => {f : Option A → ℝ × ℝ | ∃ a ∈ K t,
    ¬ ((f none).1 = 1 ∧ q t a < (f none).2 ∧
      (f none).2 ∈ Set.Icc (0 : ℝ) 1)}
  let R := fun t => {f : Option A → ℝ × ℝ | ∃ a ∈ K t,
    ¬ ((f (some a)).1 = 1 ∧ q t a < (f (some a)).2 ∧
      (f (some a)).2 ∈ Set.Icc (0 : ℝ) 1)}
  have hUfiber (t) (c) : D (F t c) ∈ U ↔ d t ∈ U := by
    simp only [U, Set.mem_setOf_eq, hCfiber, d]
  have hpriority (t) (c) (x : {x : V // x ∈ X}) :
      (D (F t c)).1.2 x.1 = (d t).1.2 x.1 ∧
      (D (F t c)).2.2 (φ x.1) = (d t).1.2 x.1 := by
    have hx := surface.sourceCoord_contains_embedded x.1 (Finset.mem_insert_of_mem x.2)
    have htag := (product.overlap x.1 (φ x.1)).mpr ⟨hx, rfl⟩
    change (F t c (product.sourceTag x.1)).2 = _ ∧
      (F t c (product.targetTag (φ x.1))).2 = _
    rw [← htag, hzero t c _ (hcandidate x)]
    exact ⟨rfl, rfl⟩
  have hcurrentValue (t) (c) (a : Option A) : F t c (j a) = P c a := by
    rw [hP]
    have hm : j a ∈ J := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    simp only [F, dif_pos hm]
  obtain ⟨hstageL, hstageR, hdisL, hdisR, hCm, hUm, hLm, hRm⟩ :=
    SamplingSplitOutsideBlockerActualAdjacentSharedContextProducer
      G G' φ r X n zAt B hOutside β cell targetCell w surface k ω
  have hEmL : MeasurableSet ((surface.mixedStage k ω \ U) ∩ surface.pairedCell ω) :=
    ((hstageL ▸ hUm.union hLm).diff hUm).inter hQ
  have hEmR : MeasurableSet ((surface.mixedStage (k.val + 1) ω \ U) ∩
      surface.pairedCell ω) :=
    ((hstageR ▸ hUm.union hRm).diff hUm).inter hQ
  have hLmFiber (t) : MeasurableSet (L t) := by
    have hm : Measurable (fun f : Option A → ℝ × ℝ => f none) := measurable_pi_apply _
    exact (Measurable.exists fun a => measurable_const.and
      ((measurableSet_eq_fun hm.fst measurable_const).mem.and
        ((measurableSet_lt measurable_const hm.snd).mem.and
          (measurableSet_Icc.preimage hm.snd).mem)).not).setOf
  have hRmFiber (t) : MeasurableSet (R t) := by
    have hm (a : A) : Measurable (fun f : Option A → ℝ × ℝ => f (some a)) :=
      measurable_pi_apply _
    exact (Measurable.exists fun a => measurable_const.and
      ((measurableSet_eq_fun (hm a).fst measurable_const).mem.and
        ((measurableSet_lt measurable_const (hm a).snd).mem.and
          (measurableSet_Icc.preimage (hm a).snd).mem)).not).setOf
  have hleft (t) (c) :
      D (F t c) ∈ (surface.mixedStage k ω \ U) ∩ surface.pairedCell ω ↔
        t ∈ gate ∧ P c ∈ L t := by
    rw [hstageL]
    change ((D (F t c) ∈ U ∨ (D (F t c) ∉ U ∧
      ∃ x : {x : V // x ∈ X}, x.1 ∈ B k ∧ D (F t c) ∈ C x ∧
        ¬ (zAt k ∈ (D (F t c)).1.1 ∧
          (D (F t c)).1.2 x.1 < (D (F t c)).1.2 (zAt k) ∧
          (D (F t c)).1.2 (zAt k) ∈ Set.Icc (0 : ℝ) 1))) ∧
      D (F t c) ∉ U) ∧ D (F t c) ∈ surface.pairedCell ω ↔ _
    have htest (x : {x : V // x ∈ X}) :
        (zAt k ∈ (D (F t c)).1.1 ∧
          (D (F t c)).1.2 x.1 < (D (F t c)).1.2 (zAt k) ∧
          (D (F t c)).1.2 (zAt k) ∈ Set.Icc (0 : ℝ) 1) ↔
        ((P c none).1 = 1 ∧ (d t).1.2 x.1 < (P c none).2 ∧
          (P c none).2 ∈ Set.Icc (0 : ℝ) 1) := by
      rw [(hpriority t c x).1]
      have hv := hcurrentValue t c none
      change F t c (product.sourceTag (zAt k)) = P c none at hv
      simp only [D, SamplingSplitOutsideBlockerProductDecode, Finset.mem_filter,
        Finset.mem_univ, true_and, hv]
    simp only [hUfiber, hQfiber, hCfiber, htest]
    change ((_ ∨ (d t ∉ U ∧ ∃ x, x.1 ∈ B k ∧ d t ∈ C x ∧ _)) ∧ _) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨h, hn⟩, hq⟩
      obtain ⟨_, x, hx, hc, ht⟩ := h.resolve_left hn
      exact ⟨⟨hq, hn⟩, ⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, ht⟩
    · rintro ⟨⟨hq, hn⟩, a, ha, ht⟩
      exact ⟨⟨Or.inr ⟨hn, a.1, a.2, (Finset.mem_filter.mp ha).2, ht⟩, hn⟩, hq⟩
  have hright (t) (c) :
      D (F t c) ∈ (surface.mixedStage (k.val + 1) ω \ U) ∩ surface.pairedCell ω ↔
        t ∈ gate ∧ P c ∈ R t := by
    rw [hstageR]
    change ((D (F t c) ∈ U ∨ (D (F t c) ∉ U ∧
      ∃ x : {x : V // x ∈ X}, x.1 ∈ B k ∧ D (F t c) ∈ C x ∧
        ∀ hz : zAt k ∉ insert r X ∧ G.Adj x.1 (zAt k),
          ¬ (β ⟨x, ⟨zAt k, hz⟩⟩ ∈ (D (F t c)).2.1 ∧
            (D (F t c)).2.2 (φ x.1) < (D (F t c)).2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∧
            (D (F t c)).2.2 (β ⟨x, ⟨zAt k, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1))) ∧
      D (F t c) ∉ U) ∧ D (F t c) ∈ surface.pairedCell ω ↔ _
    have htest (a : A) (hz : zAt k ∉ insert r X ∧ G.Adj a.1.1 (zAt k)) :
        (β ⟨a.1, ⟨zAt k, hz⟩⟩ ∈ (D (F t c)).2.1 ∧
          (D (F t c)).2.2 (φ a.1.1) < (D (F t c)).2.2 (β ⟨a.1, ⟨zAt k, hz⟩⟩) ∧
          (D (F t c)).2.2 (β ⟨a.1, ⟨zAt k, hz⟩⟩) ∈ Set.Icc (0 : ℝ) 1) ↔
        ((P c (some a)).1 = 1 ∧ q t a < (P c (some a)).2 ∧
          (P c (some a)).2 ∈ Set.Icc (0 : ℝ) 1) := by
      rw [(hpriority t c a.1).2]
      have hv := hcurrentValue t c (some a)
      change F t c (product.targetTag (β ⟨a.1, ⟨zAt k, hz⟩⟩)) = P c (some a) at hv
      simp only [D, SamplingSplitOutsideBlockerProductDecode, Finset.mem_filter,
        Finset.mem_univ, true_and, hv]
      rfl
    simp only [hUfiber, hQfiber, hCfiber]
    constructor
    · rintro ⟨⟨h, hn⟩, hq⟩
      obtain ⟨_, x, hx, hc, ht⟩ := h.resolve_left hn
      refine ⟨⟨hq, hn⟩, ⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, ?_⟩
      exact fun hf => ht ⟨hOutside k, ((surface.candidate_sets k x.1).mp hx).2⟩
        ((htest ⟨x, hx⟩ _).mpr hf)
    · rintro ⟨⟨hq, hn⟩, a, ha, ht⟩
      refine ⟨⟨Or.inr ⟨hn, a.1, a.2, (Finset.mem_filter.mp ha).2, ?_⟩, hn⟩, hq⟩
      intro hz hf
      exact ht ((htest a hz).mp hf)
  have integrate (E) (hE : MeasurableSet E)
      (H : ({i : product.Tag // i ∉ J} → ℝ × ℝ) → Set (Option A → ℝ × ℝ))
      (hH : ∀ t, MeasurableSet (H t))
      (hf : ∀ t c, D (F t c) ∈ E ↔ t ∈ gate ∧ P c ∈ H t) :
      surface.pairedMeasure E =
        ∫⁻ t, gate.indicator (fun t => (Measure.pi (fun _ : Option A => ρ)) (H t)) t ∂τ := by
    calc
      surface.pairedMeasure E = (Measure.pi (fun _ : product.Tag => ρ)) (D ⁻¹' E) :=
        (congrArg (fun μ => μ E) product.measure_eq).trans
          (Measure.map_apply product.decode_measurable hE)
      _ = _ := ?_
    rw [(hslice (D ⁻¹' E) (hE.preimage product.decode_measurable)).2]
    apply lintegral_congr
    intro t
    change κJ {c | D (F t c) ∈ E} = _
    simp only [hf]
    by_cases ht : t ∈ gate
    · rw [Set.indicator_of_mem ht]
      simp only [ht, true_and]
      exact hreindex.measure_preimage (hH t).nullMeasurableSet
    · rw [Set.indicator_of_notMem ht]
      simp only [ht, false_and, Set.setOf_false, measure_empty]
  refine ⟨hQ, ?_, ?_⟩
  · filter_upwards [hsupp] with t ht
    intro a
    change (F t (fun _ => (0, 0)) (product.sourceTag a.1.1)).2 ∈ _
    simpa only [F, dif_neg (hcandidate a.1)] using
      ht ⟨product.sourceTag a.1.1, hcandidate a.1⟩
  · exact ⟨integrate _ hEmL L hLmFiber hleft, integrate _ hEmR R hRmFiber hright⟩
