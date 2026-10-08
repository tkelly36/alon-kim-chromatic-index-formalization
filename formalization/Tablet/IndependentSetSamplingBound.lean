import Tablet.LocalBParameter
import Tablet.RandomIndependentSetSampling
import Tablet.SamplingOneVertexEstimate
import Tablet.SamplingRegularEnlargementReduction
import Tablet.SamplingTripleBonferroniEstimate

open BigOperators

-- [TABLET NODE: IndependentSetSamplingBound]
theorem IndependentSetSamplingBound (iota : ℝ) (hiota : 0 < iota) :
    ∃ Delta0 gamma0 : ℕ, ∀ Delta : ℕ, ∀ gamma : ℝ,
      Delta0 ≤ Delta → (gamma0 : ℝ) ≤ gamma →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
          (∀ v : V, G.degree v = Delta) →
          ∀ μ : Finset V → ℝ,
            RandomIndependentSetSampling G Delta gamma μ →
            (∀ r : V,
              abs ((∑ S : Finset V, if r ∈ S then μ S else 0) -
                  (1 - Real.exp (-gamma)) / (Delta : ℝ)) ≤
                2 / (Delta : ℝ)^2) ∧
            (∀ r : V, ∀ X : Finset V,
              (∀ x : V, x ∈ X → G.Adj r x) →
              let s : Set V := {v | v ∈ X ∨ v = r}
              letI : Fintype s := Fintype.ofFinite s
              letI : DecidableEq s := Classical.decEq s
              letI : DecidableRel (G.induce s).Adj := Classical.decRel (G.induce s).Adj
              (∑ S : Finset V, if (S ∩ X).Nonempty then μ S else 0) ≤
                LocalBParameter (G.induce s) Delta (⟨r, by simp [s]⟩ : s) + iota) := by
-- BODY
  classical
  obtain ⟨D1, hD1⟩ := Filter.eventually_atTop.mp SamplingOneVertexEstimate
  obtain ⟨D2, g0, hB⟩ := SamplingTripleBonferroniEstimate iota hiota
  refine ⟨max D1 D2, g0, ?_⟩
  intro D g hD hg V _ _ G _ hreg μ hsam
  refine ⟨fun r => (hD1 D ((le_max_left _ _).trans hD) g G hreg μ hsam r).2, ?_⟩
  intro r X hX
  obtain ⟨W, instF, instD, H, instA, hex⟩ :=
    SamplingRegularEnlargementReduction G D g hreg μ hsam r X hX
  letI := instF
  letI := instD
  letI := instA
  obtain ⟨φ, t, Y, ν, hinj, rfl, rfl, hreg', hadj, hclean, hsam', hmono⟩ := hex
  have hY : ∀ y ∈ X.image φ, H.Adj (φ r) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (hadj r x (Or.inr rfl) (Or.inl hx)).mp (hX x hx)
  have hclean' : ∀ u ∈ X.image φ, ∀ v ∈ X.image φ, u ≠ v →
      ¬ ∃ w, H.Adj u w ∧ H.Adj v w ∧ w ≠ φ r ∧ ¬ H.Adj (φ r) w := by
    intro u hu v hv hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact hclean a ha b hb (fun h => hne (congrArg φ h))
  have hb := hB D g ((le_max_right _ _).trans hD) hg H hreg' ν hsam'
    (φ r) (X.image φ) hY hclean'
  let s : Set V := {v | v ∈ X ∨ v = r}
  letI : Fintype s := Fintype.ofFinite s
  letI : DecidableEq s := Classical.decEq s
  let R : SimpleGraph s := G.induce s
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  let root : s := ⟨r, Or.inr rfl⟩
  let ψ : s → W := fun x => φ x.val
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinj h)
  have hn (x : s) : x ∈ R.neighborFinset root ↔ x.val ∈ X := by
    rw [SimpleGraph.mem_neighborFinset]
    change G.Adj r x.val ↔ x.val ∈ X
    constructor
    · intro h
      rcases x.property with hx | hx
      · exact hx
      · exact (G.loopless.irrefl r (hx ▸ h)).elim
    · exact hX x.val
  have hψadj (x y : s) : R.Adj x y ↔ H.Adj (ψ x) (ψ y) :=
    hadj x.val y.val x.property y.property
  have himage : (R.neighborFinset root).image ψ = X.image φ := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.val, (hn x).mp hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, Or.inl hx⟩, (hn _).mpr hx, hxy⟩
  have hdegree : R.degree root = (X.image φ).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← himage,
      Finset.card_image_of_injective _ hψ]
  have hcount (n : ℕ) :
      (Finset.univ.filter fun P : Finset s => P.card = n ∧
        P ⊆ R.neighborFinset root ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ R.Adj a b).card =
      (Finset.univ.filter fun P : Finset W => P.card = n ∧
        P ⊆ X.image φ ∧
        ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → ¬ H.Adj a b).card := by
    apply Finset.card_bij (fun P _ => P.image ψ)
    · intro P hP
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      refine ⟨by simpa [Finset.card_image_of_injective _ hψ] using hP.1,
        ?_, ?_⟩
      · rw [← himage]
        exact Finset.image_mono ψ hP.2.1
      · rintro a ha b hb hab h
        obtain ⟨a0, ha0, ea⟩ := Finset.mem_image.mp ha
        obtain ⟨b0, hb0, eb⟩ := Finset.mem_image.mp hb
        subst a
        subst b
        exact hP.2.2 ha0 hb0 (fun he => hab (congrArg ψ he)) ((hψadj a0 b0).mpr h)
    · intro P _ Q _ he
      exact (Finset.image_injective hψ) he
    · intro Q hQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
      let P := Finset.univ.filter fun x : s => ψ x ∈ Q
      have he : P.image ψ = Q := by
        ext y
        constructor
        · rintro hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hx).2
        · intro hy
          have hy' := hQ.2.1 hy
          rw [← himage] at hy'
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy'
          exact Finset.mem_image.mpr ⟨x, by simp [P, hy], rfl⟩
      refine ⟨P, ?_, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← Finset.card_image_of_injective P hψ, he]
        exact hQ.1
      · intro x hx
        have hh := hQ.2.1 (Finset.mem_filter.mp hx).2
        rw [← himage] at hh
        obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hh
        simpa [hψ heq] using hy
      · intro a ha b hb hab h
        exact hQ.2.2 (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
          (fun he => hab (hψ he)) ((hψadj a b).mp h)
  have hparam : SamplingInducedNeighborhoodLocalBParameter H D (φ r) (X.image φ) =
      LocalBParameter R D root := by
    unfold SamplingInducedNeighborhoodLocalBParameter LocalBParameter
      IndependentPairCount IndependentTripleCount
    rw [hdegree, hcount 2, hcount 3]
  change _ ≤ LocalBParameter R D root + iota
  rw [hparam] at hb
  exact hmono.trans hb
