import Tablet.Preamble
import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentTripleCount
import Tablet.LineGraphOfHypergraph
import Tablet.ThreeUniformTwoSimpleNeighborPartition
import Tablet.ThreeUniformIndependentTriplesThroughEdgeBound
import Tablet.ThreeUniformSelectedTriplePermutationBound
import Mathlib.Data.Finset.Option

open scoped BigOperators

-- [TABLET NODE: ThreeUniformTwoSimpleTripleBound]
theorem ThreeUniformTwoSimpleTripleBound :
    ∀ D : ℕ,
      ∀ {V E : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V],
        ∀ H : MultiHypergraph V E,
          H ∈ HypergraphClass (V := V) (E := E) 3 2 D →
          ∀ f : E, ∀ v : Fin 3 → V,
            (∀ i : Fin 3, v i ∈ H.edge f) →
            (∀ y : V, y ∈ H.edge f → ∃ i : Fin 3, v i = y) →
            (∀ i : Fin 3, HypergraphDegree H (v i) = D) →
            (((Finset.univ : Finset E).filter
                (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)).card =
              3 * (D - 1)) →
            ∀ X Xs Xb : Finset V, ∀ x : Fin 3 → Option V,
            ∀ a : Fin 3 → V → ℝ,
              let b : Fin 3 → Fin 3 → ℝ := fun i j => (x j).elim 0 (a i)
              (∀ y : V, y ∈ X ↔
                y ∉ H.edge f ∧ ∃ e : E, e ≠ f ∧ y ∈ H.edge e ∧
                  (H.edge e ∩ H.edge f).Nonempty) →
              (∀ e : E, e ≠ f → (H.edge e ∩ H.edge f).Nonempty →
                (H.edge e ∩ H.edge f).card = 1) →
              (∀ y ∈ X, (∑ i : Fin 3, a i y) ≤ (D : ℝ)) →
              (∀ i : Fin 3, (∑ y ∈ X, a i y) = 2 * ((D : ℝ) - 1)) →
              (∀ i y, a i y =
                (((Finset.univ : Finset E).filter
                  (fun e => v i ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ)) →
              Xs = X.filter (fun y =>
                (∑ i : Fin 3, a i y) < (D : ℝ) ^ ((2 : ℝ) / 3)) →
              Xb = X \ Xs →
              Xb ⊆ X →
              (∀ j y, x j = some y → y ∈ Xb) →
              (∀ j k y, x j = some y → x k = some y → j = k) →
              (∀ j, x j = none → ∀ y ∈ Xb, ∃ k, x k = some y) →
              (∑ i : Fin 3, b i 1) ≤ (∑ i : Fin 3, b i 0) →
              (∑ i : Fin 3, b i 2) ≤ (∑ i : Fin 3, b i 1) →
              (∀ y ∈ Xb, (∀ j, x j ≠ some y) →
                (∑ i : Fin 3, a i y) ≤ (∑ i : Fin 3, b i 2)) →
              (@IndependentTripleCount E _ _ (LineGraphOfHypergraph H)
                (Classical.decRel (LineGraphOfHypergraph H).Adj) f : ℝ) ≤
                (∑ p : Equiv.Perm (Fin 3),
                  b 0 (p 0) * b 1 (p 1) * b 2 (p 2)) +
                (3 * (D : ℝ) ^ (3 : ℕ) + 6 * (D : ℝ) ^ (2 : ℕ)) -
                (D : ℝ) ^ (2 : ℕ) *
                  (∑ i : Fin 3, ∑ j : Fin 3, b i j) := by
-- BODY
  classical
  intro D V E _ _ _ _ H hH f v hv hcover hdegree hneighbors
    X Xs Xb x a b hX hroot hcolumn hrow hcodegree hXs hXb hXbX
    hslot hslotinj hdummy horder1 horder2 htop
  have hu : UniformHypergraph H 3 := hH.1
  have hs : TSimpleHypergraph H 2 := hH.2.1
  have hvimage : Finset.univ.image v = H.edge f := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hv i, hcover y⟩
  have hvinj : Function.Injective v := by
    have hi : Set.InjOn v ↑(Finset.univ : Finset (Fin 3)) :=
      Finset.card_image_iff.mp (by rw [hvimage, hu f]; simp)
    exact fun i j hij => hi (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hD : 1 ≤ D := by
    rw [← hdegree 0]
    exact Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv 0⟩⟩
  let A : Finset V := Finset.univ.biUnion (fun j => (x j).toFinset)
  let N : Finset E := Finset.univ.filter
    (fun e => e ≠ f ∧ (H.edge e ∩ H.edge f).Nonempty)
  have hAmem (y : V) : y ∈ A ↔ ∃ j, x j = some y := by
    simp [A, Option.mem_def]
  have hAX : A ⊆ X := by
    intro y hy
    obtain ⟨j, hj⟩ := (hAmem y).mp hy
    exact hXbX (hslot j y hj)
  have hAdis : Disjoint A (H.edge f) := by
    apply Finset.disjoint_left.mpr
    intro y hy hyf
    exact ((hX y).mp (hAX hy)).1 hyf
  have hAc : A.card ≤ 3 := by
    calc
      A.card ≤ ∑ j : Fin 3, (x j).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin 3, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        cases x j <;> simp
      _ = 3 := by simp
  have hslotdis : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).Pairwise
      (fun j k => Disjoint (x j).toFinset (x k).toFinset) := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro y hyj hyk
    have hj' : x j = some y := by simpa [Option.mem_def] using hyj
    have hk' : x k = some y := by simpa [Option.mem_def] using hyk
    exact hjk (hslotinj j k y hj' hk')
  have hslotsum (i : Fin 3) : (∑ j : Fin 3, b i j) = ∑ y ∈ A, a i y := by
    rw [Finset.sum_biUnion hslotdis]
    apply Finset.sum_congr rfl
    intro j hj
    cases hx : x j <;> simp [b, hx]
  obtain ⟨hpartition, hincidence, hnine, hbound, hdouble⟩ :=
    ThreeUniformTwoSimpleNeighborPartition H f N A hu hs hAdis hAc
      (fun e he => hroot e (Finset.mem_filter.mp he).2.1
        (Finset.mem_filter.mp he).2.2)
      (fun e => by simp [N]) D hD hneighbors
  have hS : (∑ i : Fin 3, ∑ j : Fin 3, b i j) =
      ((∑ e ∈ N, (H.edge e ∩ A).card : ℕ) : ℝ) := by
    simp_rw [hslotsum, hcodegree]
    rw [← Finset.sum_image (f := fun u => ∑ y ∈ A,
      (((Finset.univ : Finset E).filter
        (fun e => u ∈ H.edge e ∧ y ∈ H.edge e)).card : ℝ))
      (fun i _ j _ hij => hvinj hij), hvimage]
    exact_mod_cast hdouble
  rw [← hS] at hbound
  let T : Finset (Finset E) := Finset.univ.filter (fun S =>
    S.card = 3 ∧ S ⊆ (LineGraphOfHypergraph H).neighborFinset f ∧
      ∀ ⦃e⦄, e ∈ S → ∀ ⦃g⦄, g ∈ S → e ≠ g →
        ¬ (LineGraphOfHypergraph H).Adj e g)
  let V1 := N.filter (fun e => (H.edge e ∩ A).card = 0)
  have hT (S : Finset E) (hS : S ∈ T) : S.card = 3 ∧
      (∀ e ∈ S, (H.edge e ∩ H.edge f).Nonempty) ∧
      (∀ e ∈ S, ∀ g ∈ S, e ≠ g → ¬ (LineGraphOfHypergraph H).Adj e g) := by
    obtain ⟨_, hc, hn, hi⟩ := Finset.mem_filter.mp hS
    refine ⟨hc, ?_, fun e he g hg hne => hi he hg hne⟩
    intro e he
    have ha := (SimpleGraph.mem_neighborFinset _ _ _).mp (hn he)
    exact (LineGraphOfHypergraph H).symm ha |>.2
  have hmeet : (T.filter (fun S => ∃ g ∈ V1, g ∈ S)).card ≤ D ^ 2 * V1.card := by
    have heq : T.filter (fun S => ∃ g ∈ V1, g ∈ S) =
        V1.biUnion (fun g => T.filter (fun S => g ∈ S)) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hS, g, hg, hgS⟩
        exact ⟨g, hg, hS, hgS⟩
      · rintro ⟨g, hg, hS, hgS⟩
        exact ⟨hS, g, hg, hgS⟩
    rw [heq]
    calc
      _ ≤ ∑ g ∈ V1, (T.filter (fun S => g ∈ S)).card := Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ V1, D ^ 2 := by
        apply Finset.sum_le_sum
        intro g hg
        have hgN := (Finset.mem_filter.mp hg).1
        obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hgN).2.2
        obtain ⟨i, hi⟩ := hcover y (Finset.mem_inter.mp hy).2
        exact ThreeUniformIndependentTriplesThroughEdgeBound H f v hcover D hdegree
          T hT g i (hi ▸ (Finset.mem_inter.mp hy).1)
      _ = _ := by simp [Nat.mul_comm]
  have havoid : ((T.filter (fun S => ¬ ∃ g ∈ V1, g ∈ S)).card : ℝ) ≤
      ∑ p : Equiv.Perm (Fin 3), b 0 (p 0) * b 1 (p 1) * b 2 (p 2) := by
    apply ThreeUniformSelectedTriplePermutationBound H f v hcover x b
    · intro i j
      cases hx : x j with
      | none => simp [b, hx]
      | some y => simpa [b, hx] using hcodegree i y
    · intro S hS
      exact hT S (Finset.mem_filter.mp hS).1
    · intro S hS e he
      obtain ⟨hST, havoid⟩ := Finset.mem_filter.mp hS
      have heN : e ∈ N := by
        have hn := (Finset.mem_filter.mp hST).2.2.1 he
        have ha := (SimpleGraph.mem_neighborFinset _ _ _).mp hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (LineGraphOfHypergraph H).symm ha⟩
      have hpos : 0 < (H.edge e ∩ A).card := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact havoid ⟨e, Finset.mem_filter.mpr ⟨heN, hz⟩, he⟩
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      obtain ⟨j, hj⟩ := (hAmem y).mp (Finset.mem_inter.mp hy).2
      exact ⟨j, y, hj, (Finset.mem_inter.mp hy).1⟩
  have hcount :
      (@IndependentTripleCount E _ _ (LineGraphOfHypergraph H)
        (Classical.decRel (LineGraphOfHypergraph H).Adj) f : ℝ) ≤
      (∑ p : Equiv.Perm (Fin 3), b 0 (p 0) * b 1 (p 1) * b 2 (p 2)) +
        (D : ℝ) ^ 2 * (N.filter (fun e => (H.edge e ∩ A).card = 0)).card := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := T) (p := fun S => ∃ g ∈ V1, g ∈ S)
    have hsplitR : (T.card : ℝ) =
        ((T.filter (fun S => ∃ g ∈ V1, g ∈ S)).card : ℝ) +
        ((T.filter (fun S => ¬ ∃ g ∈ V1, g ∈ S)).card : ℝ) := by
      exact_mod_cast hsplit.symm
    have hmeetR : ((T.filter (fun S => ∃ g ∈ V1, g ∈ S)).card : ℝ) ≤
        (D : ℝ) ^ 2 * V1.card := by exact_mod_cast hmeet
    change (T.card : ℝ) ≤ _
    linarith
  have hweighted := mul_le_mul_of_nonneg_left hbound (sq_nonneg (D : ℝ))
  nlinarith only [hcount, hweighted]
