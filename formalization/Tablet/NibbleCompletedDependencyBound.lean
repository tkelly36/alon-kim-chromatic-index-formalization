import Tablet.NibbleBadEvent
import Tablet.NibbleProductSamplingLaw
import Tablet.UniformHypergraph
import Tablet.MaxDegreeAtMost
import Tablet.FiniteRegularGraphRadiusTwo

-- [TABLET NODE: NibbleCompletedDependencyBound]
theorem NibbleCompletedDependencyBound {V E : Type*} [Fintype E]
    [DecidableEq V] [DecidableEq E] (A k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (H : MultiHypergraph V E) (hu : UniformHypergraph H k) (hd : MaxDegreeAtMost H D)
    (M : E → Finset (Fin (A * D))) (Q : NibbleCompletionData H M (k * D))
    (d z : ℝ) :
    let J := {x : V // x ∈ (Finset.univ : Finset E).biUnion H.edge} ⊕ E
    (∀ j : J, MeasurableSet (NibbleBadEvent Q d z j)) ∧
    ∃ S : J → Finset (Sigma fun a => Fin (Q.size a)),
      (∀ j ω ω', (∀ t ∈ S j, ω t = ω' t) →
        (ω ∈ NibbleBadEvent Q d z j ↔ ω' ∈ NibbleBadEvent Q d z j)) ∧
      (∀ j, (S j).card ≤ 2 * A * D^2 * (k * D)^2) ∧
      (∀ t, ((Finset.univ : Finset J).filter (fun j => t ∈ S j)).card ≤
        2 * (k + 1) * (k * D)^2) ∧
      (∀ j, ((Finset.univ : Finset J).filter
        (fun i => i ≠ j ∧ (S i ∩ S j).Nonempty)).card ≤
          4 * A * (k + 1) * k^4 * D^6) := by
-- BODY
  classical
  let K := Fin (A * D)
  let T := Sigma fun a => Fin (Q.size a)
  let W := {x : V // x ∈ (Finset.univ : Finset E).biUnion H.edge}
  let J := W ⊕ E
  have hDelta : 1 ≤ k * D := by nlinarith
  let R (a : K) (v : Fin (Q.size a)) := Finset.univ.filter fun w =>
    w = v ∨ (Q.graph a).Adj v w ∨
      ∃ u, (Q.graph a).Adj v u ∧ (Q.graph a).Adj u w
  have hR (a : K) := FiniteRegularGraphRadiusTwo (Q.graph a) (k * D)
    (Q.regular a) hDelta
  have hRcard (a : K) (v : Fin (Q.size a)) : (R a v).card ≤ 2 * (k * D)^2 := by
    convert (hR a).2.1 v using 1
    congr 1
    ext w
    simp [R]
  let B (e : E) : Finset T := (M e).attach.biUnion fun a =>
    (R a.val (Q.embed a.val ⟨e, a.property⟩)).image (Sigma.mk a.val)
  let S : J → Finset T := fun j => match j with
    | Sum.inl x => (Finset.univ.filter fun e => x.val ∈ H.edge e).biUnion B
    | Sum.inr e => B e
  have hB (e : E) (a : K) (ha : a ∈ M e) (v : Fin (Q.size a))
      (hv : v ∈ R a (Q.embed a ⟨e, ha⟩)) : Sigma.mk a v ∈ B e := by
    exact Finset.mem_biUnion.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have hBcard (e : E) : (B e).card ≤ A * D * (2 * (k * D)^2) := by
    calc
      _ ≤ ∑ a ∈ (M e).attach,
          ((R a.val (Q.embed a.val ⟨e, a.property⟩)).image
            (fun v => (⟨a.val, v⟩ : T))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ a ∈ (M e).attach, 2 * (k * D)^2 :=
        Finset.sum_le_sum fun a _ => (Finset.card_image_le).trans
          (hRcard a.val (Q.embed a.val ⟨e, a.property⟩))
      _ = (M e).card * (2 * (k * D)^2) := by simp
      _ ≤ A * D * (2 * (k * D)^2) := by
        apply Nat.mul_le_mul_right
        exact (Finset.card_le_univ (M e)).trans_eq (Fintype.card_fin _)
  have hScard (j : J) : (S j).card ≤ 2 * A * D^2 * (k * D)^2 := by
    cases j with
    | inl x =>
      calc
        _ ≤ ∑ e ∈ Finset.univ.filter (fun e => x.val ∈ H.edge e), (B e).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ e ∈ Finset.univ.filter (fun e => x.val ∈ H.edge e),
            A * D * (2 * (k * D)^2) := Finset.sum_le_sum fun e _ => hBcard e
        _ = HypergraphDegree H x.val * (A * D * (2 * (k * D)^2)) := by
          simp [HypergraphDegree]
        _ ≤ D * (A * D * (2 * (k * D)^2)) := Nat.mul_le_mul_right _ (hd x.val)
        _ = _ := by ring
    | inr e =>
      calc
        _ ≤ A * D * (2 * (k * D)^2) := hBcard e
        _ ≤ D * (A * D * (2 * (k * D)^2)) := Nat.le_mul_of_pos_left _ hD
        _ = _ := by ring
  have hlocal (a : K) (v : Fin (Q.size a)) (ω ω' : T → ℝ × ℝ)
      (heq : ∀ u, u = v ∨ (Q.graph a).Adj v u → ω ⟨a, u⟩ = ω' ⟨a, u⟩) :
      v ∈ NibbleCompletedSelection Q ω a ↔ v ∈ NibbleCompletedSelection Q ω' a := by
    simp only [NibbleCompletedSelection, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq v (Or.inl rfl)]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro u
    by_cases hu : (Q.graph a).Adj v u
    · rw [heq u (Or.inr hu)]
    · simp [hu]
  have hselected (e : E) (ω ω' : T → ℝ × ℝ)
      (heq : ∀ t ∈ B e, ω t = ω' t) (a : K) :
      e ∈ NibbleSelectedEdges Q ω a ↔ e ∈ NibbleSelectedEdges Q ω' a := by
    simp only [NibbleSelectedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    apply exists_congr
    intro ha
    apply hlocal
    intro u hu
    apply heq
    apply hB e a ha
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hu.imp_right Or.inl
  have hdet (j : J) (ω ω' : T → ℝ × ℝ)
      (heq : ∀ t ∈ S j, ω t = ω' t) :
      ω ∈ NibbleBadEvent Q d z j ↔ ω' ∈ NibbleBadEvent Q d z j := by
    cases j with
    | inl x =>
      have hdeg : NibbleResidualDegree H (NibbleSelectedEdges Q ω) x.val =
          NibbleResidualDegree H (NibbleSelectedEdges Q ω') x.val := by
        unfold NibbleResidualDegree
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hx : x.val ∈ H.edge e
        · simp only [hx, true_and]
          apply forall_congr'
          intro a
          exact not_congr (hselected e ω ω' (fun t ht => heq t
            (Finset.mem_biUnion.mpr ⟨e, by simp [hx], ht⟩)) a)
        · simp [hx]
      change d < (_ : ℝ) ↔ d < (_ : ℝ)
      rw [hdeg]
    | inr e =>
      have hdel : NibbleDeletedColors H M (NibbleSelectedEdges Q ω) e =
          NibbleDeletedColors H M (NibbleSelectedEdges Q ω') e := by
        unfold NibbleDeletedColors
        apply Finset.filter_congr
        intro a ha
        apply exists_congr
        intro f
        by_cases hef : (LineGraphOfHypergraph H).Adj e f
        · simp only [hef, and_true]
          simp only [NibbleSelectedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          apply exists_congr
          intro hf
          apply hlocal
          intro u hu
          apply heq
          apply hB e a ha
          have hef' := (Q.induced a ⟨e, ha⟩ ⟨f, hf⟩).mpr hef
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hu with rfl | hu
          · exact Or.inr (Or.inl hef')
          · exact Or.inr (Or.inr ⟨_, hef', hu⟩)
        · simp [hef]
      change z ≤ (_ : ℝ) ↔ z ≤ (_ : ℝ)
      rw [hdel]
  have hmeas : ∀ j : J, MeasurableSet (NibbleBadEvent Q d z j) := by
    have hDeltaReal : (1 : ℝ) ≤ k * D := by exact_mod_cast hDelta
    have hm := (NibbleProductSamplingLaw Q 1 (by norm_num) (by
      simpa only [Nat.cast_mul] using hDeltaReal)).2.2.2.1
    have hfiber (I : K → Finset E) : MeasurableSet
        {ω : T → ℝ × ℝ | NibbleSelectedEdges Q ω = I} := by
      have he : {ω : T → ℝ × ℝ | NibbleSelectedEdges Q ω = I} =
          ⋂ a, ⋂ e, {ω | e ∈ NibbleSelectedEdges Q ω a ↔ e ∈ I a} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, funext_iff, Finset.ext_iff]
        rfl
      rw [he]
      exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun e =>
        (hm a e).iff (MeasurableSet.const _)
    have hpred (P : (K → Finset E) → Prop) : MeasurableSet
        {ω : T → ℝ × ℝ | P (NibbleSelectedEdges Q ω)} := by
      have he : {ω : T → ℝ × ℝ | P (NibbleSelectedEdges Q ω)} =
          ⋃ I, ⋃ (_ : P I), {ω | NibbleSelectedEdges Q ω = I} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨I, h, he⟩
          rwa [he]
      rw [he]
      exact MeasurableSet.iUnion fun I => MeasurableSet.iUnion fun _ => hfiber I
    intro j
    cases j with
    | inl x => exact hpred (fun I => d < (NibbleResidualDegree H I x.val : ℝ))
    | inr e => exact hpred (fun I => z ≤ ((NibbleDeletedColors H M I e).card : ℝ))
  have hroot (t : T) (e : E) (ht : t ∈ B e) :
      ∃ ha : t.1 ∈ M e, Q.embed t.1 ⟨e, ha⟩ ∈ R t.1 t.2 := by
    obtain ⟨⟨a, ha⟩, _, hvImage⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨v, hvRadius, he⟩ := Finset.mem_image.mp hvImage
    cases he
    refine ⟨ha, ?_⟩
    have hs := (hR a).2.2 (Q.embed a ⟨e, ha⟩) v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using
      hs.mp (by simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using hvRadius)
  let F (t : T) := Finset.univ.filter fun e => t ∈ B e
  have hFcard (t : T) : (F t).card ≤ 2 * (k * D)^2 := by
    let f : {e // e ∈ F t} → {v // v ∈ R t.1 t.2} := fun e =>
      ⟨Q.embed t.1 ⟨e.val, (hroot t e.val (Finset.mem_filter.mp e.property).2).choose⟩,
        (hroot t e.val (Finset.mem_filter.mp e.property).2).choose_spec⟩
    have hf : Function.Injective f := by
      intro e g h
      apply Subtype.ext
      exact congrArg (fun x : {e // t.1 ∈ M e} => x.val)
        (Q.injective t.1 (congrArg Subtype.val h))
    exact (Finset.card_le_card_of_injective hf).trans (hRcard t.1 t.2)
  let C (e : E) : Finset J := insert (Sum.inr e)
    ((H.edge e).attach.image fun x => Sum.inl
      ⟨x.val, Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, x.property⟩⟩)
  have hCcard (e : E) : (C e).card ≤ k + 1 := by
    calc
      _ ≤ ((H.edge e).attach.image (fun x => (Sum.inl
          ⟨x.val, Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, x.property⟩⟩ : J))).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (H.edge e).attach.card + 1 := Nat.add_le_add_right Finset.card_image_le _
      _ = k + 1 := by rw [Finset.card_attach, hu e]
  have hocc (t : T) : (Finset.univ.filter (fun j => t ∈ S j)).card ≤
      2 * (k + 1) * (k * D)^2 := by
    have hsub : Finset.univ.filter (fun j => t ∈ S j) ⊆ (F t).biUnion C := by
      intro j hj
      have ht := (Finset.mem_filter.mp hj).2
      cases j with
      | inl x =>
        obtain ⟨e, he, hb⟩ := Finset.mem_biUnion.mp ht
        refine Finset.mem_biUnion.mpr ⟨e, by simp [F, hb], ?_⟩
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨⟨x.val, (Finset.mem_filter.mp he).2⟩, Finset.mem_attach _ _, rfl⟩
      | inr e =>
        exact Finset.mem_biUnion.mpr ⟨e, by simpa [F] using ht,
          Finset.mem_insert_self _ _⟩
    calc
      _ ≤ ((F t).biUnion C).card := Finset.card_le_card hsub
      _ ≤ ∑ e ∈ F t, (C e).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ F t, (k + 1) := Finset.sum_le_sum fun e _ => hCcard e
      _ = (F t).card * (k + 1) := by simp
      _ ≤ (2 * (k * D)^2) * (k + 1) := Nat.mul_le_mul_right _ (hFcard t)
      _ = _ := by ring
  refine ⟨hmeas, S, hdet, hScard, hocc, ?_⟩
  intro j
  have hsub : Finset.univ.filter (fun i => i ≠ j ∧ (S i ∩ S j).Nonempty) ⊆
      (S j).biUnion (fun t => Finset.univ.filter fun i => t ∈ S i) := by
    intro i hi
    obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hi).2.2
    exact Finset.mem_biUnion.mpr ⟨t, (Finset.mem_inter.mp ht).2,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp ht).1⟩⟩
  calc
    _ ≤ ((S j).biUnion (fun t => Finset.univ.filter fun i => t ∈ S i)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ t ∈ S j, (Finset.univ.filter (fun i => t ∈ S i)).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ S j, 2 * (k + 1) * (k * D)^2 := Finset.sum_le_sum fun t _ => hocc t
    _ = (S j).card * (2 * (k + 1) * (k * D)^2) := by simp
    _ ≤ (2 * A * D^2 * (k * D)^2) * (2 * (k + 1) * (k * D)^2) :=
      Nat.mul_le_mul_right _ (hScard j)
    _ = _ := by ring
