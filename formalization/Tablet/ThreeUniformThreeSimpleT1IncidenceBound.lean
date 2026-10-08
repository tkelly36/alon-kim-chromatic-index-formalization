import Tablet.ThreeUniformThreeSimpleLocalSetup
import Tablet.ThreeUniformSaturatedEdgeStructure

open scoped BigOperators

-- [TABLET NODE: ThreeUniformThreeSimpleT1IncidenceBound]
theorem ThreeUniformThreeSimpleT1IncidenceBound
    {D : ℕ} {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (F : MultiHypergraph V E) (f : E)
    (S : ThreeUniformThreeSimpleLocalSetup D F f) :
    S.T1 ≤ (S.V1.card : ℝ) * (D : ℝ) ^ 2 ∧
      (S.V1.card : ℝ) ≤ S.totalXs := by
-- BODY
  classical
  have hu := S.class_mem.1
  have hd := S.class_mem.2.2
  have hfcard : (F.edge f).card = 3 := hu f
  let N := Finset.univ.filter (fun g => g ≠ f ∧ (F.edge g ∩ F.edge f).Nonempty)
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (show 0 < (F.edge f).card by omega)
  let row : E → V := fun g => if h : g ∈ N then
    (Finset.mem_filter.mp h).2.2.choose else v0
  have hrow (g : E) (hg : g ∈ N) : row g ∈ F.edge g ∧ row g ∈ F.edge f := by
    simpa only [row, dif_pos hg] using
      Finset.mem_inter.mp (Classical.choose_spec (Finset.mem_filter.mp hg).2.2)
  let C := Finset.univ.filter (fun t : Finset E =>
    t.card = 3 ∧ t ⊆ N ∧
      (∀ ⦃g⦄, g ∈ t → ∀ ⦃h⦄, h ∈ t → g ≠ h →
        ¬ (g ≠ h ∧ (F.edge g ∩ F.edge h).Nonempty)) ∧
      ∃ g ∈ t, g ∈ S.V1)
  have hC (t : Finset E) (ht : t ∈ C) :
      t.card = 3 ∧ t ⊆ N ∧ Set.InjOn row t := by
    obtain ⟨hc, hn, hi, _⟩ := (Finset.mem_filter.mp ht).2
    refine ⟨hc, hn, ?_⟩
    intro g hg h hh heq
    by_contra hne
    apply hi hg hh hne
    exact ⟨hne, row g, Finset.mem_inter.mpr
      ⟨(hrow g (hn hg)).1, heq ▸ (hrow h (hn hh)).1⟩⟩
  have hcover (t : Finset E) (ht : t ∈ C) : t.image row = F.edge f := by
    obtain ⟨hc, hn, hi⟩ := hC t ht
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
      exact (hrow g (hn hg)).2
    · rw [Finset.card_image_of_injOn hi, hc, hfcard]
  have hfixed (g : E) (hg : g ∈ S.V1) :
      (C.filter (fun t => g ∈ t)).card ≤ D ^ 2 := by
    have hgN : g ∈ N := by
      rw [S.V1_eq] at hg
      exact (Finset.mem_filter.mp hg).1
    have hrg := (hrow g hgN).2
    have htwo : ((F.edge f).erase (row g)).card = 2 := by
      rw [Finset.card_erase_of_mem hrg, hfcard]
    obtain ⟨v, w, hvw, hvwset⟩ := Finset.card_eq_two.mp htwo
    have hvf : v ∈ F.edge f := Finset.mem_of_mem_erase
      (by rw [hvwset]; simp)
    have hwf : w ∈ F.edge f := Finset.mem_of_mem_erase
      (by rw [hvwset]; simp)
    have hvr : v ≠ row g := (Finset.mem_erase.mp (by rw [hvwset]; simp)).1
    have hwr : w ≠ row g := (Finset.mem_erase.mp (by rw [hvwset]; simp)).1
    let A := Finset.univ.filter (fun h : E => v ∈ F.edge h)
    let B := Finset.univ.filter (fun h : E => w ∈ F.edge h)
    let Q := C.filter (fun t => g ∈ t)
    have hex (t : {t // t ∈ Q}) (x : V) (hx : x ∈ F.edge f) :
        ∃ h ∈ t.val, row h = x := by
      have ht := (Finset.mem_filter.mp t.property).1
      exact Finset.mem_image.mp ((hcover t.val ht).symm ▸ hx)
    let a (t : {t // t ∈ Q}) := (hex t v hvf).choose
    let b (t : {t // t ∈ Q}) := (hex t w hwf).choose
    have ha (t : {t // t ∈ Q}) : a t ∈ t.val ∧ row (a t) = v :=
      (hex t v hvf).choose_spec
    have hb (t : {t // t ∈ Q}) : b t ∈ t.val ∧ row (b t) = w :=
      (hex t w hwf).choose_spec
    have hab (t : {t // t ∈ Q}) : t.val = {g, a t, b t} := by
      have ht := hC t.val (Finset.mem_filter.mp t.property).1
      have hga : g ≠ a t := by intro h; exact hvr (by rw [← (ha t).2, ← h])
      have hgb : g ≠ b t := by intro h; exact hwr (by rw [← (hb t).2, ← h])
      have hab : a t ≠ b t := by intro h; exact hvw (by rw [← (ha t).2, h, (hb t).2])
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (Finset.mem_filter.mp t.property).2
        · exact (ha t).1
        · exact (hb t).1
      · simp [ht.1, hga, hgb, hab]
    let enc : {t // t ∈ Q} → {h // h ∈ A} × {h // h ∈ B} := fun t =>
      (⟨a t, by
        have hh := (hrow (a t) ((hC t.val (Finset.mem_filter.mp t.property).1).2.1 (ha t).1)).1
        simpa [A, (ha t).2] using hh⟩,
       ⟨b t, by
        have hh := (hrow (b t) ((hC t.val (Finset.mem_filter.mp t.property).1).2.1 (hb t).1)).1
        simpa [B, (hb t).2] using hh⟩)
    have hinj : Function.Injective enc := by
      intro t u heq
      have heqa : a t = a u := congrArg (fun z => z.1.val) heq
      have heqb : b t = b u := congrArg (fun z => z.2.val) heq
      apply Subtype.ext
      rw [hab t, hab u, heqa, heqb]
    have hcard := Fintype.card_le_of_injective enc hinj
    have hA : A.card ≤ D := hd v
    have hB : B.card ≤ D := hd w
    have hc : Q.card ≤ A.card * B.card := by simpa using hcard
    exact hc.trans (by simpa [pow_two] using Nat.mul_le_mul hA hB)
  have hcount : C.card ≤ ∑ g ∈ S.V1, (C.filter (fun t => g ∈ t)).card := by
    calc
      C.card ≤ (S.V1.biUnion (fun g => C.filter (fun t => g ∈ t))).card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨g, hgt, hg⟩ := (Finset.mem_filter.mp ht).2.2.2.2
        exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨ht, hgt⟩⟩
      _ ≤ _ := Finset.card_biUnion_le
  have hfirst : C.card ≤ S.V1.card * D ^ 2 := by
    calc
      _ ≤ _ := hcount
      _ ≤ ∑ g ∈ S.V1, D ^ 2 := Finset.sum_le_sum hfixed
      _ = _ := by simp
  refine ⟨?_, ?_⟩
  · rw [S.T1_is_triangle_count_meeting_V1]
    exact_mod_cast hfirst
  · let I := fun x v : V => Finset.univ.filter (fun g : E => v ∈ F.edge g ∧ x ∈ F.edge g)
    have hi : S.V1 ⊆ S.Xs.biUnion (fun x => (F.edge f).biUnion (I x)) := by
      intro g hg
      rw [S.V1_eq] at hg
      obtain ⟨hgN, hx⟩ := Finset.mem_filter.mp hg
      obtain ⟨x, hx⟩ := hx
      obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hgN).2.2
      exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_inter.mp hx).2,
        Finset.mem_biUnion.mpr ⟨v, (Finset.mem_inter.mp hv).2,
          by simp [I, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hx).1]⟩⟩
    have hic : S.V1.card ≤ ∑ x ∈ S.Xs, ∑ v ∈ F.edge f, (I x v).card := by
      calc
        _ ≤ _ := Finset.card_le_card hi
        _ ≤ _ := Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum (fun x _ => Finset.card_biUnion_le)
    rw [S.totalXs_eq_sum]
    simp_rw [S.vertexDegreeIntoF_eq]
    exact_mod_cast hic
