import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairComplementLowerBound
import Tablet.IndependentPairCount
import Tablet.FiniteBipartiteIncidenceTableRowBound
import Tablet.KUniformKSimpleExtremalSaturation
import Tablet.KUniformNeighborClassWithinPairs
import Tablet.KUniformNeighborOneIntersectionFromSaturation
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.MaxDegreeAtMost
import Tablet.TablePairFillingBound
import Tablet.UniformHypergraph
import Mathlib.Data.Nat.Choose.Cast

set_option maxHeartbeats 800000

universe u v

-- [TABLET NODE: KUniformKSimplePairLowerBound]
theorem KUniformKSimplePairLowerBound :
    ∀ k : ℕ, 0 < k →
      ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
        ∀ {V : Type u} {E : Type v} [Fintype E] [DecidableEq E] [DecidableEq V],
          ∀ H : MultiHypergraph V E,
            H ∈ HypergraphClass (V := V) (E := E) k k D →
            ∀ f : E,
              (∀ {V' : Type u} {E' : Type v}
                [Fintype E'] [DecidableEq E'] [DecidableEq V'],
                ∀ H' : MultiHypergraph V' E',
                  H' ∈ HypergraphClass (V := V') (E := E') k k D →
                  ∀ e' : E',
                    @LocalBParameter E' _ _ (LineGraphOfHypergraph H')
                        (Classical.decRel (LineGraphOfHypergraph H').Adj) (k * D) e'
                      ≤ @LocalBParameter E _ _ (LineGraphOfHypergraph H)
                        (Classical.decRel (LineGraphOfHypergraph H).Adj) (k * D) f) →
              (((k : ℝ) - 1) / 2) * (D : ℝ) ^ 2 - (k : ℝ) ^ 2 * (D : ℝ)
                ≤ (@IndependentPairCount E _ _ (LineGraphOfHypergraph H)
                    (Classical.decRel (LineGraphOfHypergraph H).Adj) f : ℝ) := by
-- BODY
  classical
  intro k hk
  by_cases hk_one : k = 1
  · subst k
    refine ⟨1, ?_⟩
    intro D hD V E _ _ _ H hH f hmax
    have hP_nonneg :
        (0 : ℝ) ≤
          (@IndependentPairCount E _ _ (LineGraphOfHypergraph H)
            (Classical.decRel (LineGraphOfHypergraph H).Adj) f : ℝ) := by
      exact_mod_cast
        (Nat.zero_le
          (@IndependentPairCount E _ _ (LineGraphOfHypergraph H)
            (Classical.decRel (LineGraphOfHypergraph H).Adj) f))
    have hD_nonneg : (0 : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast Nat.zero_le D
    nlinarith
  · obtain ⟨Dsat0, hsat_thm⟩ := KUniformKSimpleExtremalSaturation k hk
    refine ⟨max 2 Dsat0, ?_⟩
    intro D hD V E _ _ _ H hH f hmax
    have hk_ge_two : 2 ≤ k := by
      omega
    have hD_ge_one : 1 ≤ D := by
      exact le_trans (by omega : 1 ≤ max 2 Dsat0) hD
    have hDsat_two : 2 ≤ D := by
      exact le_trans (Nat.le_max_left 2 Dsat0) hD
    have hsat :
        (∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D) ∧
          ((Finset.univ : Finset E).filter
            (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := by
      have hDsat0 : Dsat0 ≤ D := by
        exact le_trans (Nat.le_max_right 2 Dsat0) hD
      exact hsat_thm D hDsat0 H hH f (by
        intro V' E' _ _ _ H' hH' e'
        exact hmax H' hH' e')
    have hvertex_saturated : ∀ v : V, v ∈ H.edge f → HypergraphDegree H v = D := hsat.1
    have hneighbor_card :
        ((Finset.univ : Finset E).filter
          (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)).card = k * D - k := hsat.2
    have hneighbor_one :
        ∀ g : E, g ≠ f → (H.edge g ∩ H.edge f).Nonempty →
          (H.edge g ∩ H.edge f).card = 1 :=
      KUniformNeighborOneIntersectionFromSaturation k D H f hH.1 hvertex_saturated hneighbor_card
    have hneighbor_classes :=
      KUniformNeighborClassWithinPairs k D H f hH.1 hvertex_saturated hneighbor_one
    let fVerts : Finset V := H.edge f
    let X : Finset V :=
      (Finset.univ : Finset E).biUnion (fun g =>
        if g = f then ∅
        else (H.edge g).filter (fun x => x ∉ H.edge f))
    let row : Fin k → V :=
      fun i => ((Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm i).1
    let A : Fin k → Fin X.card → ℝ :=
      fun i j =>
        (((Finset.univ : Finset E).filter (fun g =>
          g ≠ f ∧ row i ∈ H.edge g ∧
            ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card : ℕ)
    have hrow_mem : ∀ i : Fin k, row i ∈ H.edge f := by
      intro i
      have hmem :
          ((Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm i).1 ∈ fVerts :=
        ((Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm i).2
      simpa [row, fVerts] using hmem
    have hA_nonneg : ∀ i j, 0 ≤ A i j := by
      intro i j
      change
        (0 : ℝ) ≤
          (((Finset.univ : Finset E).filter (fun g =>
            g ≠ f ∧ row i ∈ H.edge g ∧
              ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card : ℝ)
      exact_mod_cast Nat.zero_le
        (((Finset.univ : Finset E).filter (fun g =>
          g ≠ f ∧ row i ∈ H.edge g ∧
            ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card)
    have htable_cross :
        (∑ j : Fin X.card,
          ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0))
          ≤ (((k : ℝ) - 1) ^ 2 / 2) * (D : ℝ) ^ 2 := by
      have hCpos : (0 : ℝ) < (D : ℝ) := by
        exact_mod_cast hD_ge_one
      have hTpos : (0 : ℝ) < ((k * (k - 1) * D : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hD_ge_one
      have hq :
          k * (k - 1) = Nat.floor (((k * (k - 1) * D : ℕ) : ℝ) / (D : ℝ)) := by
        have hDne : ((D : ℝ) ≠ 0) := ne_of_gt hCpos
        have hdiv :
            (((k * (k - 1) * D : ℕ) : ℝ) / (D : ℝ))
              = (k * (k - 1) : ℕ) := by
          rw [Nat.cast_mul, Nat.cast_mul]
          field_simp [hDne]
        rw [hdiv]
        exact (Nat.floor_natCast (k * (k - 1))).symm
      have hr :
          (0 : ℝ) =
            ((k * (k - 1) * D : ℕ) : ℝ) - ((k * (k - 1) : ℕ) : ℝ) * (D : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul]
        ring
      have hcol :
          ∀ j : Fin X.card, (∑ i : Fin k, A i j) ≤ (D : ℝ) := by
        intro j
        let x : V := ((Finset.equivFin X).symm j).1
        let S : Fin k → Finset E := fun i =>
          (Finset.univ : Finset E).filter (fun g =>
            g ≠ f ∧ row i ∈ H.edge g ∧ x ∈ H.edge g)
        have hpairwise :
            ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint S := by
          rw [Finset.pairwiseDisjoint_iff]
          intro i _ i' _ hnonempty
          rcases hnonempty with ⟨g, hginter⟩
          have hgi : g ∈ S i := (Finset.mem_inter.mp hginter).1
          have hgi' : g ∈ S i' := (Finset.mem_inter.mp hginter).2
          have hgiS : g ≠ f ∧ row i ∈ H.edge g ∧ x ∈ H.edge g := by
            simpa [S] using hgi
          have hgiS' : g ≠ f ∧ row i' ∈ H.edge g ∧ x ∈ H.edge g := by
            simpa [S] using hgi'
          by_contra hii_ne
          have hrows_ne : row i ≠ row i' := by
            intro hroweq
            have :
                (Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm i =
                  (Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm i' := by
              ext
              exact hroweq
            exact hii_ne ((EquivLike.injective
              (Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])).symm) this)
          have hg_non : (H.edge g ∩ H.edge f).Nonempty :=
            ⟨row i, Finset.mem_inter.mpr ⟨hgiS.2.1, hrow_mem i⟩⟩
          have hcard_one := hneighbor_one g hgiS.1 hg_non
          have hpair_sub : ({row i, row i'} : Finset V) ⊆ H.edge g ∩ H.edge f := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hgiS.2.1, hrow_mem i⟩
            · exact Finset.mem_inter.mpr ⟨hgiS'.2.1, hrow_mem i'⟩
          have htwo : 2 ≤ (H.edge g ∩ H.edge f).card := by
            calc
              2 = ({row i, row i'} : Finset V).card := (Finset.card_pair hrows_ne).symm
              _ ≤ (H.edge g ∩ H.edge f).card := Finset.card_le_card hpair_sub
          omega
        have hsub_degree :
            (Finset.univ : Finset (Fin k)).biUnion S ⊆
              ((Finset.univ : Finset E).filter (fun g => x ∈ H.edge g)) := by
          intro g hg
          rcases Finset.mem_biUnion.mp hg with ⟨i, _, hgi⟩
          have hgiS : g ≠ f ∧ row i ∈ H.edge g ∧ x ∈ H.edge g := by
            simpa [S] using hgi
          simp [hgiS.2.2]
        have hsum_nat :
            (∑ i : Fin k, ((S i).card)) ≤ HypergraphDegree H x := by
          calc
            (∑ i : Fin k, ((S i).card))
                = ((Finset.univ : Finset (Fin k)).biUnion S).card := by
                  rw [Finset.card_biUnion hpairwise]
            _ ≤ ((Finset.univ : Finset E).filter (fun g => x ∈ H.edge g)).card :=
                  Finset.card_le_card hsub_degree
            _ = HypergraphDegree H x := by rfl
        have hdeg : HypergraphDegree H x ≤ D := hH.2.2 x
        have hsumA :
            (∑ i : Fin k, A i j) = ((∑ i : Fin k, ((S i).card)) : ℝ) := by
          simp [A, S, x]
        rw [hsumA]
        exact_mod_cast le_trans hsum_nat hdeg
      have htot :
          (∑ i : Fin k, ∑ j : Fin X.card, A i j)
            ≤ ((k * (k - 1) * D : ℕ) : ℝ) := by
        have hx_out : ∀ x : V, x ∈ X → x ∉ H.edge f := by
          intro x hx
          rcases Finset.mem_biUnion.mp hx with ⟨g, _, hxg⟩
          by_cases hgf : g = f
          · simp [X, hgf] at hxg
          · have hxg' : x ∈ (H.edge g).filter (fun x => x ∉ H.edge f) := by
              simpa [X, hgf] using hxg
            exact (Finset.mem_filter.mp hxg').2
        have hrow :
            ∀ i : Fin k, (∑ j : Fin X.card, A i j)
              ≤ (((D - 1) * (k - 1) : ℕ) : ℝ) := by
          intro i
          let C : Finset E :=
            (Finset.univ : Finset E).filter (fun g => g ≠ f ∧ row i ∈ H.edge g)
          have hC_card : C.card = D - 1 := by
            simpa [C] using hneighbor_classes.1 (row i) (hrow_mem i)
          have hper_edge :
              ∀ g : E, g ∈ C → (X ∩ H.edge g).card ≤ k - 1 := by
            intro g hg
            have hgC : g ≠ f ∧ row i ∈ H.edge g := by
              simpa [C] using hg
            have hnon : (H.edge g ∩ H.edge f).Nonempty :=
              ⟨row i, Finset.mem_inter.mpr ⟨hgC.2, hrow_mem i⟩⟩
            have hone : (H.edge f ∩ H.edge g).card = 1 := by
              simpa [Finset.inter_comm] using hneighbor_one g hgC.1 hnon
            have hdiff_card : (H.edge g \ H.edge f).card = k - 1 := by
              rw [Finset.card_sdiff, hH.1 g, hone]
            have hsub : X ∩ H.edge g ⊆ H.edge g \ H.edge f := by
              intro x hx
              have hxX : x ∈ X := (Finset.mem_inter.mp hx).1
              have hxg : x ∈ H.edge g := (Finset.mem_inter.mp hx).2
              exact Finset.mem_sdiff.mpr ⟨hxg, hx_out x hxX⟩
            exact (Finset.card_le_card hsub).trans_eq hdiff_card
          have hrow_nat :
              (∑ j : Fin X.card,
                (C.filter (fun g => ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card)
                ≤ C.card * (k - 1) :=
            FiniteBipartiteIncidenceTableRowBound X C (fun g => H.edge g) (k - 1) hper_edge
          have hrow_nat' :
              (∑ j : Fin X.card,
                (((Finset.univ : Finset E).filter (fun g =>
                  g ≠ f ∧ row i ∈ H.edge g ∧
                    ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card))
                ≤ (D - 1) * (k - 1) := by
            calc
              (∑ j : Fin X.card,
                (((Finset.univ : Finset E).filter (fun g =>
                  g ≠ f ∧ row i ∈ H.edge g ∧
                    ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card))
                  = ∑ j : Fin X.card,
                      (C.filter (fun g => ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card := by
                    apply Finset.sum_congr rfl
                    intro j _
                    congr 1
                    ext g
                    simp [C, and_assoc]
              _ ≤ C.card * (k - 1) := hrow_nat
              _ = (D - 1) * (k - 1) := by rw [hC_card]
          have hrowA :
              (∑ j : Fin X.card, A i j) =
                ((∑ j : Fin X.card,
                  (((Finset.univ : Finset E).filter (fun g =>
                    g ≠ f ∧ row i ∈ H.edge g ∧
                      ((Finset.equivFin X).symm j).1 ∈ H.edge g)).card)) : ℝ) := by
            simp [A]
          rw [hrowA]
          exact_mod_cast hrow_nat'
        calc
          (∑ i : Fin k, ∑ j : Fin X.card, A i j)
              ≤ ∑ _i : Fin k, (((D - 1) * (k - 1) : ℕ) : ℝ) :=
                Finset.sum_le_sum (fun i _ => hrow i)
          _ = (k : ℝ) * (((D - 1) * (k - 1) : ℕ) : ℝ) := by
                simp
          _ ≤ ((k * (k - 1) * D : ℕ) : ℝ) := by
                have hDsub : (D - 1 : ℕ) ≤ D := Nat.sub_le _ _
                have hnat :
                    k * ((D - 1) * (k - 1)) ≤ k * (k - 1) * D := by
                  nlinarith [Nat.mul_le_mul_left (k * (k - 1)) hDsub]
                exact_mod_cast hnat
      have hraw :=
        TablePairFillingBound (k := k) (n := X.card) hk_ge_two
          (D : ℝ) (((k * (k - 1) * D : ℕ) : ℝ)) (k * (k - 1)) 0
          A hCpos hTpos hq hr hA_nonneg hcol htot
      have hrhs :
          (((k : ℝ) - 1) / (2 * (k : ℝ))) *
            (((k * (k - 1) : ℕ) : ℝ) * (D : ℝ) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ))
            = (((k : ℝ) - 1) ^ 2 / 2) * (D : ℝ) ^ 2 := by
        have hk_ne : (k : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hk_ge_two))
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)]
        field_simp [hk_ne]
        ring
      exact hraw.trans_eq hrhs
    let G : SimpleGraph E := LineGraphOfHypergraph H
    let N : Finset E :=
      (Finset.univ : Finset E).filter
        (fun g => g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty)
    let adjacentPairs : Finset (Finset E) :=
      ((G.neighborFinset f).powersetCard 2).filter (fun S =>
        ∃ x, x ∈ S ∧ ∃ y, y ∈ S ∧ x ≠ y ∧ G.Adj x y)
    have hG_neighbor : G.neighborFinset f = N := by
      ext g
      simp only [G, N, LineGraphOfHypergraph, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hfg, hnon⟩
        exact ⟨hfg.symm, by simpa [Finset.inter_comm] using hnon⟩
      · rintro ⟨hgf, hnon⟩
        exact ⟨hgf.symm, by simpa [Finset.inter_comm] using hnon⟩
    have hG_neighbor_card : (G.neighborFinset f).card = k * D - k := by
      rw [hG_neighbor]
      exact hneighbor_card
    have hcomplement :
        Nat.choose (G.neighborFinset f).card 2 - adjacentPairs.card ≤
          @IndependentPairCount E _ _ G (Classical.decRel G.Adj) f := by
      simpa [adjacentPairs] using
        (IndependentPairComplementLowerBound (G := G) (v := f) (B := adjacentPairs.card)
          (by rfl : adjacentPairs.card ≤ adjacentPairs.card))
    let C : V → Finset E :=
      fun v => (Finset.univ : Finset E).filter (fun g => g ≠ f ∧ v ∈ H.edge g)
    let sameClassPairs : Finset (Finset E) :=
      (Finset.univ : Finset (Finset E)).filter
        (fun S => S.card = 2 ∧ ∃ v ∈ H.edge f, S ⊆ C v)
    let I : Fin k → Fin X.card → Finset E :=
      fun i j =>
        (Finset.univ : Finset E).filter (fun g =>
          g ≠ f ∧ row i ∈ H.edge g ∧
            ((Finset.equivFin X).symm j).1 ∈ H.edge g)
    let crossPairs : Finset (Finset E) :=
      (Finset.univ : Finset (Fin X.card)).biUnion (fun j =>
        (Finset.univ : Finset (Fin k)).biUnion (fun i =>
          ((Finset.univ : Finset (Fin k)).filter (fun i' => i < i')).biUnion (fun i' =>
            ((I i j).product (I i' j)).image
              (fun p : E × E => ({p.1, p.2} : Finset E)))))
    have hcross_card_nat :
        crossPairs.card ≤
          ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then (I i j).card * (I i' j).card else 0) := by
      calc
        crossPairs.card
            ≤ ∑ j : Fin X.card,
                ((Finset.univ : Finset (Fin k)).biUnion (fun i =>
                    ((Finset.univ : Finset (Fin k)).filter (fun i' => i < i')).biUnion
                      (fun i' =>
                        ((I i j).product (I i' j)).image
                          (fun p : E × E => ({p.1, p.2} : Finset E))))).card := by
              dsimp [crossPairs]
              exact Finset.card_biUnion_le
        _ ≤ ∑ j : Fin X.card, ∑ i : Fin k,
                  (((Finset.univ : Finset (Fin k)).filter (fun i' => i < i')).biUnion
                    (fun i' =>
                      ((I i j).product (I i' j)).image
                        (fun p : E × E => ({p.1, p.2} : Finset E)))).card := by
              exact Finset.sum_le_sum (fun j _ => Finset.card_biUnion_le)
        _ ≤ ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' ∈
                ((Finset.univ : Finset (Fin k)).filter (fun i' => i < i')),
                (((I i j).product (I i' j)).image
                  (fun p : E × E => ({p.1, p.2} : Finset E))).card := by
              exact Finset.sum_le_sum (fun j _ =>
                Finset.sum_le_sum (fun i _ => Finset.card_biUnion_le))
        _ ≤ ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' ∈
                ((Finset.univ : Finset (Fin k)).filter (fun i' => i < i')),
                (I i j).card * (I i' j).card := by
              exact Finset.sum_le_sum (fun j _ =>
                Finset.sum_le_sum (fun i _ =>
                  Finset.sum_le_sum (fun i' _ =>
                    (Finset.card_image_le.trans_eq (Finset.card_product _ _)))))
        _ = ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
              (if i < i' then (I i j).card * (I i' j).card else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_filter]
    have hcross_card :
        (crossPairs.card : ℝ) ≤
          ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0) := by
      have hcast :
          ((∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then (I i j).card * (I i' j).card else 0) : ℕ) : ℝ)
            =
          ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
            (if i < i' then A i j * A i' j else 0) := by
        simp [A, I, Nat.cast_sum, Nat.cast_mul]
      rw [← hcast]
      exact_mod_cast hcross_card_nat
    have hsame_card :
        sameClassPairs.card ≤ k * Nat.choose (D - 1) 2 := by
      simpa [C, sameClassPairs] using hneighbor_classes.2.2.2
    have hadj_subset : adjacentPairs ⊆ sameClassPairs ∪ crossPairs := by
      intro S hS
      have hS' : S ∈ (G.neighborFinset f).powersetCard 2 ∧
          ∃ x, x ∈ S ∧ ∃ y, y ∈ S ∧ x ≠ y ∧ G.Adj x y := by
        simpa [adjacentPairs] using hS
      rcases hS'.2 with ⟨g, hgS, g', hg'S, hgg', hgg'adj⟩
      have hS_card : S.card = 2 := (Finset.mem_powersetCard.mp hS'.1).2
      have hpair_sub : ({g, g'} : Finset E) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hgS
        · exact hg'S
      have hS_eq : S = ({g, g'} : Finset E) := by
        exact (Finset.eq_of_subset_of_card_le hpair_sub (by
          rw [Finset.card_pair hgg', hS_card])).symm
      have hgN : g ∈ N := by
        have hg_nei : g ∈ G.neighborFinset f := (Finset.mem_powersetCard.mp hS'.1).1 hgS
        rw [← hG_neighbor]
        exact hg_nei
      have hg'N : g' ∈ N := by
        have hg_nei : g' ∈ G.neighborFinset f := (Finset.mem_powersetCard.mp hS'.1).1 hg'S
        rw [← hG_neighbor]
        exact hg_nei
      have hgN' : g ≠ f ∧ (H.edge g ∩ H.edge f).Nonempty := by
        simpa [N] using hgN
      have hg'N' : g' ≠ f ∧ (H.edge g' ∩ H.edge f).Nonempty := by
        simpa [N] using hg'N
      rcases hneighbor_classes.2.2.1 g |>.mp (by simpa [N] using hgN) with ⟨v, hvf, hgvC⟩
      rcases hneighbor_classes.2.2.1 g' |>.mp (by simpa [N] using hg'N) with ⟨v', hv'f, hgv'C⟩
      by_cases hvv' : v = v'
      · subst v'
        have hS_same : S ∈ sameClassPairs := by
          simp [sameClassPairs, hS_card]
          exact ⟨v, hvf, by
            rw [hS_eq]
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hgvC
            · exact hgv'C⟩
        exact Finset.mem_union.mpr (Or.inl hS_same)
      · have hrow_v : ∃ i : Fin k, row i = v := by
          let e : fVerts ≃ Fin k :=
            Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])
          let vv : fVerts := ⟨v, by simpa [fVerts] using hvf⟩
          refine ⟨e vv, ?_⟩
          change (e.symm (e vv)).1 = v
          simpa [vv] using congrArg Subtype.val (Equiv.symm_apply_apply e vv)
        have hrow_v' : ∃ i : Fin k, row i = v' := by
          let e : fVerts ≃ Fin k :=
            Finset.equivFinOfCardEq (s := fVerts) (by simp [fVerts, hH.1 f])
          let vv : fVerts := ⟨v', by simpa [fVerts] using hv'f⟩
          refine ⟨e vv, ?_⟩
          change (e.symm (e vv)).1 = v'
          simpa [vv] using congrArg Subtype.val (Equiv.symm_apply_apply e vv)
        rcases hrow_v with ⟨i, hi⟩
        rcases hrow_v' with ⟨i', hi'⟩
        have hii' : i ≠ i' := by
          intro hii
          exact hvv' (by simpa [← hi, ← hi', hii])
        have hcommon : (H.edge g ∩ H.edge g').Nonempty := by
          simpa [G, LineGraphOfHypergraph] using hgg'adj.2
        rcases hcommon with ⟨x, hxcommon⟩
        have hxg : x ∈ H.edge g := (Finset.mem_inter.mp hxcommon).1
        have hxg' : x ∈ H.edge g' := (Finset.mem_inter.mp hxcommon).2
        have hx_not_f : x ∉ H.edge f := by
          intro hxf
          have hgint : ({v, x} : Finset V) ⊆ H.edge g ∩ H.edge f := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with hyv | hyx
            · rw [hyv]
              have hgvC' : g ≠ f ∧ v ∈ H.edge g := by simpa [C] using hgvC
              exact Finset.mem_inter.mpr ⟨hgvC'.2, hvf⟩
            · rw [hyx]
              exact Finset.mem_inter.mpr ⟨hxg, hxf⟩
          by_cases hvx : v = x
          · subst x
            have hg'int : ({v', v} : Finset V) ⊆ H.edge g' ∩ H.edge f := by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with hyv' | hyv
              · rw [hyv']
                have hgv'C' : g' ≠ f ∧ v' ∈ H.edge g' := by simpa [C] using hgv'C
                exact Finset.mem_inter.mpr ⟨hgv'C'.2, hv'f⟩
              · rw [hyv]
                exact Finset.mem_inter.mpr ⟨hxg', hvf⟩
            have htwo : 2 ≤ (H.edge g' ∩ H.edge f).card := by
              calc
                2 = ({v', v} : Finset V).card := (Finset.card_pair (Ne.symm hvv')).symm
                _ ≤ (H.edge g' ∩ H.edge f).card := Finset.card_le_card hg'int
            have hone := hneighbor_one g' hg'N'.1 hg'N'.2
            omega
          · have htwo : 2 ≤ (H.edge g ∩ H.edge f).card := by
              calc
                2 = ({v, x} : Finset V).card := (Finset.card_pair hvx).symm
                _ ≤ (H.edge g ∩ H.edge f).card := Finset.card_le_card hgint
            have hone := hneighbor_one g hgN'.1 hgN'.2
            omega
        have hxX : x ∈ X := by
          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, ?_⟩
          simp [X, hgN'.1, hxg, hx_not_f]
        let j : Fin X.card := Finset.equivFin X ⟨x, hxX⟩
        have hxj : ((Finset.equivFin X).symm j).1 = x := by
          simp [j]
        have hgi : g ∈ I i j := by
          have hgvC' : g ≠ f ∧ v ∈ H.edge g := by simpa [C] using hgvC
          simp [I, hi, hxj, hgvC'.1, hgvC'.2, hxg]
        have hg'i' : g' ∈ I i' j := by
          have hgv'C' : g' ≠ f ∧ v' ∈ H.edge g' := by simpa [C] using hgv'C
          simp [I, hi', hxj, hgv'C'.1, hgv'C'.2, hxg']
        by_cases hi_lt : i < i'
        · have hcross : S ∈ crossPairs := by
            rw [hS_eq]
            dsimp [crossPairs]
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩
            refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
            refine Finset.mem_biUnion.mpr ⟨i', by simp [hi_lt], ?_⟩
            refine Finset.mem_image.mpr ⟨(g, g'), ?_, rfl⟩
            exact Finset.mem_product.mpr ⟨hgi, hg'i'⟩
          exact Finset.mem_union.mpr (Or.inr hcross)
        · have hi'_lt : i' < i := by
            exact lt_of_le_of_ne (not_lt.mp hi_lt) (Ne.symm hii')
          have hgi' : g ∈ I i j := hgi
          have hg'i : g' ∈ I i' j := hg'i'
          have hcross : S ∈ crossPairs := by
            rw [hS_eq]
            have hpair_comm : ({g, g'} : Finset E) = ({g', g} : Finset E) := by
              ext z
              simp [or_comm]
            rw [hpair_comm]
            dsimp [crossPairs]
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩
            refine Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ i', ?_⟩
            refine Finset.mem_biUnion.mpr ⟨i, by simp [hi'_lt], ?_⟩
            refine Finset.mem_image.mpr ⟨(g', g), ?_, rfl⟩
            exact Finset.mem_product.mpr ⟨hg'i, hgi'⟩
          exact Finset.mem_union.mpr (Or.inr hcross)
    have hadj_card_real :
        (adjacentPairs.card : ℝ) ≤
          (k * Nat.choose (D - 1) 2 : ℕ) +
            ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
              (if i < i' then A i j * A i' j else 0) := by
      have hnat :
          adjacentPairs.card ≤ sameClassPairs.card + crossPairs.card := by
        exact (Finset.card_le_card hadj_subset).trans (Finset.card_union_le _ _)
      calc
        (adjacentPairs.card : ℝ) ≤ (sameClassPairs.card + crossPairs.card : ℕ) := by
          exact_mod_cast hnat
        _ = (sameClassPairs.card : ℝ) + (crossPairs.card : ℝ) := by norm_num
        _ ≤ (k * Nat.choose (D - 1) 2 : ℕ) +
            ∑ j : Fin X.card, ∑ i : Fin k, ∑ i' : Fin k,
              (if i < i' then A i j * A i' j else 0) := by
          exact add_le_add (by exact_mod_cast hsame_card) hcross_card
    have hadj_bound :
          (adjacentPairs.card : ℝ) ≤
          (k * Nat.choose (D - 1) 2 : ℕ) +
            (((k : ℝ) - 1) ^ 2 / 2) * (D : ℝ) ^ 2 :=
      hadj_card_real.trans (add_le_add (le_refl _) htable_cross)
    have hcomp_real :
        ((Nat.choose (G.neighborFinset f).card 2 : ℕ) : ℝ) -
            (adjacentPairs.card : ℝ) ≤
          (@IndependentPairCount E _ _ G (Classical.decRel G.Adj) f : ℝ) := by
      have hadj_le_total :
          adjacentPairs.card ≤ Nat.choose (G.neighborFinset f).card 2 := by
        calc
          adjacentPairs.card
              ≤ ((G.neighborFinset f).powersetCard 2).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
          _ = Nat.choose (G.neighborFinset f).card 2 := by
                rw [Finset.card_powersetCard]
      have hcast_sub :
          (((Nat.choose (G.neighborFinset f).card 2 - adjacentPairs.card : ℕ) : ℝ)) =
            ((Nat.choose (G.neighborFinset f).card 2 : ℕ) : ℝ) -
              (adjacentPairs.card : ℝ) := by
        rw [Nat.cast_sub hadj_le_total]
      rw [← hcast_sub]
      exact_mod_cast hcomplement
    have hchoose_real :
        ((Nat.choose (G.neighborFinset f).card 2 : ℕ) : ℝ) =
          ((k * D - k : ℕ) * ((k * D - k : ℕ) - 1) / 2 : ℝ) := by
      rw [hG_neighbor_card]
      exact Nat.cast_choose_two (K := ℝ) (k * D - k)
    have hmain_lower :
        ((Nat.choose (G.neighborFinset f).card 2 : ℕ) : ℝ) -
            ((k * Nat.choose (D - 1) 2 : ℕ) +
              (((k : ℝ) - 1) ^ 2 / 2) * (D : ℝ) ^ 2)
          ≤ (@IndependentPairCount E _ _ G (Classical.decRel G.Adj) f : ℝ) := by
      nlinarith [hcomp_real, hadj_bound]
    have harith :
        (((k : ℝ) - 1) / 2) * (D : ℝ) ^ 2 - (k : ℝ) ^ 2 * (D : ℝ)
          ≤
        ((Nat.choose (G.neighborFinset f).card 2 : ℕ) : ℝ) -
            ((k * Nat.choose (D - 1) 2 : ℕ) +
              (((k : ℝ) - 1) ^ 2 / 2) * (D : ℝ) ^ 2) := by
      rw [hchoose_real]
      have hkD_sub : k * D - k = k * (D - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      have hDsub_cast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
        rw [Nat.cast_sub hD_ge_one]
        norm_num
      have hkDsub_cast : ((k * D - k : ℕ) : ℝ) = (k : ℝ) * ((D : ℝ) - 1) := by
        rw [hkD_sub, Nat.cast_mul, hDsub_cast]
      have hchooseD_cast :
          ((Nat.choose (D - 1) 2 : ℕ) : ℝ) =
            ((D : ℝ) - 1) * ((D : ℝ) - 2) / 2 := by
        rw [Nat.cast_choose_two (K := ℝ), hDsub_cast]
        ring
      rw [Nat.cast_mul, hchooseD_cast, hkDsub_cast]
      ring_nf
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k,
        show (0 : ℝ) ≤ (D : ℝ) by exact_mod_cast Nat.zero_le D]
    exact le_trans harith hmain_lower
