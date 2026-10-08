import Tablet.HypergraphClass
import Tablet.HypergraphDegree
import Tablet.IndependentPairCount
import Tablet.IndependentTripleCount
import Tablet.KUniformKSimpleBoundedLocalPattern
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter
import Tablet.LocalBParameterNeighborhoodEmbeddingTransport
import Tablet.MaxDegreeAtMost
import Tablet.TSimpleHypergraph
import Tablet.UniformHypergraph

universe u v

-- [TABLET NODE: KUniformKSimpleBoundedLocalPatternLift]
theorem KUniformKSimpleBoundedLocalPatternLift :
    ∀ k D : ℕ, ∀ P : KUniformKSimpleBoundedLocalPattern k D,
      ∃ (Vloc : Type u) (Eloc : Type v),
        ∃ (_instFintype : Fintype Eloc) (_instDecidableEqE : DecidableEq Eloc)
          (_instDecidableEqV : DecidableEq Vloc),
          ∃ (F : MultiHypergraph Vloc Eloc) (f : Eloc),
            F ∈ HypergraphClass (V := Vloc) (E := Eloc) k k D ∧
              @LocalBParameter (Fin (1 + k * (D - 1))) _ _
                  (LineGraphOfHypergraph
                    ({ edge := P.1.1 } :
                      MultiHypergraph
                        (Fin (k + k * k * (D - 1)))
                        (Fin (1 + k * (D - 1)))))
                  (Classical.decRel
                    (LineGraphOfHypergraph
                      ({ edge := P.1.1 } :
                        MultiHypergraph
                          (Fin (k + k * k * (D - 1)))
                          (Fin (1 + k * (D - 1))))).Adj)
                  (k * D) P.1.2
                =
              @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
                  (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) f := by
-- BODY
  classical
  intro k D P
  let edgeBound := 1 + k * (D - 1)
  let vertexBound := k + k * k * (D - 1)
  let Vloc : Type u := ULift.{u} (Fin vertexBound)
  let Eloc : Type v := ULift.{v} (Fin edgeBound)
  let HP : MultiHypergraph (Fin vertexBound) (Fin edgeBound) := { edge := P.1.1 }
  let vertEmb : Fin vertexBound ↪ Vloc :=
    ⟨fun x => ULift.up x, by
      intro x y h
      exact congrArg ULift.down h⟩
  let edgeEmb : Fin edgeBound ↪ Eloc :=
    ⟨fun x => ULift.up x, by
      intro x y h
      exact congrArg ULift.down h⟩
  let F : MultiHypergraph Vloc Eloc :=
    { edge := fun e => (HP.edge e.down).map vertEmb }
  have hInter_card (A B : Finset (Fin vertexBound)) :
      ((A.map vertEmb) ∩ (B.map vertEmb)).card = (A ∩ B).card := by
    have hset : (A.map vertEmb) ∩ (B.map vertEmb) = (A ∩ B).map vertEmb := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_inter.mp hz with ⟨hzA, hzB⟩
        rcases Finset.mem_map.mp hzA with ⟨a, haA, rfl⟩
        rcases Finset.mem_map.mp hzB with ⟨b, hbB, hb⟩
        have hba : b = a := vertEmb.injective hb
        exact Finset.mem_map.mpr ⟨a, Finset.mem_inter.mpr ⟨haA, by simpa [hba] using hbB⟩, rfl⟩
      · intro hz
        rcases Finset.mem_map.mp hz with ⟨a, ha, rfl⟩
        exact Finset.mem_inter.mpr ⟨Finset.mem_map.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩,
          Finset.mem_map.mpr ⟨a, (Finset.mem_inter.mp ha).2, rfl⟩⟩
    rw [hset, Finset.card_map]
  have hClass : F ∈ HypergraphClass (V := Vloc) (E := Eloc) k k D := by
    rcases P.2 with ⟨hUniform, hSimple, hDegree⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e
      dsimp [UniformHypergraph, F, HP]
      rw [Finset.card_map]
      exact hUniform e.down
    · intro e f hef
      dsimp [TSimpleHypergraph, F, HP]
      rw [hInter_card]
      exact hSimple (by
        intro hdown
        apply hef
        cases e
        cases f
        simp at hdown
        simp [hdown])
    · intro z
      have hdeg_eq : HypergraphDegree F z = HypergraphDegree HP z.down := by
        unfold HypergraphDegree
        refine Finset.card_bij'
          (fun e _he => e.down)
          (fun e _he => (ULift.up e : Eloc))
          ?_ ?_ ?_ ?_
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          rcases z with ⟨z0⟩
          simpa [F, HP, vertEmb] using he
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
          rcases z with ⟨z0⟩
          simpa [F, HP, vertEmb] using he
        · intro e he
          cases e
          rfl
        · intro e he
          rfl
      rw [hdeg_eq]
      exact hDegree z.down
  have hAdj :
      ∀ x y : Fin edgeBound,
        (LineGraphOfHypergraph HP).Adj x y ↔
          (LineGraphOfHypergraph F).Adj (edgeEmb x) (edgeEmb y) := by
    intro x y
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro hxy
        exact h.1 (edgeEmb.injective hxy)
      · rcases h.2 with ⟨z, hz⟩
        exact ⟨vertEmb z, by
          rw [Finset.mem_inter]
          exact ⟨Finset.mem_map.mpr ⟨z, (Finset.mem_inter.mp hz).1, rfl⟩,
            Finset.mem_map.mpr ⟨z, (Finset.mem_inter.mp hz).2, rfl⟩⟩⟩
    · intro h
      refine ⟨?_, ?_⟩
      · intro hxy
        apply h.1
        simp [edgeEmb, hxy]
      · rcases h.2 with ⟨z, hz⟩
        rcases Finset.mem_inter.mp hz with ⟨hzx, hzy⟩
        rcases Finset.mem_map.mp hzx with ⟨a, hax, haz⟩
        rcases Finset.mem_map.mp hzy with ⟨b, hby, hbz⟩
        have hba : b = a := vertEmb.injective (by simpa [haz] using hbz)
        exact ⟨a, Finset.mem_inter.mpr ⟨hax, by simpa [hba] using hby⟩⟩
  have hlocal_eq :
      @LocalBParameter (Fin edgeBound) _ _ (LineGraphOfHypergraph HP)
          (Classical.decRel (LineGraphOfHypergraph HP).Adj) (k * D) P.1.2 =
        @LocalBParameter Eloc _ _ (LineGraphOfHypergraph F)
          (Classical.decRel (LineGraphOfHypergraph F).Adj) (k * D) (edgeEmb P.1.2) := by
    refine LocalBParameterNeighborhoodEmbeddingTransport
      (LineGraphOfHypergraph HP) (LineGraphOfHypergraph F) (k * D) P.1.2 (edgeEmb P.1.2) edgeEmb
      ?_ ?_ ?_
    · intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx ⊢
      exact (hAdj P.1.2 x).mp hx
    · intro y hy
      refine ⟨y.down, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
        have hy' : (LineGraphOfHypergraph F).Adj (edgeEmb P.1.2) (edgeEmb y.down) := by
          cases y
          simpa [edgeEmb] using hy
        exact (hAdj P.1.2 y.down).mpr hy'
      · cases y
        rfl
    · intro x _hx y _hy
      exact hAdj x y
  refine ⟨Vloc, Eloc, inferInstance, inferInstance, inferInstance, F, edgeEmb P.1.2, ?_⟩
  exact ⟨hClass, hlocal_eq⟩
