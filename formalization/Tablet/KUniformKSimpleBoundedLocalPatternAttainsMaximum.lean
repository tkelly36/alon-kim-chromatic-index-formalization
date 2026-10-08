import Tablet.FiniteRealFunctionAttainsMaximum
import Tablet.KUniformKSimpleBoundedLocalPattern
import Tablet.LineGraphOfHypergraph
import Tablet.LocalBParameter

-- [TABLET NODE: KUniformKSimpleBoundedLocalPatternAttainsMaximum]
theorem KUniformKSimpleBoundedLocalPatternAttainsMaximum :
    ∀ k D : ℕ,
      Nonempty (KUniformKSimpleBoundedLocalPattern k D) →
        ∃ Pmax : KUniformKSimpleBoundedLocalPattern k D,
          ∀ P : KUniformKSimpleBoundedLocalPattern k D,
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
              ≤
            @LocalBParameter (Fin (1 + k * (D - 1))) _ _
                (LineGraphOfHypergraph
                  ({ edge := Pmax.1.1 } :
                    MultiHypergraph
                      (Fin (k + k * k * (D - 1)))
                      (Fin (1 + k * (D - 1)))))
                (Classical.decRel
                  (LineGraphOfHypergraph
                    ({ edge := Pmax.1.1 } :
                      MultiHypergraph
                        (Fin (k + k * k * (D - 1)))
                        (Fin (1 + k * (D - 1))))).Adj)
                (k * D) Pmax.1.2 := by
-- BODY
  intro k D hnonempty
  classical
  letI : Fintype (KUniformKSimpleBoundedLocalPattern k D) := by
    unfold KUniformKSimpleBoundedLocalPattern
    infer_instance
  let score : KUniformKSimpleBoundedLocalPattern k D → ℝ :=
    fun P =>
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
  simpa [score] using
    (FiniteRealFunctionAttainsMaximum
      (ι := KUniformKSimpleBoundedLocalPattern k D) score)
