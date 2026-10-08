import Tablet.HypergraphClass

-- [TABLET NODE: KUniformKSimpleBoundedLocalPattern]
def KUniformKSimpleBoundedLocalPattern (k D : ℕ) : Type :=
-- BODY
  {P :
    ((Fin (1 + k * (D - 1)) → Finset (Fin (k + k * k * (D - 1)))) ×
      Fin (1 + k * (D - 1))) //
    ({ edge := P.1 } :
      MultiHypergraph
        (Fin (k + k * k * (D - 1)))
        (Fin (1 + k * (D - 1)))) ∈
      HypergraphClass
        (V := Fin (k + k * k * (D - 1)))
        (E := Fin (1 + k * (D - 1))) k k D}
