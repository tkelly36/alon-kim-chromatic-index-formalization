import Tablet.MultiHypergraph
import Mathlib.Data.ZMod.Basic

-- [TABLET NODE: OrderThreeAffineMultihypergraph]
def OrderThreeAffineMultihypergraph (q : ℕ) :
    MultiHypergraph (ZMod 3 × ZMod 3) (Option (ZMod 3 × ZMod 3 × Fin q)) where
-- BODY
  edge
    | none => Finset.univ.image (fun y : ZMod 3 => (0, y))
    | some (m, a, _) => Finset.univ.image (fun x : ZMod 3 => (x, m * x + a))
