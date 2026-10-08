import Tablet.LocalBParameterRealAntitone
import Tablet.LocalBParameterRealNatCast
import Tablet.RealDegreeFloorBound
import Tablet.UniformHypergraphLineDegreeBound

-- [TABLET NODE: LocalBParameterRealFloorTransfer]
theorem LocalBParameterRealFloorTransfer {V E : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (H : MultiHypergraph V E) [DecidableRel (LineGraphOfHypergraph H).Adj]
    {k : ℕ} (hk : 0 < k) (hu : UniformHypergraph H k)
    {r : ℝ} (hr : 1 ≤ r) (hd : ∀ v, (HypergraphDegree H v : ℝ) ≤ r) (e : E) :
    LocalBParameterReal (LineGraphOfHypergraph H) ((k : ℝ) * r) e ≤
      LocalBParameter (LineGraphOfHypergraph H) (k * ⌊r⌋₊) e := by
-- BODY
  have hn : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa using hr)
  have hpos : (0 : ℝ) < (k * ⌊r⌋₊ : ℕ) := by exact_mod_cast Nat.mul_pos hk (by omega)
  have hscale : ((k * ⌊r⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) * r := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by positivity)
  have hdeg : ((LineGraphOfHypergraph H).degree e : ℝ) ≤ (k * ⌊r⌋₊ : ℕ) := by
    exact_mod_cast (UniformHypergraphLineDegreeBound H hu (RealDegreeFloorBound H hd) e).trans
      (Nat.mul_le_mul_left k (Nat.sub_le _ _))
  rw [← LocalBParameterRealNatCast]
  exact LocalBParameterRealAntitone _ e hpos hscale hdeg
