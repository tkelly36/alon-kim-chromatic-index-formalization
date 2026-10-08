import Tablet.SubhypergraphInheritance

-- [TABLET NODE: CanonicalResidualEmbedding]
theorem CanonicalResidualEmbedding {V E F : Type*}
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] [DecidableEq V]
    (H : MultiHypergraph V E) (C : Finset E) (embed : F → E)
    (Hc : MultiHypergraph V F)
    (hedge : ∀ f, Hc.edge f = H.edge (embed f))
    (hcover : ∀ e, e ∉ C ↔ ∃ f, embed f = e) :
    let R := {e : E // e ∉ C}
    let Hr : MultiHypergraph V R := ⟨fun e => H.edge e.val⟩
    (∃ j : R → F, Function.Injective j ∧ ∀ e, embed (j e) = e.val) ∧
      SubhypergraphOf Hr Hc ∧ SubhypergraphOf Hr H ∧
      ∀ v, HypergraphDegree Hr v ≤ HypergraphDegree Hc v := by
-- BODY
  classical
  dsimp only
  let j : {e : E // e ∉ C} → F := fun e => Classical.choose ((hcover e.val).mp e.property)
  have hj : ∀ e, embed (j e) = e.val := fun e => Classical.choose_spec ((hcover e.val).mp e.property)
  have hinj : Function.Injective j := by
    intro e f h
    apply Subtype.ext
    exact (hj e).symm.trans ((congrArg embed h).trans (hj f))
  have hs : SubhypergraphOf (⟨fun e : {e : E // e ∉ C} => H.edge e.val⟩) Hc := by
    refine ⟨j, hinj, ?_⟩
    intro e
    change H.edge e.val = Hc.edge (j e)
    rw [hedge, hj]
  exact ⟨⟨j, hinj, hj⟩, hs, ⟨Subtype.val, Subtype.val_injective, fun _ => rfl⟩,
    (SubhypergraphInheritance _ Hc hs).2.2⟩
