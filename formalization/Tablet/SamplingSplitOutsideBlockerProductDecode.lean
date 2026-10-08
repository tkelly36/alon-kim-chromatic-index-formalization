import Tablet.Preamble

-- [TABLET NODE: SamplingSplitOutsideBlockerProductDecode]
noncomputable def SamplingSplitOutsideBlockerProductDecode
    {V V' T : Type*} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] (s : V → T) (t : V' → T)
    (q : T → ℝ × ℝ) :
    (Finset V × (V → ℝ)) × (Finset V' × (V' → ℝ)) := by
-- BODY
  classical
  exact ((Finset.univ.filter fun v => (q (s v)).1 = 1,
      fun v => (q (s v)).2),
    (Finset.univ.filter fun v => (q (t v)).1 = 1,
      fun v => (q (t v)).2))
