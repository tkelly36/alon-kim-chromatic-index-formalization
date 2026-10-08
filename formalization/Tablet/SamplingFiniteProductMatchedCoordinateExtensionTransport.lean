import Tablet.Preamble

open BigOperators

-- [TABLET NODE: SamplingFiniteProductMatchedCoordinateExtensionTransport]
theorem SamplingFiniteProductMatchedCoordinateExtensionTransport
    {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (p baseMass sourceExt targetExt : ℝ)
    (sourceAD sourceD sourceK : Finset V)
    (targetAD targetD targetK : Finset V')
    (sourceThreshold : V → ℝ) (targetThreshold : V' → ℝ)
    (hsource :
      sourceExt =
        baseMass *
          (p ^ sourceAD.card * (1 - p) ^ (sourceD.card - sourceAD.card)) *
            (∏ v : V, if v ∈ sourceK then sourceThreshold v else 1))
    (htarget :
      targetExt =
        baseMass *
          (p ^ targetAD.card * (1 - p) ^ (targetD.card - targetAD.card)) *
            (∏ v' : V', if v' ∈ targetK then targetThreshold v' else 1))
    (hactivation :
      p ^ sourceAD.card * (1 - p) ^ (sourceD.card - sourceAD.card) =
        p ^ targetAD.card * (1 - p) ^ (targetD.card - targetAD.card))
    (hpriority :
      (∏ v : V, if v ∈ sourceK then sourceThreshold v else 1) =
        (∏ v' : V', if v' ∈ targetK then targetThreshold v' else 1)) :
    sourceExt = targetExt := by
-- BODY
  rw [hsource, htarget, hactivation, hpriority]
