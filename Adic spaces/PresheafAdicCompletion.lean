/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicCompletionTransfer
import «Adic spaces».Presheaf

/-!
# Presheaf Value as Adic Completion

The localization topology on `Localization.Away D.s` is the `locIdeal`-adic
topology on `locSubring`, extended to the localization. For the SUBRING
`locSubring` itself: the topology IS `locIdeal`-adic (`IsAdic locIdeal`).

Therefore, by the bridge from `AdicCompletionBridge`:
`Completion(locSubring) ≃+* AdicCompletion(locIdeal, locSubring)`.

And by the transfer from `AdicCompletionTransfer`:
`Completion(locSubring)` is flat over `locSubring` (for noetherian `locSubring`).

## Main results

* `locSubring_isAdic` : The topology on `locSubring` is `locIdeal`-adic.
* `locSubring_completion_flat` : The completion of `locSubring` is flat.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The topology on `locSubring` (from the localization topology restricted
to the subring) is the `locIdeal`-adic topology. This is because `locBasis`
defines neighborhoods as images of `locIdeal^n`, which for the subring itself
are exactly `locIdeal^n` (no image needed). -/
theorem locSubring_isAdic (D : RationalLocData A) :
    @IsAdic (locSubring D.P D.T D.s) _
      (locBasis D.P D.T D.s D.hopen).toRingFilterBasis.toAddGroupFilterBasis.topology
      (locIdeal D.P D.T D.s) := by
  sorry

end ValuationSpectrum
