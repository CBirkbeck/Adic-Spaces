/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison
import «Adic spaces».CompletionLocalization

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13): helpers

Helper lemmas about `canonicalMap` and `restrictionMapHom` that feed into the
iterated rational identification and the Laurent bridges. The Wedhorn
Example 6.38 machinery used to live here under the name `Example638`; that
block now lives in `«Adic spaces».Example638` (extracted to break the cycle
with `LaurentRefinement`).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Helpers -/

section Helpers

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- `D₀.canonicalMap D₀.s` is a unit in `presheafValue D₀`, because `D₀.s`
becomes a unit under `algebraMap A (Localization.Away D₀.s)` (definition of
localization) and `D₀.coeRingHom` preserves units. -/
theorem canonicalMap_s_isUnit (D₀ : RationalLocData A) :
    IsUnit (D₀.canonicalMap D₀.s) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map D₀.coeRingHom
    (IsLocalization.Away.algebraMap_isUnit D₀.s)

/-- Compatibility: `restrictionMapHom D₀ D' hsub ∘ D₀.canonicalMap = D'.canonicalMap`.
Follows directly from `UniformSpace.Completion.extensionHom_coe` + the
`IsLocalization.Away.lift_eq` identity for the underlying alg map. -/
theorem restrictionMapHom_canonicalMap (D₀ D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D₀.T D₀.s) (a : A) :
    restrictionMapHom D₀ D' h (D₀.canonicalMap a) = D'.canonicalMap a := by
  unfold restrictionMapHom RationalLocData.canonicalMap
  letI := D₀.uniformSpace
  letI := D₀.isTopologicalRing
  letI := D₀.isUniformAddGroup
  letI := D'.uniformSpace
  letI := D'.isTopologicalRing
  letI := D'.isUniformAddGroup
  simp only [RingHom.coe_comp, Function.comp_apply]
  erw [UniformSpace.Completion.extensionHom_coe (restrictionMapAlg D₀ D' h)
    (restrictionMapAlg_continuous D₀ D' h)]
  simp only [restrictionMapAlg, IsLocalization.Away.lift_eq]
  rfl

end Helpers

end ValuationSpectrum
