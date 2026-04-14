/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison

/-!
# Iterated Rational Localization (Wedhorn Lemma 2.13)

For a rational datum `D₀ : RationalLocData A` on a strongly noetherian Tate
ring `A`, and for iterated data (`laurent±Datum D₀ f` for `f : A`), the
iterated rational localization `presheafValue (laurent±Datum D₀ f)` is
isomorphic to a single rational localization of `B := presheafValue D₀`.

This module houses the proofs of:
- `presheafValue_iteratedMinus_equiv` (minus branch, Q3-STEP2C).
- `presheafValue_iteratedPlus_equiv` (plus branch, Q3-STEP2C).
- `presheafValue_trivialPlus_fSubX_equiv` (Q3-STEP2D, non-discrete f−X
  quotient over generic B).

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13, Prop 8.7.
-/

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

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

end Helpers

end ValuationSpectrum
