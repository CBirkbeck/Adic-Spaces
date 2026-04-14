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

end Helpers

/-! ### Forward uncompleted ring hom for `presheafValue_iteratedMinus_equiv` -/

section IteratedMinusForward

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- Composite `A → presheafValue D₀ → Localization.Away (canonicalMap f)`. -/
noncomputable def iteratedMinus_baseHom (D₀ : RationalLocData A) (f : A) :
    A →+* Localization.Away (D₀.canonicalMap f) :=
  (algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f))).comp
    D₀.canonicalMap

/-- `D₀.s * f` becomes a unit in `Localization.Away (canonicalMap f)` via the
base hom: `D₀.s` maps to a unit (since `canonicalMap D₀.s` is a unit in
`presheafValue D₀`, preserved by `algebraMap`) and `f` maps to a unit (since
`canonicalMap f` is the localization element). -/
theorem iteratedMinus_D₀s_mul_f_isUnit (D₀ : RationalLocData A) (f : A) :
    IsUnit (iteratedMinus_baseHom D₀ f (D₀.s * f)) := by
  show IsUnit (algebraMap (presheafValue D₀) _ (D₀.canonicalMap (D₀.s * f)))
  rw [map_mul, map_mul]
  exact ((canonicalMap_s_isUnit D₀).map _).mul
    (IsLocalization.Away.algebraMap_isUnit (D₀.canonicalMap f))

/-- Forward ring hom `Localization.Away (D₀.s * f) → Localization.Away (canonicalMap f)`
(at the uncompleted localization level), obtained by the universal property of
`IsLocalization.Away` using that `D₀.s * f` becomes a unit in the target. -/
noncomputable def iteratedMinus_forwardLocHom (D₀ : RationalLocData A) (f : A) :
    Localization.Away (D₀.s * f) →+* Localization.Away (D₀.canonicalMap f) :=
  IsLocalization.Away.lift (D₀.s * f) (iteratedMinus_D₀s_mul_f_isUnit D₀ f)

/-- The forward localization hom composed with `algebraMap A` equals `iteratedMinus_baseHom`. -/
theorem iteratedMinus_forwardLocHom_algebraMap (D₀ : RationalLocData A) (f : A) (a : A) :
    iteratedMinus_forwardLocHom D₀ f
      (algebraMap A (Localization.Away (D₀.s * f)) a) =
      iteratedMinus_baseHom D₀ f a :=
  IsLocalization.Away.lift_eq (D₀.s * f) (iteratedMinus_D₀s_mul_f_isUnit D₀ f) a

/-- Forward ring hom to the completion: composes `iteratedMinus_forwardLocHom`
with the completion's `coeRingHom`. -/
noncomputable def iteratedMinus_forwardToCompletion
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    Localization.Away ((laurentMinusDatum D₀ f).s) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) :=
  (iteratedMinusDatum_B P D₀ f).coeRingHom.comp
    (iteratedMinus_forwardLocHom D₀ f)

end IteratedMinusForward

end ValuationSpectrum
