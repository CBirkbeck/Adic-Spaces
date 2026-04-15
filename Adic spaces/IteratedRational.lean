/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement
import «Adic spaces».PresheafTateStructure
import «Adic spaces».TopologyComparison
import «Adic spaces».CompletionLocalization

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

/-- Continuity of `iteratedMinus_forwardToCompletion` wrt the laurentMinus
topology on the source and the completion uniformity on the target.

**Obstacle encountered (2026-04-15):** the natural proof path uses
`IsLocalization.Away.lift` continuity, which in turn requires
`HasLocLiftPowerBounded (presheafValue D₀)` at `B`. The existing
`HasLocLiftPowerBounded.tate` instance in
`PresheafIdentification.lean:1165` is gated by `[IsDomain A]` —
`presheafValue D₀` is not generally a domain, so this instance does
not fire.

**Recommended route (per reviewer 2026-04-15):** reroute through the
generic Example 6.38 primitive (R3 in the revised plan). This builds
the forward map `TateAlgebra B →+* presheafValue(iteratedMinusDatum_B)`
by evaluation at `canonicalMap f`, whose continuity uses Tate-algebra
machinery and avoids the locLift route entirely. Once R3 is in place,
this continuity sorry is discharged via composition with the generic
Example 6.38 bridge. -/
theorem iteratedMinus_forwardToCompletion_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    @Continuous _ _ (laurentMinusDatum D₀ f).topology _
      (iteratedMinus_forwardToCompletion P D₀ f) := by
  sorry

/-- Forward RingHom between the two completions — extension via
`UniformSpace.Completion.extensionHom`. -/
noncomputable def iteratedMinus_forwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A) :
    presheafValue (laurentMinusDatum D₀ f) →+*
      presheafValue (iteratedMinusDatum_B P D₀ f) := by
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom
    (iteratedMinus_forwardToCompletion P D₀ f)
    (iteratedMinus_forwardToCompletion_continuous P D₀ f)

end IteratedMinusForward

/-! ### Backward uncompleted ring hom for `presheafValue_iteratedMinus_equiv`

The backward direction goes from `presheafValue (iteratedMinusDatum_B P D₀ f)`
(completion of `Loc_B(canonicalMap f)`) back to `presheafValue (laurentMinusDatum D₀ f)`.

Key observation: in `presheafValue (laurentMinusDatum D₀ f)`, the element
`D₀.s · f` is a unit (localization), hence `f` is a unit too (since `D₀.s`
is a unit — follows from it being in the ring and the product being a unit).
So `canonicalMap f` becomes a unit in the LHS completion, and by the universal
property of `Localization.Away (canonicalMap f)`, we get a RingHom back. -/

section IteratedMinusBackward

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- In `Localization.Away (D₀.s * f)`, the element `algebraMap f` is a unit
(because `D₀.s * f` is a unit and `D₀.s` is also a unit, by the factorisation
argument using `isUnit_of_mul_isUnit_right`). -/
theorem algebraMap_f_isUnit_in_laurentMinus (D₀ : RationalLocData A) (f : A) :
    IsUnit (algebraMap A (Localization.Away (D₀.s * f)) f) := by
  have hmul : algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f) =
      algebraMap A _ D₀.s * algebraMap A _ f := map_mul _ _ _
  have hu : IsUnit (algebraMap A (Localization.Away (D₀.s * f)) (D₀.s * f)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [hmul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- In `presheafValue (laurentMinusDatum D₀ f)`, the canonical image of `f`
is a unit. This uses that `f` is already a unit in `Localization.Away (D₀.s · f)`
and `coeRingHom` preserves units. -/
theorem canonicalMap_f_isUnit_in_laurentMinus (D₀ : RationalLocData A) (f : A) :
    IsUnit ((laurentMinusDatum D₀ f).canonicalMap f) := by
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map _ (algebraMap_f_isUnit_in_laurentMinus D₀ f)

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

/-- In `presheafValue (laurentMinusDatum D₀ f)`, the image of `D₀.canonicalMap f`
under the restriction map equals `(laurentMinusDatum D₀ f).canonicalMap f`, which
is a unit. -/
theorem restrictionMap_canonicalMap_f_isUnit
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    IsUnit (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub (D₀.canonicalMap f)) := by
  rw [restrictionMapHom_canonicalMap]
  exact canonicalMap_f_isUnit_in_laurentMinus D₀ f

/-- Backward ring hom at the uncompleted B-localization level:
`Localization.Away (canonicalMap f) →+* presheafValue (laurentMinusDatum D₀ f)`,
obtained by applying `IsLocalization.Away.lift` to the composite
`B → presheafValue (laurentMinusDatum D₀ f)` (via `restrictionMapHom`) after
establishing that it sends `canonicalMap f` to a unit. -/
noncomputable def iteratedMinus_backwardLocHom
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Localization.Away (D₀.canonicalMap f) →+*
      presheafValue (laurentMinusDatum D₀ f) :=
  IsLocalization.Away.lift (S := Localization.Away (D₀.canonicalMap f))
    (R := presheafValue D₀) (D₀.canonicalMap f)
    (g := restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub)
    (restrictionMap_canonicalMap_f_isUnit D₀ f hsub)

/-- The backward loc hom composed with `algebraMap B` equals `restrictionMapHom`. -/
theorem iteratedMinus_backwardLocHom_algebraMap
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : presheafValue D₀) :
    iteratedMinus_backwardLocHom D₀ f hsub
      (algebraMap (presheafValue D₀) (Localization.Away (D₀.canonicalMap f)) b) =
      restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub b :=
  IsLocalization.Away.lift_eq (D₀.canonicalMap f)
    (restrictionMap_canonicalMap_f_isUnit D₀ f hsub) b

/-- Continuity of the backward loc hom.

**Obstacle encountered (2026-04-15):** same shape as the forward continuity.
The natural proof uses `IsLocalization.Away.lift` continuity for a lift
whose "locLift" property requires `HasLocLiftPowerBounded` at B. The
existing instance is gated by `[IsDomain]`, which fails at
`B = presheafValue D₀`.

**Recommended route (per reviewer 2026-04-15):** reroute through the
generic Example 6.38 minus-branch primitive (R3). The backward map
`TateAlgebra B →+* presheafValue(laurentMinusDatum D₀ f)` is built by
evaluation at `canonicalMap f / 1` (i.e., `1 / canonicalMap f` in the
localization), whose continuity is standard for Tate algebras. -/
theorem iteratedMinus_backwardLocHom_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    @Continuous _ _ (iteratedMinusDatum_B P D₀ f).topology _
      (iteratedMinus_backwardLocHom D₀ f hsub) := by
  sorry

/-- Backward RingHom between the two completions, via
`UniformSpace.Completion.extensionHom`. -/
noncomputable def iteratedMinus_backwardHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    presheafValue (iteratedMinusDatum_B P D₀ f) →+*
      presheafValue (laurentMinusDatum D₀ f) := by
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  exact UniformSpace.Completion.extensionHom
    (iteratedMinus_backwardLocHom D₀ f hsub)
    (iteratedMinus_backwardLocHom_continuous P D₀ f hsub)

end IteratedMinusBackward

/-! ### Round trip and final assembly for `presheafValue_iteratedMinus_equiv` -/

section IteratedMinusEquiv

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- The composite `backwardLocHom ∘ forwardLocHom` at the algebraic level equals
`(laurentMinusDatum D₀ f).coeRingHom` (both Loc_A(D₀.s·f) → presheafValue(laurentMinus)
ring homs agreeing on algebraMap via `restrictionMapHom_canonicalMap`). -/
private theorem backward_forward_locHom_comp_eq_coeRingHom
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    ((iteratedMinus_backwardLocHom D₀ f hsub).comp
      (iteratedMinus_forwardLocHom D₀ f)) =
    (laurentMinusDatum D₀ f).coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (D₀.s * f))
  ext a
  show iteratedMinus_backwardLocHom D₀ f hsub
    (iteratedMinus_forwardLocHom D₀ f
      (algebraMap A (Localization.Away (D₀.s * f)) a)) =
      (laurentMinusDatum D₀ f).coeRingHom (algebraMap A _ a)
  rw [iteratedMinus_forwardLocHom_algebraMap,
      iteratedMinus_baseHom, RingHom.comp_apply,
      iteratedMinus_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap]
  rfl

/-- `iteratedMinus_backwardHom ∘ iteratedMinus_forwardHom = id`.
Proved by the Completion.ext' pattern: both continuous ring homs agree on
the dense `coeRingHom` image, where the check reduces to the uncompleted-level
identity `backward_forward_locHom_comp_eq_coeRingHom`. -/
theorem iteratedMinus_backward_forward_eq_id
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_backwardHom P D₀ f hsub).comp
      (iteratedMinus_forwardHom P D₀ f) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  apply RingHom.ext
  intro x
  show iteratedMinus_backwardHom P D₀ f hsub
    (iteratedMinus_forwardHom P D₀ f x) = x
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  show iteratedMinus_backwardHom P D₀ f hsub
    (iteratedMinus_forwardHom P D₀ f
      (UniformSpace.Completion.coeRingHom a)) = UniformSpace.Completion.coeRingHom a
  have hfwd : iteratedMinus_forwardHom P D₀ f
      (UniformSpace.Completion.coeRingHom a) =
      iteratedMinus_forwardToCompletion P D₀ f a :=
    UniformSpace.Completion.extensionHom_coe _ _ a
  rw [hfwd]
  show iteratedMinus_backwardHom P D₀ f hsub
    ((iteratedMinusDatum_B P D₀ f).coeRingHom
      (iteratedMinus_forwardLocHom D₀ f a)) = _
  have hbwd : iteratedMinus_backwardHom P D₀ f hsub
      ((iteratedMinusDatum_B P D₀ f).coeRingHom
        (iteratedMinus_forwardLocHom D₀ f a)) =
      iteratedMinus_backwardLocHom D₀ f hsub
        (iteratedMinus_forwardLocHom D₀ f a) :=
    UniformSpace.Completion.extensionHom_coe _ _ _
  rw [hbwd]
  have h := backward_forward_locHom_comp_eq_coeRingHom D₀ f hsub
  have := congr_fun (congrArg DFunLike.coe h) a
  simp only [RingHom.comp_apply] at this
  exact this

/-- RingHom equality at the completion level:
`forward ∘ restrictionMapHom = coeRingHom_B ∘ algebraMap_B`
as maps `presheafValue D₀ →+* presheafValue (iteratedMinusDatum_B)`.

Proved by `Completion.ext'` on the source: both sides continuous, and they
agree on the dense image of `D₀.coeRingHom` (checked via
`IsLocalization.ringHom_ext` against `algebraMap A` generators, where the
computation reduces to `restrictionMapHom_canonicalMap` + `forwardHom`'s
extension behaviour). -/
private theorem forward_comp_restrictionMapHom_eq
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_forwardHom P D₀ f).comp
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom.comp
      (algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedMinusDatum_B P D₀ f).s))) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  -- Both sides are continuous ring homs `presheafValue D₀ →+* presheafValue(iteratedMinusDatum_B)`.
  -- Reduce to checking on `D₀.coeRingHom c` (dense in source).
  apply RingHom.ext
  intro x
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub x) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom
      (algebraMap (presheafValue D₀) _ x)
  -- Establish continuity of LHS and RHS separately.
  have hLHS_cont : Continuous (fun y : presheafValue D₀ =>
      iteratedMinus_forwardHom P D₀ f
        (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub y)) :=
    (UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension
  have hRHS_cont : Continuous (fun y : presheafValue D₀ =>
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (algebraMap (presheafValue D₀) _ y)) :=
    canonicalMap_continuous (iteratedMinusDatum_B P D₀ f)
  refine UniformSpace.Completion.ext' hLHS_cont hRHS_cont ?_ x
  -- Agreement on the dense D₀.coeRingHom image:
  -- show for all c : Loc_A(D₀.s), both sides at D₀.coeRingHom c coincide.
  intro c
  -- Reduce to a RingHom equality Loc_A(D₀.s) →+* presheafValue(iteratedMinusDatum_B).
  -- Both composites: LHS = forward ∘ restrictionMapHom ∘ D₀.coeRingHom
  --                 RHS = coeRingHom_B ∘ algebraMap_B ∘ D₀.coeRingHom
  -- By IsLocalization.ringHom_ext, check on algebraMap A.
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub (D₀.coeRingHom c)) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom
      (algebraMap (presheafValue D₀) _ (D₀.coeRingHom c))
  -- Use IsLocalization.ringHom_ext on Loc_A(D₀.s).
  revert c
  suffices h :
      ((iteratedMinus_forwardHom P D₀ f).comp
        ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).comp D₀.coeRingHom)) =
      ((iteratedMinusDatum_B P D₀ f).coeRingHom.comp
        ((algebraMap (presheafValue D₀) _).comp D₀.coeRingHom)) by
    intro c
    exact congr_fun (congrArg DFunLike.coe h) c
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext a
  -- LHS: forward (restrictionMapHom (D₀.coeRingHom (algebraMap A a)))
  --    = forward (restrictionMapHom (D₀.canonicalMap a))   [def of canonicalMap]
  --    = forward ((laurentMinusDatum D₀ f).canonicalMap a) [restrictionMapHom_canonicalMap]
  --    = forward ((laurentMinusDatum D₀ f).coeRingHom (algebraMap A a))
  --    = forwardToCompletion (algebraMap A a)               [extensionHom_coe]
  --    = coeRingHom_B (forwardLocHom (algebraMap A a))      [def]
  --    = coeRingHom_B (iteratedMinus_baseHom a)             [forwardLocHom_algebraMap]
  --    = coeRingHom_B (algebraMap_B (D₀.canonicalMap a))    [def of baseHom]
  -- RHS: coeRingHom_B (algebraMap_B (D₀.coeRingHom (algebraMap A a)))
  --    = coeRingHom_B (algebraMap_B (D₀.canonicalMap a))
  show iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub
        (D₀.coeRingHom (algebraMap A _ a))) =
    (iteratedMinusDatum_B P D₀ f).coeRingHom
      (algebraMap (presheafValue D₀) _ (D₀.coeRingHom (algebraMap A _ a)))
  have hD₀can : D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a) =
      D₀.canonicalMap a := rfl
  rw [hD₀can]
  rw [restrictionMapHom_canonicalMap]
  have hlmcan : (laurentMinusDatum D₀ f).canonicalMap a =
      (laurentMinusDatum D₀ f).coeRingHom
        (algebraMap A (Localization.Away (laurentMinusDatum D₀ f).s) a) := rfl
  rw [hlmcan]
  have hfwd : iteratedMinus_forwardHom P D₀ f
      ((laurentMinusDatum D₀ f).coeRingHom
        (algebraMap A _ a)) =
      iteratedMinus_forwardToCompletion P D₀ f
        (algebraMap A _ a) :=
    UniformSpace.Completion.extensionHom_coe _ _ _
  rw [hfwd]
  show (iteratedMinusDatum_B P D₀ f).coeRingHom
      (iteratedMinus_forwardLocHom D₀ f (algebraMap A _ a)) = _
  rw [iteratedMinus_forwardLocHom_algebraMap]
  rfl

/-- Consequence of `forward_comp_restrictionMapHom_eq`, specialised at a point. -/
private theorem forward_backward_on_coeRingHom_B_algebraMap
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : presheafValue D₀) :
    iteratedMinus_forwardHom P D₀ f
      (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub b) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom
        (algebraMap (presheafValue D₀)
          (Localization.Away ((iteratedMinusDatum_B P D₀ f).s)) b) := by
  have h := forward_comp_restrictionMapHom_eq P D₀ f hsub
  have := congr_fun (congrArg DFunLike.coe h) b
  simp only [RingHom.comp_apply] at this
  exact this

/-- Symmetric: `iteratedMinus_forwardHom ∘ iteratedMinus_backwardHom = id`.

Uses Completion.ext' on the source `presheafValue (iteratedMinusDatum_B)` to reduce
to `coeRingHom_B` dense image. On `coeRingHom_B b` for `b : Loc_B(canonicalMap f)`:
- `backward (coeRingHom_B b) = backwardLocHom b` via extensionHom_coe;
- `forward (backwardLocHom b) = coeRingHom_B b` — this is the uncompleted-level
  identity (reduces to `forward_backward_on_coeRingHom_B_algebraMap` via
  `IsLocalization.ringHom_ext`). -/
theorem iteratedMinus_forward_backward_eq_id
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedMinus_forwardHom P D₀ f).comp
      (iteratedMinus_backwardHom P D₀ f hsub) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (iteratedMinusDatum_B P D₀ f).s) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (D₀.canonicalMap f)) :=
    (iteratedMinusDatum_B P D₀ f).isTopologicalRing
  letI : UniformSpace (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (laurentMinusDatum D₀ f).s) :=
    (laurentMinusDatum D₀ f).isTopologicalRing
  apply RingHom.ext
  intro y
  show iteratedMinus_forwardHom P D₀ f
    (iteratedMinus_backwardHom P D₀ f hsub y) = y
  refine @UniformSpace.Completion.ext' _ _ _ _ _ _ _
    ((UniformSpace.Completion.continuous_extension).comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro b
  show iteratedMinus_forwardHom P D₀ f
    (iteratedMinus_backwardHom P D₀ f hsub
      (UniformSpace.Completion.coeRingHom b)) =
      UniformSpace.Completion.coeRingHom b
  have hbwd : iteratedMinus_backwardHom P D₀ f hsub
      (UniformSpace.Completion.coeRingHom b) =
      iteratedMinus_backwardLocHom D₀ f hsub b :=
    UniformSpace.Completion.extensionHom_coe _ _ b
  rw [hbwd]
  -- Now prove: forwardHom (backwardLocHom b) = coeRingHom b.
  -- This is the composite (forwardHom ∘ backwardLocHom) b = coeRingHom b,
  -- which equals the RingHom equality between two maps Loc_B(canonicalMap f) →
  -- presheafValue (iteratedMinusDatum_B P D₀ f).
  have hringHom : (iteratedMinus_forwardHom P D₀ f).comp
      (iteratedMinus_backwardLocHom D₀ f hsub) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (D₀.canonicalMap f))
    ext b'
    show iteratedMinus_forwardHom P D₀ f
      (iteratedMinus_backwardLocHom D₀ f hsub
        (algebraMap _ _ b')) =
      (iteratedMinusDatum_B P D₀ f).coeRingHom (algebraMap _ _ b')
    rw [iteratedMinus_backwardLocHom_algebraMap]
    exact forward_backward_on_coeRingHom_B_algebraMap P D₀ f hsub b'
  have hb_apply := congr_fun (congrArg DFunLike.coe hringHom) b
  simp only [RingHom.comp_apply] at hb_apply
  exact hb_apply

/-- **Iterated rational identification, minus branch** (Wedhorn Lemma 2.13):
assembles the forward/backward homs into a `RingEquiv`.

Requires a subset hypothesis `hsub` witnessing that the minus piece is inside
the base rational open — this is provided by `laurentMinus_subset` in callsites. -/
noncomputable def presheafValue_iteratedMinus_equiv_aux
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    presheafValue (laurentMinusDatum D₀ f) ≃+*
      presheafValue (iteratedMinusDatum_B P D₀ f) where
  toFun := iteratedMinus_forwardHom P D₀ f
  invFun := iteratedMinus_backwardHom P D₀ f hsub
  left_inv x :=
    congr_fun (congrArg DFunLike.coe
      (iteratedMinus_backward_forward_eq_id P D₀ f hsub)) x
  right_inv y :=
    congr_fun (congrArg DFunLike.coe
      (iteratedMinus_forward_backward_eq_id P D₀ f hsub)) y
  map_mul' := map_mul _
  map_add' := map_add _

end IteratedMinusEquiv

/-! ## R3 — Generic Wedhorn Example 6.38 primitives

Per the reviewer's 2026-04-15 guidance, the load-bearing primitive for closing
the Laurent-branch bridges is Wedhorn Example 6.38 generically: for any
complete strongly noetherian Tate base `B` and any `b ∈ B` power-bounded in
the relevant branch, the Tate-algebra quotient identifies with the
presheafValue of a trivial rational datum on `B`.

This avoids the `HasLocLiftPowerBounded [IsDomain]`-gated route entirely:
the forward map is built from `TateAlgebra B` via evaluation at `b`
(plus) or `1/b` (minus), which is the standard `evalHomBounded`
construction — not the `IsLocalization.Away.lift` route.

### Plus branch: `B⟨X⟩ / (algebraMap b − X) ≃+* presheafValue (trivialPlusDatum P b)`

### Minus branch: `B⟨X⟩ / (1 − algebraMap b · X) ≃+* presheafValue (trivialMinusDatum P b)`
-/

section Example638

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]

/-- Generic trivial plus datum on `B` at `b`: `T = {b}`, `s = 1`.
`hopen` is trivial via `hopen_away_one` (no constraint on `b`, since the ring of
definition already contains `b` when we add it to `T`, in the localization at 1). -/
noncomputable def trivialPlusDatum (P : PairOfDefinition B) (b : B) :
    RationalLocData B where
  P := P
  T := {b}
  s := 1
  hopen := hopen_away_one P {b}

/-- Generic trivial minus datum on `B` at `b`: `T = {1}`, `s = b`.
`hopen` with `N = 0`: for any `c : P.A₀`, `divByS c.val b` factors as
`algebraMap c.val * divByS 1 b`, both in the `locSubring`. -/
noncomputable def trivialMinusDatum (P : PairOfDefinition B) (b : B) :
    RationalLocData B where
  P := P
  T := {1}
  s := b
  hopen := ⟨0, fun c _ => by
    have hmul : algebraMap B (Localization.Away b) c.val *
        divByS (1 : B) b = divByS c.val b := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers b)
            (S := Localization.Away b) c.val,
          ← IsLocalization.mk'_mul, one_mul, mul_one]
    rw [← hmul]
    exact (locSubring _ _ _).mul_mem
      (algebraMap_mem_locSubring _ _ _ c.2)
      (divByS_mem_locSubring _ _ _ (Finset.mem_singleton_self 1))⟩

/-! ### Plus branch forward: evaluation at `canonicalMap b` -/

section Example638PlusForward

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- `canonicalMap b` is power-bounded in `presheafValue (trivialPlusDatum P b)`.

Parallels `invS_isPowerBounded_of_one_mem_T` in `CompletionLocalization.lean`:
`divByS b 1 = algebraMap B _ b` lies in `locSubring P {b} 1` (since `b ∈ T`),
its powers stay in `locSubring`, and `coeRingHom_image_locSubring_isBounded`
gives boundedness of the image in the completion. -/
theorem canonicalMap_b_isPowerBounded_in_trivialPlus
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    TopologicalRing.IsPowerBounded
      ((trivialPlusDatum B P b).canonicalMap b) := by
  set D := trivialPlusDatum B P b
  -- `D.canonicalMap b = D.coeRingHom (algebraMap B (Localization.Away 1) b)`.
  have hcm : D.canonicalMap b =
      D.coeRingHom (algebraMap B (Localization.Away D.s) b) := rfl
  rw [hcm]
  -- Show `algebraMap b = divByS b 1` lies in `locSubring P {b} 1`.
  have halg_eq : algebraMap B (Localization.Away D.s) b = divByS b D.s := by
    show algebraMap B (Localization.Away (1 : B)) b = divByS b 1
    rw [divByS_eq_algebraMap]
  rw [halg_eq]
  -- `divByS b D.s ∈ locSubring D.P D.T D.s` since `b ∈ D.T = {b}`.
  have hmem : divByS b D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (Finset.mem_singleton_self b)
  -- Powers of `divByS b D.s` all lie in `locSubring`.
  have hpow : ∀ n : ℕ, (divByS b D.s) ^ n ∈ locSubring D.P D.T D.s :=
    fun n => (locSubring D.P D.T D.s).pow_mem hmem n
  -- The range of `(D.coeRingHom (divByS b D.s))^·` lies in
  -- `D.coeRingHom '' locSubring`, which is bounded.
  have hrange : Set.range
      ((D.coeRingHom (divByS b D.s)) ^ · : ℕ → presheafValue D) ⊆
      D.coeRingHom '' (locSubring D.P D.T D.s : Set (Localization.Away D.s)) := by
    rintro _ ⟨n, rfl⟩
    change (D.coeRingHom (divByS b D.s)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(divByS b D.s) ^ n, hpow n, rfl⟩
  exact (CompletionLocalization.coeRingHom_image_locSubring_isBounded D).subset hrange

/-- The generic evaluation hom `TateAlgebra B →+* presheafValue (trivialPlusDatum P b)`
sending `X ↦ canonicalMap b`, via `evalHomBounded`. -/
noncomputable def example638Plus_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) →+* presheafValue (trivialPlusDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded
    (trivialPlusDatum B P b).canonicalMap
    (canonicalMap_continuous (trivialPlusDatum B P b))
    ((trivialPlusDatum B P b).canonicalMap b)
    (canonicalMap_b_isPowerBounded_in_trivialPlus B P b)

/-- `example638Plus_evalHom` sends `algebraMap(a)` to `canonicalMap(a)`. -/
theorem example638Plus_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Plus_evalHom B P b (algebraMap B _ a) =
      (trivialPlusDatum B P b).canonicalMap a := by
  unfold example638Plus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 0]
  · unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    simp only [Finsupp.single_zero, pow_zero, mul_one]
    congr 1
  · intro n hn
    unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    have : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (↑(algebraMap B ↥(TateAlgebra B) a) : MvPowerSeries (Fin 1) B) = 0 := by
      change (MvPowerSeries.coeff (Finsupp.single 0 n))
        (MvPowerSeries.C (σ := Fin 1) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (Finsupp.single_ne_zero.mpr hn)]
    simp [this]

/-- `example638Plus_evalHom` sends `X` to `canonicalMap b`. -/
theorem example638Plus_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Plus_evalHom B P b TateAlgebra.X =
      (trivialPlusDatum B P b).canonicalMap b := by
  unfold example638Plus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    change (trivialPlusDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 1))
        (MvPowerSeries.X 0)) *
      (trivialPlusDatum B P b).canonicalMap b =
      (trivialPlusDatum B P b).canonicalMap b
    rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    change (trivialPlusDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (0 : Fin 1))) *
      (trivialPlusDatum B P b).canonicalMap b ^ n = 0
    classical
    have hcoeff : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (σ := Fin 1) 0) = 0 := by
      rw [MvPowerSeries.coeff_X]
      apply if_neg
      intro heq
      apply hn
      have : (Finsupp.single 0 n : Fin 1 →₀ ℕ) 0 =
        (Finsupp.single 0 1 : Fin 1 →₀ ℕ) 0 := by rw [heq]
      simpa using this
    simp [hcoeff]

/-- The ideal `(algebraMap b - X)` maps to zero under `example638Plus_evalHom`,
since the eval sends `algebraMap b ↦ canonicalMap b` and `X ↦ canonicalMap b`. -/
theorem example638Plus_evalHom_fSubX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Plus_evalHom B P b
      (algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X) = 0 := by
  rw [map_sub, example638Plus_evalHom_algebraMap, example638Plus_evalHom_X, sub_self]

/-- Forward ring hom `TateAlgebra B ⧸ (algebraMap b − X) → presheafValue (trivialPlusDatum P b)`,
obtained by factoring `example638Plus_evalHom` through the quotient. -/
noncomputable def example638Plus_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) ⧸
      Ideal.span {algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X} →+*
        presheafValue (trivialPlusDatum B P b) :=
  Ideal.Quotient.lift _ (example638Plus_evalHom B P b) (fun y hy => by
    rw [Ideal.mem_span_singleton'] at hy
    obtain ⟨c, hc⟩ := hy
    rw [← hc, map_mul, example638Plus_evalHom_fSubX_eq_zero, mul_zero])

end Example638PlusForward

end Example638

end ValuationSpectrum
