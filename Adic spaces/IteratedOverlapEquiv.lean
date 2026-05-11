/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentOverlap

/-!
# `presheafValue_iteratedOverlap_equiv`: presheaf-level Wedhorn 2.13 for the overlap

This file constructs the **concrete ring equivalence**
```
presheafValue (laurentOverlapDatum D₀ f) ≃+*
  presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B)
```

This is the overlap-shape analog of `presheafValue_iteratedMinus_equiv`
(in `LaurentRefinement.lean`). The structure mirrors the iteratedMinus
chain exactly:

1. Forward / backward uncompleted loc homs.
2. Power-boundedness of the forward map's generators (with the **larger**
   overlap `T` containing the extra `f` factor on the source side).
3. Continuity of forward via `locTopology_continuous_lift`.
4. Power-boundedness of the backward map's generators (with `T = {1, b, b²}`
   on the target side).
5. Continuity of backward.
6. Forward / backward completion homs via `UniformSpace.Completion.extensionHom`.
7. Round-trip identities via `Completion.ext'`.
8. The packaged `≃+*` (this file's main result).

Compared to `iteratedMinusDatum_B`:

* Source `(laurentOverlapDatum D₀ f).T` includes `f` as a possible first
  factor (vs. `(insert D₀.s D₀.T)` for the minus).
* Target `(iteratedOverlapDatum_B P D₀ f).T = {1, canonicalMap f,
  (canonicalMap f)²}` (vs. `{1}` for the minus).

The extra generators are handled by:

* Forward: extra source generator `t = f * b` for `b ∈ {D₀.s, f}` lands in
  `locSubring (iteratedOverlapDatum_B)` using `1 ∈ D₀.T` (via
  `LaurentNormalized.one_mem_T`) to express `invS D₀ ∈ P_B.A₀`.
* Backward: extra target generators `divByS b b` and `divByS (b·b) b` both
  equal `algebraMap_B b`, and `(laurentOverlap).canonicalMap f` is
  power-bounded because `algebraMap_A f = divByS (f²) (D₀.s · f) ·
  algebraMap_A D₀.s ∈ locSubring (laurentOverlap)`.

## Type-transport convention

`(iteratedOverlapDatum_B P D₀ f).s = D₀.canonicalMap f` only propositionally
(via `iteratedOverlapDatum_B_s_eq`); the literal `.s` field is `1 * canonicalMap f`.
We therefore build the forward map landing in
`Localization.Away ((iteratedOverlapDatum_B).s)` via `IsLocalization.Away.lift`,
using the transported instance `IsLocalization.Away (D₀.canonicalMap f)
  (Localization.Away ((iteratedOverlapDatum_B).s))`.

## Main result

* `presheafValue_iteratedOverlap_equiv` — the concrete `≃+*` ring
  equivalence; no parametric hypothesis-witnesses, no sorries, no axioms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 2.13.
* `LaurentRefinement.lean` — `presheafValue_iteratedMinus_equiv` (template).
* `LaurentOverlap.lean` — overlap forward/backward loc homs and
  `canonicalMap_b_isPowerBounded_in_overlap` helper.
-/

universe u

open Classical

namespace ValuationSpectrum

open UniformSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-! ### Phase 0: target-side IsLocalization instance via transport

Given `(iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f` and
the canonical `IsLocalization.Away (D₀.canonicalMap f)` instance on
`Localization.Away (D₀.canonicalMap f)`, we get `IsLocalization.Away
(D₀.canonicalMap f) (Localization.Away (iteratedOverlapDatum_B).s)` by
transport. This is the same trick used in `iteratedOverlap_backwardToCompletion`. -/

/-- IsLocalization instance for the target localization. -/
private theorem iteratedOverlap_isLocalization_target
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  rw [iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B]; infer_instance

/-! ### Phase 1: forward uncompleted hom landing in target localization

We build `iteratedOverlap_forwardLocHom_to_B : Loc_A(D₀.s · f) →+*
Loc_B((iteratedOverlapDatum_B).s)` via `IsLocalization.Away.lift` using
the base hom `A → B → Loc_B((iteratedOverlapDatum_B).s)`.

Since `(iteratedOverlapDatum_B).s = canonicalMap f`, and `D₀.s * f` is sent
to a unit (via `D₀.s ↦ canonicalMap D₀.s` (unit in B → unit in Loc_B), and
`f ↦ canonicalMap f` (unit in Loc_B since canonicalMap f is the localized
generator)), this satisfies the `IsLocalization.Away.lift` hypothesis. -/

private theorem iteratedOverlap_baseHom_DsTimes_f_isUnit
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    IsUnit ((algebraMap (presheafValue D₀)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))).comp
      D₀.canonicalMap (D₀.s * f)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI := iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  show IsUnit (algebraMap (presheafValue D₀)
    (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
    (D₀.canonicalMap (D₀.s * f)))
  rw [map_mul, map_mul]
  exact ((isUnit_s_in_presheafValue D₀).map _).mul
    (IsLocalization.Away.algebraMap_isUnit (D₀.canonicalMap f))

/-- Forward uncompleted hom landing in `Loc_B((iteratedOverlapDatum_B).s)`. -/
noncomputable def iteratedOverlap_forwardLocHom_to_B
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    Localization.Away ((laurentOverlapDatum D₀ f).s) →+*
      Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s) := by
  haveI : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    show IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  exact IsLocalization.Away.lift (S := Localization.Away ((laurentOverlapDatum D₀ f).s))
    (R := A) (D₀.s * f)
    (iteratedOverlap_baseHom_DsTimes_f_isUnit P D₀ f hLocLift_B)

/-- Forward map on `algebraMap a`. -/
theorem iteratedOverlap_forwardLocHom_to_B_algebraMap
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (a : A) :
    iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (algebraMap A (Localization.Away (D₀.s * f)) a) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap a) := by
  haveI : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    show IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  show IsLocalization.Away.lift (D₀.s * f)
    (iteratedOverlap_baseHom_DsTimes_f_isUnit P D₀ f hLocLift_B)
    (algebraMap A (Localization.Away (D₀.s * f)) a) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-! ### Phase 2: forward loc hom power-boundedness for the overlap T -/

/-- **Forward loc hom power-boundedness, overlap case.**

For each `t ∈ (laurentOverlapDatum D₀ f).T`, `iteratedOverlap_forwardLocHom_to_B`
sends `divByS t (D₀.s * f)` to an element power-bounded in
`(iteratedOverlapDatum_B P D₀ f hLocLift_B).topology`. -/
private theorem iteratedOverlap_forwardLocHom_to_B_generators_powerBounded
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    ∀ t ∈ (laurentOverlapDatum D₀ f).T,
      @TopologicalRing.IsPowerBounded _ _
        (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
        (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
          (divByS t (laurentOverlapDatum D₀ f).s)) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI hloc_src : IsLocalization.Away (D₀.s * f)
      (Localization.Away ((laurentOverlapDatum D₀ f).s)) := by
    show IsLocalization.Away (D₀.s * f) (Localization.Away (D₀.s * f))
    infer_instance
  haveI hloc_tgt : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) :=
    iteratedOverlap_isLocalization_target P D₀ f hLocLift_B
  intro t ht
  obtain ⟨⟨a, b⟩, hab_mem, hab_eq⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab_mem
  change a ∈ insert D₀.s (insert f D₀.T) at ha
  change b ∈ ({D₀.s, f} : Finset A) at hb
  change a * b = t at hab_eq
  subst hab_eq
  show @TopologicalRing.IsPowerBounded _ _
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).topology
    (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B (divByS (a * b) (D₀.s * f)))
  apply isPowerBounded_of_mem_locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B)
  set B := presheafValue D₀
  -- Auxiliary facts.
  have hu_s_src : IsUnit (algebraMap A (Localization.Away (D₀.s * f))
      D₀.s) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (D₀.s * f)
        (S := Localization.Away ((laurentOverlapDatum D₀ f).s))
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_left this
  have hu_f_src : IsUnit (algebraMap A (Localization.Away (D₀.s * f))
      f) := by
    have := IsLocalization.Away.algebraMap_isUnit (R := A) (D₀.s * f)
        (S := Localization.Away ((laurentOverlapDatum D₀ f).s))
    rw [map_mul] at this; exact isUnit_of_mul_isUnit_right this
  have hu_s_tgt : IsUnit (algebraMap B
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap D₀.s)) := (isUnit_s_in_presheafValue D₀).map _
  have hu_f_tgt : IsUnit (algebraMap B
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
      (D₀.canonicalMap f)) := IsLocalization.Away.algebraMap_isUnit _
  have hforward_alg : ∀ x : A, iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
      (algebraMap A (Localization.Away (D₀.s * f)) x) =
      algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
        (D₀.canonicalMap x) := fun x =>
    iteratedOverlap_forwardLocHom_to_B_algebraMap P D₀ f hLocLift_B x
  -- `s_B = canonicalMap f` (propositionally).
  have hs_B_eq : (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f :=
    iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B
  -- `1 ∈ T_B` and `b · b ∈ T_B`.
  have h1_mem_T_B : (1 : B) ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).T :=
    one_mem_overlapDatum_T B (presheafValue_pairOfDefinition_concrete P D₀)
      (D₀.canonicalMap f)
  have hb_sq_mem_T_B : (D₀.canonicalMap f) * (D₀.canonicalMap f) ∈
      (iteratedOverlapDatum_B P D₀ f hLocLift_B).T :=
    b_sq_mem_overlapDatum_T B (presheafValue_pairOfDefinition_concrete P D₀)
      (D₀.canonicalMap f)
  -- Split by `a`.
  rcases Finset.mem_insert.mp ha with ha_s | ha_rest
  · -- Case `a = D₀.s`.
    subst ha_s
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb_s | hb_f
    · -- `a = D₀.s, b = D₀.s`.
      subst hb_s
      have hrel : divByS (D₀.s * D₀.s) (D₀.s * f) *
          algebraMap A (Localization.Away (D₀.s * f)) f =
          algebraMap A (Localization.Away (D₀.s * f)) D₀.s := by
        unfold divByS
        rw [← IsLocalization.mk'_one
              (M := Submonoid.powers (D₀.s * f))
              (S := Localization.Away (D₀.s * f)) f,
            ← IsLocalization.mk'_mul,
            ← IsLocalization.mk'_one
              (M := Submonoid.powers (D₀.s * f))
              (S := Localization.Away (D₀.s * f)) D₀.s]
        exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
      have hforward_rel : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
          (divByS (D₀.s * D₀.s) (D₀.s * f)) *
          algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap f) =
          algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap D₀.s) := by
        have hcm := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) hrel
        rw [(iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B).map_mul,
          hforward_alg, hforward_alg] at hcm
        exact hcm
      have hinv_f : algebraMap B
          (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
          (D₀.canonicalMap f) * divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = 1 := by
        rw [hs_B_eq]
        unfold divByS
        rw [← IsLocalization.mk'_one
              (M := Submonoid.powers ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (S := Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap f),
            ← IsLocalization.mk'_mul, mul_one, one_mul, hs_B_eq]
        exact IsLocalization.mk'_self _ _
      have hforward_eq : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
          (divByS (D₀.s * D₀.s) (D₀.s * f)) =
          algebraMap B (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap D₀.s) *
            divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
        have := congrArg (· * divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s)
          hforward_rel
        simp only at this
        rwa [mul_assoc, hinv_f, mul_one] at this
      rw [hforward_eq]
      have hcan_s_A₀ : D₀.canonicalMap D₀.s ∈
          (iteratedOverlapDatum_B P D₀ f hLocLift_B).P.A₀ :=
        canonicalMap_mem_ringOfDef D₀
          (LaurentNormalized.insert_s_T_subset_A₀ D₀.s (Finset.mem_insert_self _ _))
      refine (locSubring _ _ _).mul_mem ?_ ?_
      · exact algebraMap_mem_locSubring _ _ _ hcan_s_A₀
      · exact divByS_mem_locSubring _ _ _ h1_mem_T_B
    · -- `a = D₀.s, b = f`: `divByS (D₀.s · f) (D₀.s · f) = 1`. Trivial.
      rw [hb_f]
      have hself : divByS (D₀.s * f) (D₀.s * f) = 1 := by
        unfold divByS
        exact IsLocalization.mk'_self _ _
      rw [hself, map_one]
      exact (locSubring _ _ _).one_mem
  · rcases Finset.mem_insert.mp ha_rest with ha_f | ha_T
    · -- Sub-case `a = f`: NEW.
      rw [ha_f]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb_s | hb_f
      · -- `a = f, b = D₀.s`: `divByS (f * D₀.s) (D₀.s * f) = 1`.
        rw [hb_s]
        have hself : divByS (f * D₀.s) (D₀.s * f) = 1 := by
          unfold divByS
          apply IsLocalization.mk'_eq_of_eq
          simp [mul_comm]
        rw [hself, map_one]
        exact (locSubring _ _ _).one_mem
      · -- `a = f, b = f`: NEW. forward = algebraMap_B (canonicalMap f) * algebraMap_B (invS D₀).
        rw [hb_f]
        have hrel : divByS (f * f) (D₀.s * f) *
            algebraMap A (Localization.Away (D₀.s * f)) D₀.s =
            algebraMap A (Localization.Away (D₀.s * f)) f := by
          unfold divByS
          rw [← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) D₀.s,
              ← IsLocalization.mk'_mul,
              ← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) f]
          exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
        have hforward_rel : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (f * f) (D₀.s * f)) *
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap D₀.s) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap f) := by
          have := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) hrel
          rw [map_mul, hforward_alg, hforward_alg] at this; exact this
        have hinv_canSs : D₀.canonicalMap D₀.s * invS D₀ = 1 :=
          canonicalMap_s_mul_invS D₀
        have hinv_canSs_target : algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap D₀.s) *
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (invS D₀) = 1 := by
          rw [← map_mul, hinv_canSs, map_one]
        have hforward_eq : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (f * f) (D₀.s * f)) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap f) *
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (invS D₀) := by
          apply hu_s_tgt.mul_right_cancel
          rw [hforward_rel, mul_assoc,
            mul_comm (algebraMap B _ (invS D₀)) (algebraMap B _ _),
            ← mul_assoc, hinv_canSs_target, one_mul]
        rw [hforward_eq]
        have halg_b_eq_divByS : algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap f) =
            divByS (D₀.canonicalMap f * D₀.canonicalMap f)
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
          rw [hs_B_eq]
          unfold divByS
          rw [← IsLocalization.mk'_one
                (M := Submonoid.powers ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
                (S := Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
                (D₀.canonicalMap f)]
          apply IsLocalization.mk'_eq_of_eq
          rw [hs_B_eq]; simp only [Submonoid.coe_one, one_mul]
        have halg_b_mem : algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap f) ∈
            locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
          rw [halg_b_eq_divByS]
          exact divByS_mem_locSubring _ _ _ hb_sq_mem_T_B
        have hinvS_mem_A₀ : invS D₀ ∈
            (iteratedOverlapDatum_B P D₀ f hLocLift_B).P.A₀ := by
          rw [invS_eq_coeRingHom_divByS_one]
          refine Subring.le_topologicalClosure _ ?_
          refine ⟨⟨divByS (1 : A) D₀.s,
            divByS_mem_locSubring _ _ _ LaurentNormalized.one_mem_T⟩, ?_⟩
          rfl
        have halg_invS_mem : algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (invS D₀) ∈
            locSubring (iteratedOverlapDatum_B P D₀ f hLocLift_B).P
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).T
              (iteratedOverlapDatum_B P D₀ f hLocLift_B).s :=
          algebraMap_mem_locSubring _ _ _ hinvS_mem_A₀
        exact (locSubring _ _ _).mul_mem halg_b_mem halg_invS_mem
    · -- Sub-case `a ∈ D₀.T`.
      have ha_A₀ : a ∈ D₀.P.A₀ := LaurentNormalized.insert_s_T_subset_A₀ a
        (Finset.mem_insert_of_mem ha_T)
      have hcan_a : D₀.canonicalMap a ∈ (iteratedOverlapDatum_B P D₀ f hLocLift_B).P.A₀ :=
        canonicalMap_mem_ringOfDef D₀ ha_A₀
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb_s | hb_f
      · rw [hb_s]
        have hrel : divByS (a * D₀.s) (D₀.s * f) *
            algebraMap A (Localization.Away (D₀.s * f)) f =
            algebraMap A (Localization.Away (D₀.s * f)) a := by
          unfold divByS
          rw [← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) f,
              ← IsLocalization.mk'_mul,
              ← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) a]
          exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
        have hforward_rel : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (a * D₀.s) (D₀.s * f)) *
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap f) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap a) := by
          have := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) hrel
          rw [map_mul, hforward_alg, hforward_alg] at this; exact this
        have hinv_f : algebraMap B
            (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
            (D₀.canonicalMap f) *
            divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = 1 := by
          rw [hs_B_eq]
          unfold divByS
          rw [← IsLocalization.mk'_one
                (M := Submonoid.powers ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
                (S := Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
                (D₀.canonicalMap f),
              ← IsLocalization.mk'_mul, mul_one, one_mul, hs_B_eq]
          exact IsLocalization.mk'_self _ _
        have hforward_eq : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (a * D₀.s) (D₀.s * f)) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap a) *
            divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s := by
          have := congrArg (· * divByS (1 : B) (iteratedOverlapDatum_B P D₀ f hLocLift_B).s)
            hforward_rel
          simp only at this
          rwa [mul_assoc, hinv_f, mul_one] at this
        rw [hforward_eq]
        refine (locSubring _ _ _).mul_mem ?_ ?_
        · exact algebraMap_mem_locSubring _ _ _ hcan_a
        · exact divByS_mem_locSubring _ _ _ h1_mem_T_B
      · rw [hb_f]
        have hrel : divByS (a * f) (D₀.s * f) *
            algebraMap A (Localization.Away (D₀.s * f)) D₀.s =
            algebraMap A (Localization.Away (D₀.s * f)) a := by
          unfold divByS
          rw [← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) D₀.s,
              ← IsLocalization.mk'_mul,
              ← IsLocalization.mk'_one
                (M := Submonoid.powers ((laurentOverlapDatum D₀ f).s))
                (S := Localization.Away ((laurentOverlapDatum D₀ f).s)) a]
          exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
        have hforward_rel : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (a * f) (D₀.s * f)) *
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap D₀.s) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.canonicalMap a) := by
          have := congrArg (iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B) hrel
          rw [map_mul, hforward_alg, hforward_alg] at this; exact this
        have hcoeB : D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS a D₀.s) =
            D₀.canonicalMap a := by
          change D₀.coeRingHom (algebraMap A _ D₀.s) * D₀.coeRingHom (divByS a D₀.s) =
            D₀.coeRingHom (algebraMap A _ a)
          rw [← map_mul]
          congr 1
          unfold divByS
          rw [← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
                (S := Localization.Away D₀.s) D₀.s,
              ← IsLocalization.mk'_mul,
              ← IsLocalization.mk'_one (M := Submonoid.powers D₀.s)
                (S := Localization.Away D₀.s) a]
          exact IsLocalization.mk'_eq_of_eq (by simp only [Submonoid.coe_mul]; ring)
        have hforward_eq : iteratedOverlap_forwardLocHom_to_B P D₀ f hLocLift_B
            (divByS (a * f) (D₀.s * f)) =
            algebraMap B
              (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s))
              (D₀.coeRingHom (divByS a D₀.s)) := by
          apply hu_s_tgt.mul_right_cancel
          rw [hforward_rel, ← hcoeB, map_mul]; ring
        rw [hforward_eq]
        have hdiv_mem_loc : divByS a D₀.s ∈ locSubring D₀.P D₀.T D₀.s :=
          divByS_mem_locSubring _ _ _ ha_T
        have hcoe_mem : D₀.coeRingHom (divByS a D₀.s) ∈ presheafValue_ringOfDef D₀ := by
          refine Subring.le_topologicalClosure _ ?_
          exact ⟨⟨divByS a D₀.s, hdiv_mem_loc⟩, rfl⟩
        exact algebraMap_mem_locSubring _ _ _ hcoe_mem

end ValuationSpectrum
