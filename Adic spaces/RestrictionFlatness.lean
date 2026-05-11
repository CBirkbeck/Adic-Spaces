/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».LaurentRefinement
import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness of the restriction map via Wedhorn Prop 8.30 + Wedhorn Lemma 2.13

## Reframe (MAJOR CORRECTION, ChatGPT Pro 2026-05-11 session 2)

The previous `restrictionMap_isLocalization` target (Wedhorn 8.15 as
`IsLocalization.Away`) is mathematically FALSE — completed rational
localizations contain infinite convergent denominator tails that no finite
power `s^N` can clear (counterexample: `A = ℚ_p⟨X⟩`,
`A⟨T⟩/(XT-1) ∋ ∑_{n≥0} p^n X^{-n}`).

The FIX: deliver `Module.Flat` for the restriction map DIRECTLY via the
B-level Wedhorn Prop 8.30 (Tate-algebra quotient identification at
`B := presheafValue D₀`), then transfer along the Wedhorn Lemma 2.13
identification `presheafValue (laurentMinusDatum D₀ f) ≃+*
presheafValue (iteratedMinusDatum_B P D₀ f)` (the
`presheafValue_iteratedMinus_equiv` of `LaurentRefinement.lean`, sorry-free).

## Main results

* `restrictionMap_flat_via_iteratedMinus` — for `D = laurentMinusDatum D₀ f`,
  `presheafValue D` is flat as a `presheafValue D₀`-module along the
  restriction map. Discharged by:
  1. B-level flatness `Module.Flat (presheafValue D₀)
     (presheafValue (iteratedMinusDatum_B P D₀ f))` via
     `presheafValue_flat_of_canonical` (with `T = {1}` collapsing `hT_pb`,
     `hb` via `invS_isPowerBounded_of_one_mem_T`).
  2. Transfer of flatness along `presheafValue_iteratedMinus_equiv` using
     `Module.Flat.of_linearEquiv` and the compatibility lemma
     `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Lemma 2.13.
* `docs/STATUS.md` — Reframe of T-FLAT-VIA-WEDHORN830.
* `Adic spaces/StructureSheaf.lean` — template `presheafValue_flat_of_tateQuotient`.
-/

open ValuationSpectrum CompletionLocalization

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### B-level flatness for the iteratedMinusDatum_B (`T = {1}`)

This is `presheafValue_flat_of_laurentMinus` of `StructureSheaf.lean`
specialised to `A := presheafValue D₀`, `P := presheafValue_pairOfDefinition_concrete P D₀`,
`D := iteratedMinusDatum_B P D₀ f`. The data has `T = {1}` and
`s = D₀.canonicalMap f`, so `hT_pb` and `hb` collapse to the singleton case,
and we are left with the canonical-topology hypotheses
`hA_complete_B`, `hnoeth_B`, `hcont_eval_B`.

Stated as a helper to declutter `restrictionMap_flat_via_iteratedMinus`. -/
omit [PlusSubring A] [HasLocLiftPowerBounded A] in
theorem iteratedMinus_B_flat_of_canonical
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue D₀) :=
      presheafValue_pairOfDefinition_concrete P D₀
    letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
    letI : IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
    @Module.Flat (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f))
      _ _ (RingHom.toModule (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
        (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- Discharge `hb` and `hT_pb` for `T = {1}`, `s = D₀.canonicalMap f`.
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedMinusDatum_B P D₀ f)) := by
    -- `D.T = {1}`, so `1 ∈ D.T`. Use `invS_isPowerBounded_of_one_mem_T`.
    have h1_mem : (1 : presheafValue D₀) ∈ (iteratedMinusDatum_B P D₀ f).T :=
      Finset.mem_singleton_self 1
    -- `invS D = D.coeRingHom (divByS 1 D.s)` (factor through completion).
    have hinvS_eq : invS (iteratedMinusDatum_B P D₀ f) =
        (iteratedMinusDatum_B P D₀ f).coeRingHom
          (divByS 1 (iteratedMinusDatum_B P D₀ f).s) := by
      set D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
      have halg : algebraMap (presheafValue D₀) (Localization.Away D.s) D.s *
          divByS 1 D.s = 1 := by
        rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
      have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
        change D.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away D.s) D.s) *
          D.coeRingHom (divByS 1 D.s) = 1
        rw [← map_mul, halg, map_one]
      have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
      exact hu.mul_left_cancel (h1.trans h2.symm)
    rw [hinvS_eq]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
      (iteratedMinusDatum_B P D₀ f) h1_mem
  have hT_pb : ∀ t ∈ (iteratedMinusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    -- `T = {1}` collapses to `t = 1`.
    rw [Finset.mem_singleton.mp ht]
    exact TopologicalRing.isPowerBounded_one
  -- Now apply `presheafValue_flat_of_canonical` at the B-level.
  exact presheafValue_flat_of_canonical (presheafValue D₀) P_B
    (iteratedMinusDatum_B P D₀ f) hb hA_complete_B hnoeth_B hT_pb (hcont_eval_B hb)

/-! ### Linear equiv compatibility for `presheafValue_iteratedMinus_equiv`

The ring equiv `presheafValue_iteratedMinus_equiv P D₀ f` intertwines:
* the source `presheafValue D₀`-module structure on
  `presheafValue (laurentMinusDatum D₀ f)` via
  `restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub`;
* the target `presheafValue D₀`-module structure on
  `presheafValue (iteratedMinusDatum_B P D₀ f)` via the canonical map
  `(iteratedMinusDatum_B P D₀ f).canonicalMap`.

This is the linear-equiv version of the sorry-free ring-hom compatibility
`presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`. -/

/-! ### T-FLAT-VIA-WEDHORN830: Module.Flat for the Laurent-minus restriction

`presheafValue (laurentMinusDatum D₀ f)` is flat as a `presheafValue D₀`-module
along `restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub`. Discharged via
the Wedhorn Prop 8.30 + Lemma 2.13 route, NOT via `IsLocalization.Away`. -/
theorem restrictionMap_flat_via_iteratedMinus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
          (iteratedMinusDatum_B P D₀ f).s))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedMinusDatum_B P D₀ f).P (iteratedMinusDatum_B P D₀ f).T
        (iteratedMinusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- Step 1: B-level flatness for the iteratedMinusDatum_B side.
  haveI hflat_B :
      @Module.Flat (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f))
        _ _ (RingHom.toModule
          (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))) :=
    iteratedMinus_B_flat_of_canonical P D₀ f hNoeth_B hLocLift_B
      hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hcont_eval_B
  -- Step 2: Transfer flatness via `presheafValue_iteratedMinus_equiv`.
  -- The equiv intertwines `restrictionMapHom`-module on the source with
  -- `canonicalMap`-module on the target (compatibility lemma below).
  let e := presheafValue_iteratedMinus_equiv P D₀ f
  -- Module structure compatibility: `e (a • x) = a • e x` where
  --  • src `•`: `a • x = restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub a * x`
  --  • tgt `•`: `a • y = (iteratedMinusDatum_B P D₀ f).canonicalMap a * y`
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentMinusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub).toModule
  letI : Module (presheafValue D₀) (presheafValue (iteratedMinusDatum_B P D₀ f)) :=
    RingHom.toModule (RationalLocData.canonicalMap (iteratedMinusDatum_B P D₀ f))
  -- `e_smul`: the equiv preserves the module action.
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentMinusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    -- Unfold scalar actions:
    --   src: a • x = restrictionMapHom (...) a * x
    --   tgt: a • e x = (iteratedMinusDatum_B P D₀ f).canonicalMap a * e x
    change e (restrictionMapHom D₀ (laurentMinusDatum D₀ f) hsub a * x) =
      (iteratedMinusDatum_B P D₀ f).canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    -- This is exactly `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`.
    exact presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap P D₀ f hsub a
  -- Apply `Module.Flat.of_linearEquiv` with the forward direction `e` as the
  -- LinearEquiv `N →ₗ M` where N = laurent-minus, M = iterated-minus B (known flat).
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue (iteratedMinusDatum_B P D₀ f))
    (presheafValue (laurentMinusDatum D₀ f))
    _ _ _ _ _ hflat_B
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### Plus-side analog: B-level flatness for the iteratedPlusDatum_B

`iteratedPlusDatum_B P D₀ f` has `T = {D₀.canonicalMap f}` and `s = 1`. Then
`invS D = 1` (a power-bounded unit), and `hT_pb` reduces to
`IsPowerBounded (D₀.canonicalMap f)` — an EXTERNAL hypothesis the caller
must supply (in contrast to the minus side where `T = {1}` collapses
trivially). -/
omit [PlusSubring A] [HasLocLiftPowerBounded A] in
theorem iteratedPlus_B_flat_of_canonical
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s))
    -- EXTRA HYPOTHESIS vs the minus side: `canonicalMap f` must be power-bounded.
    -- Holds when `f ∈ A°` (power-bounded elements of `A`) and `canonicalMap`
    -- preserves power-boundedness, which is the standard setting.
    (hf_canonical_pb : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      TopologicalRing.IsPowerBounded (D₀.canonicalMap f))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedPlusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
    letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
    letI P_B : PairOfDefinition (presheafValue D₀) :=
      presheafValue_pairOfDefinition_concrete P D₀
    letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
    letI : IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
    @Module.Flat (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f))
      _ _ (RingHom.toModule (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
        (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  -- For `s = 1`: `invS D = 1` (power-bounded).
  have hb : TopologicalRing.IsPowerBounded
      (invS (iteratedPlusDatum_B P D₀ f)) := by
    -- `D.s = 1` ⇒ `D.canonicalMap D.s = D.canonicalMap 1 = 1` ⇒ `invS D = 1`.
    have hinvS_eq : invS (iteratedPlusDatum_B P D₀ f) = 1 := by
      set D : RationalLocData (presheafValue D₀) := iteratedPlusDatum_B P D₀ f
      have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
      have hs : D.s = 1 := rfl
      rw [hs, map_one, one_mul] at h1
      exact h1
    rw [hinvS_eq]
    exact TopologicalRing.isPowerBounded_one
  -- For `T = {D₀.canonicalMap f}`: `hT_pb` follows from `hf_canonical_pb`.
  have hT_pb : ∀ t ∈ (iteratedPlusDatum_B P D₀ f).T,
      TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [Finset.mem_singleton.mp ht]
    exact hf_canonical_pb
  -- Apply `presheafValue_flat_of_canonical` at the B-level.
  exact presheafValue_flat_of_canonical (presheafValue D₀) P_B
    (iteratedPlusDatum_B P D₀ f) hb hA_complete_B hnoeth_B hT_pb (hcont_eval_B hb)

/-! ### T-FLAT-VIA-WEDHORN830 plus side: `Module.Flat` for the Laurent-plus restriction

`presheafValue (laurentPlusDatum D₀ f)` is flat as a `presheafValue D₀`-module
along `restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub`. Discharged via the
Wedhorn Prop 8.30 + Lemma 2.13 route on the PLUS side. Requires the additional
`hf_canonical_pb` hypothesis. -/
theorem restrictionMap_flat_via_iteratedPlus
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A)
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hsub : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
            rationalOpen D₀.T D₀.s)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hP_A₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hlocSubring_Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      IsNoetherianRing
        (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
          (iteratedPlusDatum_B P D₀ f).s))
    (hf_canonical_pb : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      TopologicalRing.IsPowerBounded (D₀.canonicalMap f))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      let D := iteratedPlusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) _ _
      ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule) := by
  letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  letI : IsNoetherianRing ↥P_B.A₀ := hP_A₀Noeth_B
  letI : IsNoetherianRing
      (locSubring (iteratedPlusDatum_B P D₀ f).P (iteratedPlusDatum_B P D₀ f).T
        (iteratedPlusDatum_B P D₀ f).s) := hlocSubring_Noeth_B
  haveI hflat_B :
      @Module.Flat (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f))
        _ _ (RingHom.toModule
          (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))) :=
    iteratedPlus_B_flat_of_canonical P D₀ f hNoeth_B hLocLift_B
      hA_complete_B hnoeth_B hP_A₀Noeth_B hlocSubring_Noeth_B hf_canonical_pb hcont_eval_B
  let e := presheafValue_iteratedPlus_equiv P D₀ f
  change @Module.Flat (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f))
    _ _ ((restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule)
  letI : Module (presheafValue D₀) (presheafValue (laurentPlusDatum D₀ f)) :=
    (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub).toModule
  letI : Module (presheafValue D₀) (presheafValue (iteratedPlusDatum_B P D₀ f)) :=
    RingHom.toModule (RationalLocData.canonicalMap (iteratedPlusDatum_B P D₀ f))
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue (laurentPlusDatum D₀ f)),
      e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D₀ (laurentPlusDatum D₀ f) hsub a * x) =
      (iteratedPlusDatum_B P D₀ f).canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    exact presheafValue_iteratedPlus_equiv_restrictionMap_canonicalMap P D₀ f hsub a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue (iteratedPlusDatum_B P D₀ f))
    (presheafValue (laurentPlusDatum D₀ f))
    _ _ _ _ _ hflat_B
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

end ValuationSpectrum
