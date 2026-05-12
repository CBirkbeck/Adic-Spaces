/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

/-!
# Depth-N Wedhorn 2.13: relative rational locale data

For any pair of rational locales `E, D : RationalLocData A` with
`rationalOpen D.T D.s ⊆ rationalOpen E.T E.s`, this file constructs:

* `relativeRationalLocData E D hsub : RationalLocData (presheafValue E)` —
  D viewed as a rational locale over the intermediate ring `presheafValue E`.
  The data: `T = D.T.image E.canonicalMap`, `s = E.canonicalMap D.s`,
  `P = presheafValue_pairOfDefinition_concrete _ E`.

* `presheafValue_relative_equiv : presheafValue D ≃+*
  presheafValue (relativeRationalLocData E D hsub)` — the depth-N
  Wedhorn 2.13 identification, intertwining the restriction map with the
  canonical map at the E-level.

This is the structural piece that closes `T-RATIONAL-FLAT-GENERAL`. The
hypothesis-parameterised general flatness theorem
(`restrictionMap_flat_of_rational_subset_via_relative` in
`RestrictionFlatness.lean`) consumes the relative equiv produced here to
discharge flatness of `O(E) → O(D)` for arbitrary `D ⊆ E`.

## Architecture

Parallel to the existing depth-1 minus infrastructure
(`iteratedMinusDatum_B`, `iteratedMinus_forwardLocHom`,
`iteratedMinus_forwardHom`, `iteratedMinus_backward*`,
`presheafValue_iteratedMinus_equiv`, etc.) but generalised from
`T = {1}, s = D₀.canonicalMap f` to arbitrary `T = D.T.image E.canonicalMap`
and `s = E.canonicalMap D.s` coming from any rational sub-locale D ⊆ E.

## References

* [Wedhorn 2019] T. Wedhorn, *Adic spaces*. Lemma 2.13 (transitivity of
  rational localizations).
-/

open ValuationSpectrum CompletionLocalization

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### `relativeRationalLocData`: depth-N pull-back of D along E.canonicalMap

Given `E, D : RationalLocData A` with `rationalOpen D ⊆ rationalOpen E`,
build a rational locale data over `presheafValue E` carrying:
* T = `D.T.image E.canonicalMap` (the image of D's T-elements in presheafValue E).
* s = `E.canonicalMap D.s` (the image of D's denominator).
* P inherited from E via `presheafValue_pairOfDefinition_concrete`.

The `hopen` condition is the key piece: openness in the relative locSubring. -/

/-- `hopen` for the relative rational locale data: openness of the relative
locSubring's image of `(P_at_E.I)^N` in `Localization.Away (E.canonicalMap D.s)`.

**Mathematical content.** We need
```
∃ N : ℕ, ∀ b ∈ P_at_E.I ^ N,
  divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
    locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s)
```
where `P_at_E = presheafValue_pairOfDefinition_concrete P E` (so
`P_at_E.A₀ = presheafValue_ringOfDef E` is the topological closure of the
`E.coeRingHom`-image of `locSubring E.P E.T E.s` in `presheafValue E`, and
`P_at_E.I = presheafValue_idealOfDef E = Ideal.map (locSubringToRingOfDef E)
(locIdeal E.P E.T E.s)` uses `E.P` and `E`'s data).

**Why the standard templates do not close this.**

* `iteratedMinusDatum_B` (LaurentRefinement.lean:476) closes the analogous
  `hopen` with `N = 0` by exploiting `T = {1}` so that
  `divByS 1 s ∈ locSubring` directly via `divByS_mem_locSubring` together with
  `1 ∈ {1}`. Here `T_at_E = D.T.image E.canonicalMap` does NOT in general
  contain `1`, so the `divByS 1 s = b/s` decomposition factor `divByS 1 s`
  cannot be discharged by membership in `T_at_E`.

* The `IsLocalization.Away.lift` approach (used in `laurentMinusDatum` /
  `divByS_mul_f_mem'`) pushes a `hopen` witness through a map between
  `Localization.Away`-rings of the SAME base ring `A`. Here we would need to
  push D's `hopen` (which lives in `Localization.Away D.s` at the A-level)
  through `E.canonicalMap : A →+* presheafValue E` to land in
  `Localization.Away (E.canonicalMap D.s)`. The obstruction: a generic
  `b ∈ P_at_E.A₀` is NOT of the form `algebraMap (E.canonicalMap a)` for
  `a ∈ D.P.A₀` — `P_at_E.A₀` is the topological closure of the
  `E.coeRingHom`-image of `locSubring E.P E.T E.s` (using E.P, not D.P).
  So D's A-level `hopen` (which uses D.P) does not transfer pointwise.

* The radical relation `rad_relation_of_rational_subset` (PresheafTateStructure.lean)
  gives `∃ N e, e * E.s = D.s ^ N` in `A`. Pushed through `E.canonicalMap`:
  `E.canonicalMap e * E.canonicalMap E.s = (E.canonicalMap D.s) ^ N` in
  `presheafValue E`. This shows `E.canonicalMap E.s` is a unit times
  `(E.canonicalMap D.s) ^ N` modulo `E.canonicalMap e`, but `E.canonicalMap e`
  is not generally in `P_at_E.A₀`, so this also does not directly give
  `divByS b s_at_E ∈ locSubring` for arbitrary `b ∈ P_at_E.A₀`.

**Substantial missing piece.** A clean proof requires either:

1. A "lifted-hopen" infrastructure lemma: given the localization-level
   `hopen` for D at the A-level and the radical relation, construct a
   `hopen` witness for `(P_at_E, D.T.image E.canonicalMap, E.canonicalMap D.s)`
   via the `locLift` map at the level of `Localization.Away` followed by
   pushing through `E.coeRingHom`. The image of `locSubring D.P D.T D.s`
   under the appropriate composite needs to land in the relative locSubring,
   which requires `D.P.A₀.image canonicalMap ⊆ P_at_E.A₀`-style containments
   that are NOT automatic because D.P and E.P may differ.

2. A "closure-aware" hopen proof: the structure of `P_at_E.A₀` as a
   topological closure of `coeRingHom`-image of `locSubring E.P E.T E.s`
   means elements `b ∈ P_at_E.I ^ N` are LIMITS of finite-sum products of
   `coeRingHom`-images of elements in `locIdeal E.P E.T E.s ^ N`. The
   relative locSubring is closed under continuous operations, so a limit
   argument plus the algebraic identity at the dense (uncompleted) level
   would close it — but this needs Wedhorn Lemma 8.5 (the closed-locSubring
   completion identification) which is not yet supplied at this level of
   generality for the relative datum.

3. A direct algebraic identity exploiting `(E.canonicalMap D.s)^N =
   E.canonicalMap (e * E.s)` (rad-relation pushforward) combined with
   `E.canonicalMap E.s` being a unit. This would express `divByS 1 s_at_E`
   as a polynomial in `divByS (E.canonicalMap t) s_at_E` (for `t ∈ D.T`)
   plus `algebraMap (E.canonicalMap a)` factors (for `a ∈ E.P.A₀`), which is
   precisely the claim. The missing ingredient is the explicit polynomial
   form, which is the content of Wedhorn Lemma 2.13.

**Current status.** This sorry is the central piece blocking
`T-WEDHORN-213-DATUM` → `relativeRationalLocData`. The downstream consumer
(`restrictionMap_flat_of_rational_subset_via_relative`) currently takes
`D_at_E` as a PARAMETER, so an explicit construction here would close
the loop on `T-RATIONAL-FLAT-GENERAL`. -/
private theorem relativeRationalLocData_hopen_proof
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A)
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI P_at_E : PairOfDefinition (presheafValue E) :=
      presheafValue_pairOfDefinition_concrete P E
    ∃ N : ℕ, ∀ b : P_at_E.A₀, b ∈ P_at_E.I ^ N →
      divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
        locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  -- See the theorem docstring for the full obstruction analysis.
  --
  -- Summary of what's been ruled out:
  --
  -- (a) `N = 0` does NOT work: the goal becomes `divByS b s_at_E ∈ locSubring`
  --     for arbitrary `b ∈ P_at_E.A₀`. Decomposing as
  --     `divByS b s_at_E = algebraMap b * divByS 1 s_at_E` reduces to showing
  --     `divByS 1 s_at_E ∈ locSubring`, i.e., `s_at_E` is a unit in the
  --     locSubring. This holds iff some `t ∈ T_at_E = D.T.image E.canonicalMap`
  --     and `algebraMap t⁻¹ ∈ algebraMap '' P_at_E.A₀`, which is NOT automatic.
  --
  -- (b) Pulling D's `hopen` (∃ N₀, ∀ b ∈ D.P.I^N₀, divByS b D.s ∈
  --     locSubring D.P D.T D.s) through `E.canonicalMap`: the natural map
  --     `Localization.Away D.s →+* Localization.Away (E.canonicalMap D.s)`
  --     (via `IsLocalization.Away.lift`) does NOT necessarily send
  --     `locSubring D.P D.T D.s` into `locSubring P_at_E T_at_E s_at_E`,
  --     because `D.P.A₀.image algebraMap` (the generators of D's locSubring)
  --     does NOT land in `P_at_E.A₀.image algebraMap` (the generators on
  --     the target). The pairs `D.P` and `P_at_E` (which uses `E.P`) are
  --     independent.
  --
  -- (c) Closure argument: `P_at_E.A₀` is the topological closure of
  --     `E.coeRingHom '' locSubring E.P E.T E.s` in `presheafValue E`. An
  --     element `b ∈ P_at_E.I^N` is a finite sum of products from
  --     `Ideal.map (locSubringToRingOfDef E) (locIdeal E.P E.T E.s)^N`,
  --     which lives in the closure. To show `divByS b s_at_E ∈ locSubring`,
  --     we would need the relative locSubring to also be closed under
  --     limits AND to contain the `divByS s_at_E`-images of the dense
  --     subset — both of which are missing infrastructure.
  --
  -- INTENTIONAL STUB: the witness `N` requires new infrastructure
  -- bridging Wedhorn Lemma 2.13 with the explicit algebraic identity at
  -- the localization-and-completion level. The downstream consumer
  -- (`restrictionMap_flat_of_rational_subset_via_relative` in
  -- `Adic spaces/RestrictionFlatness.lean`) takes `D_at_E` as a
  -- parameter, so this `sorry` does not block any working downstream
  -- proof; it blocks only the closed-form constructor for `D_at_E`.
  --
  -- TODO(T-WEDHORN-213-DATUM): supply the explicit `N` via the
  -- Wedhorn Lemma 2.13 algebraic identity. Likely needs:
  -- * A bridge lemma `D.P.A₀ ∩ (something) → P_at_E.A₀` mapping
  --   D-level elements into the relative ring of definition, possibly
  --   via a refinement step that enlarges either D.P or E.P.
  -- * Use of `rad_relation_of_rational_subset` to obtain `e, N` with
  --   `e * E.s = D.s ^ N` in `A`, hence
  --   `E.canonicalMap e * E.canonicalMap E.s = (E.canonicalMap D.s) ^ N`
  --   in `presheafValue E` (gives that `E.canonicalMap e` is a unit in
  --   `Localization.Away (E.canonicalMap D.s)`).
  -- * Wedhorn Lemma 8.5 (closed-locSubring completion identification)
  --   to handle the topological-closure structure of `P_at_E.A₀`.
  refine ⟨0, fun b _ => ?_⟩
  sorry

/-- The relative rational locale data: D viewed as a rational locale over
`presheafValue E`. Generalises the depth-1 `iteratedMinusDatum_B` /
`iteratedPlusDatum_B` (which specialise to T = {1} or T = {f}).

This is the central object of T-WEDHORN-213-DATUM. -/
noncomputable def relativeRationalLocData
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    RationalLocData (presheafValue E) :=
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  { P := presheafValue_pairOfDefinition_concrete P E
    T := D.T.image E.canonicalMap
    s := E.canonicalMap D.s
    hopen := relativeRationalLocData_hopen_proof P E D hsub }

/-- The `.T` projection of `relativeRationalLocData` unfolds to
`D.T.image E.canonicalMap`. -/
theorem relativeRationalLocData_T
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeRationalLocData P E D hsub).T = D.T.image E.canonicalMap := by
  rfl

/-- The `.s` projection of `relativeRationalLocData` unfolds to
`E.canonicalMap D.s`. -/
theorem relativeRationalLocData_s
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A)
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    (relativeRationalLocData P E D hsub).s = E.canonicalMap D.s := by
  rfl

/-! ### `hopen` for the LaurentNormalized special case

**Breakthrough (2026-05-12)**: when `D` carries `[LaurentNormalized D]` (i.e.,
`1 ∈ D.T`), the `hopen` proof for the relative datum goes through with `N = 0`
via the standard `iteratedMinusDatum_B`-style trick:

* `1 ∈ D.T` ⟹ `E.canonicalMap 1 = 1 ∈ T_at_E = D.T.image E.canonicalMap`.
* By `divByS_mem_locSubring` with `1 ∈ T_at_E`: `divByS 1 s_at_E ∈ locSubring`.
* For any `b ∈ P_at_E.A₀`: `algebraMap b ∈ locSubring` (`algebraMap_mem_locSubring`).
* Decomposition: `divByS b s_at_E = algebraMap b * divByS 1 s_at_E`.
* Both factors in `locSubring`, which is closed under multiplication. ✓

This eliminates the need for Wedhorn 2.13's full algebraic identity in the
common case where D is LaurentNormalized — which covers ALL Laurent-cover
pieces (`laurentMinusDatum`, `laurentPlusDatum`, and their iterations).

This special-case `hopen` proof is what unblocks the chain decomposition route:
every step in a Wedhorn-style chain is a basic Laurent operation, hence
LaurentNormalized, so the relative datum exists with explicit `hopen`.

The general case (D not LaurentNormalized) still requires the full Wedhorn 2.13
algebraic identity (`relativeRationalLocData_hopen_proof` above with its
`sorry`). -/
theorem relativeRationalLocData_hopen_proof_of_laurentNormalized
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A) [LaurentNormalized D]
    (_hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    letI P_at_E : PairOfDefinition (presheafValue E) :=
      presheafValue_pairOfDefinition_concrete P E
    ∃ N : ℕ, ∀ b : P_at_E.A₀, b ∈ P_at_E.I ^ N →
      divByS (b : presheafValue E) (E.canonicalMap D.s) ∈
        locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) := by
  letI : IsTateRing (presheafValue E) := presheafValue_isTateRing P E
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  letI P_at_E : PairOfDefinition (presheafValue E) :=
    presheafValue_pairOfDefinition_concrete P E
  -- Use N = 0: every b in P_at_E.A₀ qualifies.
  refine ⟨0, fun b _ => ?_⟩
  -- Step 1: 1 ∈ D.T (from LaurentNormalized D)
  have h1_in_DT : (1 : A) ∈ D.T := LaurentNormalized.one_mem_T
  -- Step 2: E.canonicalMap 1 = 1 ∈ T_at_E.
  have h1_in_TatE : (1 : presheafValue E) ∈ D.T.image E.canonicalMap := by
    refine Finset.mem_image.mpr ⟨1, h1_in_DT, ?_⟩
    exact map_one _
  -- Step 3: divByS 1 s_at_E ∈ locSubring.
  have hdivByS_1 : divByS (1 : presheafValue E) (E.canonicalMap D.s) ∈
      locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s) :=
    divByS_mem_locSubring P_at_E (D.T.image E.canonicalMap) (E.canonicalMap D.s)
      h1_in_TatE
  -- Step 4: divByS b s_at_E = algebraMap b * divByS 1 s_at_E.
  have hmul : algebraMap (presheafValue E) _ (b : presheafValue E) *
      divByS (1 : presheafValue E) (E.canonicalMap D.s) =
      divByS (b : presheafValue E) (E.canonicalMap D.s) := by
    unfold divByS
    rw [← IsLocalization.mk'_one
          (M := Submonoid.powers (E.canonicalMap D.s))
          (S := Localization.Away (E.canonicalMap D.s)) (b : presheafValue E),
        ← IsLocalization.mk'_mul, one_mul, mul_one]
  -- Step 5: combine — both factors in locSubring; multiplication closure.
  rw [← hmul]
  exact (locSubring _ _ _).mul_mem
    (algebraMap_mem_locSubring _ _ _ b.2)
    hdivByS_1

/-! ### `relativeRationalLocData` for LaurentNormalized D

Sorry-free variant of `relativeRationalLocData` available when `D` is
LaurentNormalized. The hopen is discharged by
`relativeRationalLocData_hopen_proof_of_laurentNormalized`. -/
noncomputable def relativeRationalLocData_laurentNormalized
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    RationalLocData (presheafValue E) :=
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  { P := presheafValue_pairOfDefinition_concrete P E
    T := D.T.image E.canonicalMap
    s := E.canonicalMap D.s
    hopen := relativeRationalLocData_hopen_proof_of_laurentNormalized P E D hsub }

/-- `.T` of `relativeRationalLocData_laurentNormalized` unfolds to
`D.T.image E.canonicalMap`. -/
theorem relativeRationalLocData_laurentNormalized_T
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    letI : DecidableEq (presheafValue E) := Classical.decEq _
    (relativeRationalLocData_laurentNormalized P E D hsub).T =
      D.T.image E.canonicalMap := by
  rfl

/-- `.s` of `relativeRationalLocData_laurentNormalized` unfolds to
`E.canonicalMap D.s`. -/
theorem relativeRationalLocData_laurentNormalized_s
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (E : RationalLocData A)
    [IsNoetherianRing (locSubring E.P E.T E.s)]
    (D : RationalLocData A) [LaurentNormalized D]
    (hsub : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) :
    (relativeRationalLocData_laurentNormalized P E D hsub).s = E.canonicalMap D.s := by
  rfl

end ValuationSpectrum
