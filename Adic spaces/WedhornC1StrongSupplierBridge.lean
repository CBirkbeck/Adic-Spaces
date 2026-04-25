/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornStrengthenedC1
import «Adic spaces».WedhornNormalizedC1Assembly

/-!
# Strong-supplier insertDenom-lift bridge

The downstream Wedhorn 8.34(ii) assembly chain consumes
`C1SupplierStrong_local C.insertDenom` (e.g.,
`WedhornBaseSpaFinalBridgeStrong.lean:98`,
`WedhornNormalizedC1AssemblyStrong.lean:105`). This file lands the
**structural lift** from `C1SupplierStrong_local C` to
`C1SupplierStrong_local C.insertDenom`, the largest compileable
theorem-level bridge toward producing the strong supplier on the
normalized cover from one on the original.

## Why this lift

`C.insertDenom`'s pieces have `D.s ∈ D.T` (the normalization). The
downstream consumers
(`WedhornStrengthenedC1.exists_single_f_refining_point_in_D_via_C1SupplierStrong`,
`WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier`)
exploit this normalization. But producing
`C1SupplierStrong_local C.insertDenom` directly from Tate hypotheses
requires the full Wedhorn 8.34(ii) σ-construction (still external; see
`WedhornStandardCoverRefinement.lean:91` target signature). The
structural lift here turns an abstract `C1SupplierStrong_local C`
(potentially supplied by Tertiary) into the consumer-ready form on the
normalized cover, modulo the mild non-emptiness hypothesis on cover-piece
test families documented below.

## What this file provides

`C1SupplierStrong_local_insertDenom_lift` — given:

1. `C1SupplierStrong_local C` — abstract strong supplier on the original
   cover.
2. `h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty` — every cover-piece
   test family is non-empty (mild restriction; cover pieces with
   `D.T = ∅` are basic-opens-at-`D.s`, an unusual degenerate case).

Produces `C1SupplierStrong_local C.insertDenom`, the consumer-ready
strong supplier on the normalized cover.

## Why the non-emptiness hypothesis

For `D ∈ C.covers` with `D.T = ∅`: the corresponding `D.insertDenom`
has `D.insertDenom.T = {D.s}` (non-empty), and the strong supplier on
`C.insertDenom` would receive `t = D.s` as the test element. There is
no element of `D.T` to substitute in the underlying
`C1SupplierStrong_local C` call (which requires `t ∈ D.T`), so the
`D.T = ∅` case is uncovered by this lift. The hypothesis
`h_covers_nonempty` rules out this degenerate subcase, which is harmless
for typical rational coverings.

## Documented residual: producing `C1SupplierStrong_local C` from Tate hypotheses

The genuine remaining work toward Wedhorn 8.34(ii) is producing
`C1SupplierStrong_local C` from concrete Tate/noetherian/pseudouniformizer
hypotheses. The exact missing target signature is:

```
theorem produce_C1SupplierStrong_local_via_Wedhorn_834
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    -- Localization-topology openness data for the rational-open transfer
    -- (`rationalOpen_transfer_via_localization`):
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s) :
    C1SupplierStrong_local C
```

The proof would (canonically) proceed via:
1. Pre-localise `A` at `C.base.s` to obtain `(A_loc, A_loc⁺_image)`
   (`localizationAwayPlusSubring`).
2. Apply `Cor732.exists_dominating_unit` inside
   `Spa(A_loc, A_loc⁺_image)` (where `C.base.s` is invertible, so the
   test family is unconstrained) to extract `σ_loc : (A_loc)ˣ`.
3. Clear denominators: `σ_loc * (algebraMap C.base.s)^M = algebraMap σ`
   for some `σ : A` and `M : ℕ`.
4. Set `f := σ * t * D.s ^ N` per Wedhorn's construction.
5. Verify the three C1 clauses via `rationalOpen_transfer_via_localization`
   plus the σ-domination output.

Steps 2-5 are the genuinely Wedhorn 8.34(ii)-specific content; this
file's structural lift is independent of them.

## Notes

* No root import; leaf-level file.
* No edits to `WedhornStrengthenedC1.lean`,
  `WedhornCoverNormalization.lean`, `WedhornNormalizedC1Assembly.lean`,
  or any other Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness
  / final-acyclicity file.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Structural lift: `C1SupplierStrong_local C → C1SupplierStrong_local
C.insertDenom`** (mod cover-piece non-emptiness).

Given an abstract strong C1 supplier on the original cover `C` plus the
mild non-emptiness condition `∀ D ∈ C.covers, D.T.Nonempty`, the lift to
the normalized cover `C.insertDenom` is straightforward: invoke the
supplier on the underlying `D` (using a substitute test element from
`D.T`) and translate the rational-open clauses through the
`rationalOpen_insertDenom` and `rationalOpen_insert_base_insertDenom_eq`
identities. The conclusion's `f` is independent of `t` (only depends on
`D` and `v`), so the substitution is invisible to the user.

**Use case**: feed this into
`WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier`
and onward into `WedhornBaseSpaFinalBridgeStrong`. -/
theorem C1SupplierStrong_local_insertDenom_lift
    [DecidableEq A] (C : RationalCovering A)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_C1 : C1SupplierStrong_local C) :
    C1SupplierStrong_local C.insertDenom := by
  classical
  intro D' hD' v hv t _ht _hvt hvD_s
  -- D' = D.insertDenom for some D ∈ C.covers.
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hD'
  -- Pick a substitute test element from D.T (non-empty by hypothesis).
  obtain ⟨t', ht'_mem⟩ := h_covers_nonempty D hD
  -- Translate hypotheses on D.insertDenom back to D.
  rw [RationalLocData.rationalOpen_insertDenom] at hv
  rw [RationalLocData.insertDenom_s] at hvD_s
  -- Inputs to the underlying supplier on C, using t' ∈ D.T.
  have hvt' : v.vle t' D.s := hv.2.1 t' ht'_mem
  obtain ⟨f, hv_in, hsub, hnonzero⟩ :=
    h_C1 D hD v hv t' ht'_mem hvt' hvD_s
  refine ⟨f, ?_, ?_, hnonzero⟩
  · -- v ∈ rationalOpen (insert f C.insertDenom.base.T) C.insertDenom.base.s
    rw [rationalOpen_insert_base_insertDenom_eq]
    exact hv_in
  · -- subset translation
    rw [rationalOpen_insert_base_insertDenom_eq,
      RationalLocData.rationalOpen_insertDenom]
    exact hsub

end ValuationSpectrum
