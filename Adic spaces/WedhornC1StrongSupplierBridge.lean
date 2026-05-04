/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornStrengthenedC1
import «Adic spaces».WedhornNormalizedC1Assembly
import «Adic spaces».WedhornLocalizedMultiPieceLaurentRefinement

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

/-! ### T178: produce `C1SupplierStrong_local C` via T177's per-call localized
multi-piece supply

T177 (commit `09a84d9`,
`WedhornLocalizedMultiPieceLaurentRefinement.lean`) provides
`C1SupplierStrong_local_via_localized_multi_piece_data`, which produces
`C1SupplierStrong_local C` from per-call delivery of
`WedhornC1PerCallSupplyLocalizedMultiPiece` — the natural Wedhorn
cover-piece structural data (cover-refinement element identity,
cover-base factorization, ring-of-definition membership, source-side
clauses).

This section attacks the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` by lowering it to
T177's clean per-call supply boundary.

**Status: caller-facing reduction (acceptable fallback)**. The full
discharge from concrete Tate / pseudouniformizer hypotheses to the
per-call supply requires the Wedhorn 8.34(ii) σ-construction
(localized Cor 7.32 σ-strict-dominating unit, denominator-clearing
construction `f := σ · t · D.s ^ N`, and source-side rational-open
membership transfer) — the genuinely missing per-call structural
producer. T178's reduction theorem isolates that per-call producer
as the single open input.

Provided:

* `produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply` —
  caller-facing reduction theorem. Takes the natural cover-base
  structural data (`P`, `hA₀_le`, `C`, `hopen_base`) plus T177's
  `WedhornC1PerCallSupplyLocalizedMultiPiece` per-call supply, and
  produces `C1SupplierStrong_local C` via
  `C1SupplierStrong_local_via_localized_multi_piece_data`.

The Tate / noetherian / pseudouniformizer hypotheses listed in the
documented residual signature are not required by this reduction —
they belong to a future per-call supply producer (Wedhorn 8.34(ii)
σ-construction at the per-call level), which is outside T178's scope. -/

/-- **T178 caller-facing reduction**: produce `C1SupplierStrong_local C`
from T177's per-call localized multi-piece supply.

Reduces the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` (in this file's
docstring) to T177's clean per-call boundary
`WedhornC1PerCallSupplyLocalizedMultiPiece`. The per-call supply is
the **genuine missing per-call structural producer**: the Wedhorn
8.34(ii) σ-construction packaged as `(σ_loc, f, h_alg, h_s_factor,
hT_D_le_A₀, hv_in_plus, hvf_nz)` per `(D, v, t)`. Its discharge from
concrete Tate / pseudouniformizer hypotheses is the next theorem-level
ticket beyond T178.

Composition: applies
`C1SupplierStrong_local_via_localized_multi_piece_data` (T177).
Clauses 1, 2, 3 of `C1SupplierStrong_local` are dispatched through
T172/T173/T175/T176 producers internally to T177; T178 only handles
the per-call delivery layer. -/
theorem produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCovering A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (h_per_call_supply :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v) :
    C1SupplierStrong_local C :=
  C1SupplierStrong_local_via_localized_multi_piece_data
    P hA₀_le C hopen_base h_per_call_supply

/-! ### T179: per-call localized multi-piece supply producer

T178 (commit `d33b428`, this file) reduces the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` to T177's per-call
boundary `WedhornC1PerCallSupplyLocalizedMultiPiece`. T179 attacks the
**per-call producer** itself: how to construct that supply from
concrete Wedhorn 8.34(ii) Tate setup data.

**Decomposition of the per-call supply**:

The 8 fields of `WedhornC1PerCallSupplyLocalizedMultiPiece`:
* (1) `σ_loc : (Loc C.base.s)ˣ`,
* (2) `f : A`,
* (3) `hσ_loc_dom` — σ-strict-dom over `localizedTestFamily`,
* (4) `h_alg` — `algebraMap f = σ_loc · ∏ D.T.image`,
* (5) `h_s_factor` — `C.base.s = D.s · f`,
* (6) `hT_D_le_A₀` — `∀ t ∈ D.T, t ∈ P.A₀`,
* (7a) `hv_in_plus` — `v ∈ rationalOpen (insert f C.base.T) C.base.s`,
* (7b) `hvf_nz` — `¬ v.vle f 0`,

split naturally into:

* **Cover structural data**: `hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ t ∈ D.T, t ∈ P.A₀`
  — a cover-piece structural condition not present in
  `RationalCovering`'s definition; must be supplied explicitly.

* **σ/denominator/factorization construction (the genuinely missing
  per-call structural lemma)**: at each per-call `(D, v, t)`, construct
  `σ_loc, f` together with `hσ_loc_dom`, `h_alg`, `h_s_factor`,
  `hv_in_plus`, `hvf_nz`. This is Wedhorn 8.34(ii)'s explicit
  σ-construction `f := σ · t · D.s ^ N`, with σ chosen via
  `Cor732.exists_dominating_unit` (the localized
  `exists_dominating_unit_in_localization` API requires lifting the
  global pseudouniformizer `π : P.A₀` to a localized `π_loc` plus the
  Tate transfer of pseudouniformizer hypotheses; that lifting is the
  inner content of the missing structural lemma).

**T179 deliverable shape (acceptable fallback)**: a compiled,
caller-facing per-call reduction theorem that names
`h_dom_factorization` (the σ/denominator/factorization construction)
as the genuinely missing structural lemma and consumes
`hT_D_le_A₀` from the cover structural data, producing the per-call
`WedhornC1PerCallSupplyLocalizedMultiPiece`. A top-level theorem
composes with T178 to produce `C1SupplierStrong_local C`.

Provided:

* `produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply`
  — per-call reduction theorem.
* `produce_C1SupplierStrong_local_via_Wedhorn_834_via_factorization_and_dom_supply`
  — top-level theorem composing the per-call reduction with T178. -/

/-- **T179 per-call reduction**: produce
`WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v` from
the σ/denominator/factorization construction supplier plus the
cover-piece structural hypothesis `hT_D_le_A₀`.

The construction supplier `h_dom_factorization` packages five of the
six per-call fields:

* `σ_loc, f` (the constructed unit and cover-refinement element);
* `hσ_loc_dom`, `h_alg`, `h_s_factor` (Wedhorn cover-piece factorization
  identities);
* `hv_in_plus`, `hvf_nz` (source-side rational-open transfer).

The remaining `hT_D_le_A₀` is supplied separately as a cover-piece
structural hypothesis (the natural Wedhorn `D.T ⊆ P.A₀` condition;
explicitly required since `RationalCovering` does not embed it).

This is the **first compiled boundary** for the per-call supply
construction: the manageable inputs are isolated as cover structural
data, and the genuinely Wedhorn 8.34(ii)-specific content is named
exactly as the σ/denominator/factorization construction supplier. -/
theorem produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply
    [DecidableEq A]
    (P : PairOfDefinition A)
    (C : RationalCovering A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (D : RationalLocData A) (v : Spv A)
    (hT_D_le_A₀ : ∀ τ ∈ D.T, τ ∈ P.A₀)
    (h_dom_factorization :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
        (∀ w ∈ Spa (Localization.Away C.base.s)
              (Localization.Away C.base.s)⁺,
            ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
              w.vle (σ_loc : Localization.Away C.base.s) τ ∧
                ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
        (algebraMap A (Localization.Away C.base.s) f =
          (σ_loc : Localization.Away C.base.s) *
            (∏ τ ∈ D.T.image (algebraMap A (Localization.Away C.base.s)),
              τ)) ∧
        C.base.s = D.s * f ∧
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0) :
    WedhornC1PerCallSupplyLocalizedMultiPiece P C hopen_base D v := by
  letI : TopologicalSpace (Localization.Away C.base.s) :=
    locTopology P C.base.T C.base.s hopen_base
  letI : PlusSubring (Localization.Away C.base.s) :=
    localizationLocSubringPlusSubring P C.base.T C.base.s
  letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
  obtain ⟨σ_loc, f, hσ_dom, h_alg, h_s_factor, hv_in, hvf_nz⟩ :=
    h_dom_factorization
  exact ⟨σ_loc, f, hσ_dom, h_alg, h_s_factor, hT_D_le_A₀, hv_in, hvf_nz⟩

/-- **T179 top-level reduction**: produce `C1SupplierStrong_local C`
from per-call σ/denominator/factorization construction supplier plus
cover-piece structural data, composing T179's per-call reduction with
T178's caller-facing reduction.

**Inputs**:
* `P`, `hA₀_le`, `C`, `hopen_base` — natural cover-base structural data.
* `hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ t ∈ D.T, t ∈ P.A₀` —
  cover-piece structural condition (the natural Wedhorn `D.T ⊆ P.A₀`
  condition; explicit since `RationalCovering` does not embed it).
* `h_per_call_construction` — per-call σ/denominator/factorization
  construction supplier (the genuinely missing Wedhorn 8.34(ii) per-call
  structural lemma).

**Output**: `C1SupplierStrong_local C`.

After T179, the documented residual
`produce_C1SupplierStrong_local_via_Wedhorn_834` is reduced to a single
named per-call structural lemma `h_per_call_construction` plus the
cover structural hypothesis. The Wedhorn 8.34(ii) σ-construction at
the per-call level is the only remaining input. -/
theorem produce_C1SupplierStrong_local_via_Wedhorn_834_via_factorization_and_dom_supply
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (C : RationalCovering A)
    (hopen_base : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) C.base.s ∈ locSubring P C.base.T C.base.s)
    (hT_covers_le_A₀ : ∀ D ∈ C.covers, ∀ τ ∈ D.T, τ ∈ P.A₀)
    (h_per_call_construction :
      letI : TopologicalSpace (Localization.Away C.base.s) :=
        locTopology P C.base.T C.base.s hopen_base
      letI : PlusSubring (Localization.Away C.base.s) :=
        localizationLocSubringPlusSubring P C.base.T C.base.s
      letI : DecidableEq (Localization.Away C.base.s) := Classical.decEq _
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ_loc : (Localization.Away C.base.s)ˣ) (f : A),
          (∀ w ∈ Spa (Localization.Away C.base.s)
                (Localization.Away C.base.s)⁺,
              ∃ τ ∈ localizedTestFamily C.base.s D.T D.s,
                w.vle (σ_loc : Localization.Away C.base.s) τ ∧
                  ¬ w.vle τ (σ_loc : Localization.Away C.base.s)) ∧
          (algebraMap A (Localization.Away C.base.s) f =
            (σ_loc : Localization.Away C.base.s) *
              (∏ τ ∈ D.T.image
                (algebraMap A (Localization.Away C.base.s)), τ)) ∧
          C.base.s = D.s * f ∧
          v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
          ¬ v.vle f 0) :
    C1SupplierStrong_local C :=
  produce_C1SupplierStrong_local_via_Wedhorn_834_via_per_call_supply
    P hA₀_le C hopen_base
    (fun D hD v hv t ht hvt hvD_s =>
      produce_WedhornC1PerCallSupplyLocalizedMultiPiece_via_factorization_and_dom_supply
        P C hopen_base D v (hT_covers_le_A₀ D hD)
        (h_per_call_construction D hD v hv t ht hvt hvD_s))

end ValuationSpectrum
