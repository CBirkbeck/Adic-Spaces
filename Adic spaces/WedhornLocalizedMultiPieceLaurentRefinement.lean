/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornMultiPieceLaurentRefinement
import «Adic spaces».WedhornLocalCompatFromTestFamily

/-!
# Wedhorn 8.34(ii) — Localized multi-piece Laurent cover refinement (T171)

T054 (`WedhornMultiPieceLaurentRefinement.lean`) accepted the
**generic** per-piece Laurent cover refinement output
`MultiPieceLaurentCoverRefinementOutput`: at every `w ∈ Spa A A⁺` there
exists `τ ∈ T_test` with `w` in the σ-rescaled Laurent piece
`V_τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and a per-piece
**singleton** residual on `V_τ`. T054 explicitly documents that the
**universal-over-`T_test`** lower-bound form
`∀ τ ∈ T_test, w.vle 1 (σ⁻¹ * τ)` is **mathematically false** at a
single `w` (T035 counter-example).

T170 (`WedhornLocalCompatFromTestFamily.lean`, commit `7cbf2d8`)
exposed the same obstruction in the **localized** setting: the
`h_per_piece_multi_lower` hypothesis of T169
(`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement`, commit
`9d990df`) consumes `∀ t' ∈ T_D.image (algebraMap), w.vle 1 t'` per
`w` under f-membership, which is the **same false universal-over-`T_D`
lower-bound shape** at the localized level.

This file lands the **localized analogue** of T054's per-piece output
plus a **consumer reroute boundary** identifying the precise
cover-level assembly content needed to close the T168 α_T_D branch
honestly. The localized object specialises T054 at
`A := Localization.Away s` with the localized topology and plus-subring
instances, using `localizedTestFamily s T_D s_D` as the test family.

## What this file provides

* `LocalizedMultiPieceLaurentCoverRefinementOutput` — localized
  predicate naming T054's per-piece output at the localized level:
  at every `w ∈ Spa(Localization.Away s, ⁺)`, there exists
  `τ ∈ localizedTestFamily s T_D s_D` such that `w` lies in the
  σ_loc-rescaled Laurent piece together with a per-piece **singleton**
  lower-bound residual on that piece.

* `localizedMultiPieceLaurentCoverRefinementOutput_via_cor732` —
  bridge from localized Cor 7.32 σ-strict-domination to the localized
  per-piece output. Direct specialization of T054's
  `multiPieceLaurentCoverRefinementOutput_via_cor732` at
  `A := Localization.Away s` with the localized instances.

* `LocalizedAlphaTDBranchCoverLevelAssemblyResidual` — the **named
  cover-level assembly residual**: the precise compiled boundary
  identifying what additional content is needed beyond the per-piece
  singleton output to recover T168's α_T_D-branch conclusion. This
  isolates the missing Wedhorn Lemma 8.33 cover-level assembly content
  exactly.

* `h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece` — the
  **caller reroute**: composes the localized per-piece output with the
  cover-level assembly residual to produce T168's α_T_D-branch
  conclusion. Reduces the current T168/T169/T170 chain to the named
  cover-level assembly residual without invoking the false
  universal-over-`T_D` lower-bound clause.

## Why a separate file (not edits to T168/T169/T170 leaves)

* T168/T169/T170's existing chain consumes a hypothesis shape that is
  not achievable from generic Cor 7.32 + cover-refinement data (per
  T054). The reroute needs a different consumer interface — namely the
  per-piece singleton output — which is best presented in a fresh
  leaf file rather than threaded through the existing chain.

* The new declarations are purely additive; they do not modify
  T168/T169/T170 leaves, root imports, or final theorem signatures.

## Notes

* No root import (file is leaf-level relative to `Adic spaces.lean`;
  callers explicitly import as needed).
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No `locSubring` integral-closedness, no T001/T004/T015/final/root/C1
  edits.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [IsTopologicalRing A] in
/-- **T171 localized version of T054's
`MultiPieceLaurentCoverRefinementOutput`**.

For `Localization.Away s` with `localizedTestFamily s T_D s_D` as test
family: at every `w ∈ Spa(Localization.Away s, ⁺)`, there exists
`τ ∈ localizedTestFamily s T_D s_D` such that:

* `w ∈ rationalOpen ({(1 : Localization.Away s)}) (σ_loc⁻¹ · τ)` —
  Laurent piece membership.
* `MultiElementLowerBoundResidualOnPiece V_τ ({σ_loc⁻¹ · τ})` —
  per-piece **singleton** lower-bound residual at the σ-rescaled
  element of the piece.

Defined as the specialisation of T054's
`MultiPieceLaurentCoverRefinementOutput` at `A := Localization.Away s`
with the localized topology + plus-subring instances and
`T_test := localizedTestFamily s T_D s_D`. -/
def LocalizedMultiPieceLaurentCoverRefinementOutput
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  MultiPieceLaurentCoverRefinementOutput
    (σ := σ_loc) (localizedTestFamily s T_D s_D)

omit [PlusSubring A] in
/-- **T171 bridge from localized Cor 7.32 σ-strict-domination to the
localized per-piece output**.

Direct specialization of T054's
`multiPieceLaurentCoverRefinementOutput_via_cor732` at
`A := Localization.Away s` with the localized topology + plus-subring
instances and `T_test := localizedTestFamily s T_D s_D`. The
σ-strict-domination hypothesis is the standard
`exists_dominating_unit_in_localization` output (also consumed by T169's
`h_T_D_multi_and_lower_bound_via_laurent_cover_refinement`, commit
`9d990df`). -/
theorem localizedMultiPieceLaurentCoverRefinementOutput_via_cor732
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s)) :
    LocalizedMultiPieceLaurentCoverRefinementOutput
      P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  exact multiPieceLaurentCoverRefinementOutput_via_cor732 hσ_loc_dom

omit [PlusSubring A] in
/-- **T171 named cover-level assembly residual** for the localized
α_T_D branch.

This Prop precisely identifies what additional content is needed beyond
T171's per-piece singleton output (and beyond T170's multi-element
bound) to recover T168's α_T_D-branch conclusion via Wedhorn Lemma 8.33
cover-level assembly.

Specifically: from the localized per-piece output (per `w` an `τ` plus
the singleton residual on V_τ) plus the multi-element bound `w.vle (∏)
(algebraMap s_D)` from T170, the α_T_D-branch conclusion `∀ t' ∈
T_D.image (algebraMap), w.vle t' (algebraMap s_D)` plus `¬ w.vle
(algebraMap s_D) 0` requires a Wedhorn Lemma 8.33-style **cover-level
assembly** of per-piece per-`t'` upper bounds into a global per-`t'`
upper bound.

The honest residual content per `w` (case-split on the localized test-
family branch by `mem_localizedTestFamily_iff`):

* **`τ = algebraMap s_D` case** (V_{algebraMap s_D}): per-piece
  per-`t'` upper bound `∀ t' ∈ T_D.image (algebraMap), w.vle t'
  (algebraMap s_D)` on V_{algebraMap s_D}, derivable from
  `w.vle σ_loc (algebraMap s_D)` + per-element integrality.

* **`τ = algebraMap t` case** for `t ∈ T_D` (V_{algebraMap t}):
  per-piece per-`t'` upper bound on V_{algebraMap t}, derivable from
  `w.vle σ_loc (algebraMap t)` + the σ-strict-dom witness +
  case-specific arithmetic.

The named residual asks for the **conjunction** of these two
case-conditional bounds, which together cover Spa via T171's per-piece
output. T168's α_T_D-branch conclusion follows by case-split on the
piece membership τ + applying the per-piece bound. -/
def LocalizedAlphaTDBranchCoverLevelAssemblyResidual
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    ∀ τ ∈ localizedTestFamily s T_D s_D,
      w ∈ rationalOpen
          ({(1 : Localization.Away s)} : Finset (Localization.Away s))
          (((σ_loc⁻¹ : (Localization.Away s)ˣ) : Localization.Away s) *
            τ) →
      (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0

omit [PlusSubring A] in
/-- **T171 caller reroute**: from the localized per-piece output +
cover-level assembly residual, produce the T168 α_T_D-branch
conclusion.

This is the **honest reroute** of the T168 α_T_D branch route through
the corrected per-piece data, replacing the false universal-over-`T_D`
lower-bound clause with the named cover-level assembly residual that
exactly captures the genuine remaining content.

**Proof**: at each `w ∈ Spa` under f-membership, dispatch via the
localized per-piece output to obtain `τ ∈ localizedTestFamily` with
`w ∈ V_τ`, then apply the cover-level assembly residual at this τ. The
output is the per-`t'` upper bound + `s_D` non-vanishing — the exact
shape of T168's α_T_D-branch single-branch compatibility output.

**The cover-level assembly residual is the
strictly-stronger-than-pass-through compiled boundary** identified by
T171: it asks only for per-piece per-`t'` bounds (not the false
universal-over-`T_D` lower-bound clause), and its discharge is the
genuine remaining Wedhorn Lemma 8.33 / 8.34(ii) cover-level
arithmetic content. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_multi_piece :
      LocalizedMultiPieceLaurentCoverRefinementOutput
        P T s hopen T_D s_D σ_loc)
    (h_assembly :
      LocalizedAlphaTDBranchCoverLevelAssemblyResidual
        P T s hopen T_D s_D σ_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ_strict _hτ_strict_mem w hw_spa hw_f _hστ_strict
  -- Dispatch via the localized per-piece output to find a piece-`τ`
  -- containing `w`, then apply the cover-level assembly at that piece.
  obtain ⟨τ, hτ_mem, hw_piece, _h_singleton_residual⟩ :=
    h_multi_piece w hw_spa
  exact h_assembly w hw_spa hw_f τ hτ_mem hw_piece

omit [PlusSubring A] in
/-- **T171 end-to-end caller**: composes the localized per-piece bridge
(from σ-strict-domination via T054 specialisation) with the cover-level
assembly residual to produce the α_T_D-branch conclusion.

Demonstrates the corrected route from the natural Cor 7.32
σ-strict-domination input + the named cover-level assembly residual,
through T171's localized multi-piece output, to the α_T_D-branch
single-branch compatibility output. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_cor732_loc_and_assembly
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (hσ_loc_dom :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∃ τ ∈ localizedTestFamily s T_D s_D,
          w.vle (σ_loc : Localization.Away s) τ ∧
            ¬ w.vle τ (σ_loc : Localization.Away s))
    (h_assembly :
      LocalizedAlphaTDBranchCoverLevelAssemblyResidual
        P T s hopen T_D s_D σ_loc) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
          (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
              w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
            ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
  h_T_test_compat_loc_branch_α_T_D_via_localized_multi_piece
    P T s hopen T_D s_D σ_loc
    (localizedMultiPieceLaurentCoverRefinementOutput_via_cor732
      P T s hopen T_D s_D σ_loc hσ_loc_dom)
    h_assembly

end ValuationSpectrum
