/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornMPowerStructuralDataHonest
import «Adic spaces».WedhornLocalArithmeticPerTChain

/-!
# `WedhornMPowerStructuralDataHonest` from localized Cor 7.32 / branch
data

The honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` (commit landing
`WedhornMPowerStructuralDataHonest.lean`) packages the per-`t'`
σ-factored inequality

```
w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)
```

at each `(w, τ, t')` over the canonical test family
`localizedTestFamily s T_D s_D`. By `vle_iff_mul_unit_right`
(`WedhornMultiBranchSubsetInequality.lean`) this is **equivalent under
σ-cancellation** to the unfactored per-`t'` inequality

```
w.vle t' (algebraMap s_D)
```

which is the natural Wedhorn 8.34(ii) per-`t'` content.

## What this file provides

This file lands the **σ-cancellation reducer** between the σ-factored
honest target and its unfactored counterpart, plus the **trivial
`t' = algebraMap s_D` subcase closed by reflexivity**, plus a
**caller-shaped wrapper** that takes the unfactored per-`t'` chain as a
single hypothesis and produces `WedhornMPowerStructuralDataHonest`.

* `WedhornMPowerStructuralDataHonest_via_unfactored_chain` — the
  caller-shaped wrapper. Takes the unfactored per-`t'` chain
  `∀ w hf τ hτ hστ t' ht', w.vle t' (algebraMap s_D)` (the genuine
  Wedhorn-content residual on the local Spa) and produces
  `WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc`. Pure
  σ-cancellation via `vle_iff_mul_unit_right`.

* `WedhornMPowerStructuralDataHonest_t_eq_s_D_branch` — closes the
  `t' = algebraMap s_D` subcase trivially via `vle_total`. This
  branch is closed at every `(w, τ)` regardless of σ-strict-domination
  τ. Useful when `s_D ∈ T_D` (the `insertDenom`-normalised cover-piece
  setup).

## Branch case analysis

The honest target's quantification structure: `∀ w hf τ hτ hστ t' ht'`
with conclusion `w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`. The
test-family branches:

* **α_s_D branch**: `τ = algebraMap s_D`. σ-strict-domination by
  `algebraMap s_D` gives `w(σ_loc) ≤ w(algebraMap s_D)` strict; this
  pins down `algebraMap s_D` non-degeneracy via
  `not_vle_zero_of_strict_dominator` but does NOT directly give
  `w(t') ≤ w(algebraMap s_D)` for general `t' ∈ T_D.image algebraMap`.
* **α_T_D branch**: `τ = algebraMap t₀` for some `t₀ ∈ T_D`.
  σ-strict-domination by `algebraMap t₀` gives `w(σ_loc) ≤
  w(algebraMap t₀)` strict; only constrains the σ_loc/t₀ ratio, not
  the t'/s_D ratio for general `t'`.

Neither branch closes the per-`t'` content from σ-strict-domination
alone — this is the genuine Wedhorn 8.34(ii) Route B residual. The
wrapper here packages the residual into a single hypothesis-shuffler.

The **`t' = algebraMap s_D` subcase** closes trivially by `vle_total`
(reflexivity), regardless of branch and σ-strict-domination structure.
Landed below as `WedhornMPowerStructuralDataHonest_t_eq_s_D_branch`.

## Single named residual

The unfactored per-`t'` chain on the local Spa:

```lean
theorem unfactored_per_t_chain_target
    [DecidableEq A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    -- Wedhorn 8.34(ii) Cor 7.32 structural data:
    -- (π_loc : ..., M : ℕ, hσ_loc_eq_pow : σ_loc = π_loc^(M+1), ...) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      ∀ τ ∈ localizedTestFamily s T_D s_D,
        w.vle (σ_loc : Localization.Away s) τ ∧
          ¬ w.vle τ (σ_loc : Localization.Away s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle t' (algebraMap A (Localization.Away s) s_D)
```

The proof of this residual is the genuinely-new Wedhorn 8.34(ii)
Route B content (cf. `WedhornMultiDominatingUnit.lean:234–304`'s
audit). This file's wrapper is callsite-ready packaging.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson /
  T001 / faithful-flatness / Zavyalov / bivariate-overlap / per-call
  C1 assembly content.
* No edits to Secondary's per-call assembly leaf, Primary assembly /
  root / final files.
* Reuses `WedhornMPowerStructuralDataHonest` (target def),
  `vle_iff_mul_unit_right` (σ-cancellation),
  `mem_localizedTestFamily_iff` (test-family branch case-split). -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Unfactored per-`t'` chain target** — the genuine Wedhorn 8.34(ii)
Route B per-`t'` content on the local Spa.

This `Prop`-valued definition packages the unfactored per-`t'` chain
hypothesis as a named target, ready to be plugged into
`WedhornMPowerStructuralDataHonest_via_unfactored_chain` (below). The
shape matches the natural per-`t'` Wedhorn content
`w.vle t' (algebraMap s_D)`, equivalent under σ-cancellation to the
σ-factored honest target.

Discharging this `Prop` is the genuine remaining residual; reductions
and consumers may treat it as the named single hypothesis. -/
def UnfactoredPerTChainTarget
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
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **σ-cancellation wrapper**: produce the honest σ-factored supplier
`WedhornMPowerStructuralDataHonest` from the named unfactored per-`t'`
chain target `UnfactoredPerTChainTarget`.

The unfactored chain is the natural Wedhorn 8.34(ii) per-`t'` content
(equivalent to the σ-factored target via `vle_iff_mul_unit_right` for
the unit `σ_loc`). This wrapper packages the residual into a single
caller-shaped hypothesis.

**Proof**: pointwise application of `vle_iff_mul_unit_right` (the
σ-cancellation iff). -/
theorem WedhornMPowerStructuralDataHonest_via_unfactored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain : UnfactoredPerTChainTarget P T s hopen T_D s_D σ_loc) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ t' ht'
  -- Apply σ-cancellation iff to convert unfactored ↔ σ-factored.
  exact (vle_iff_mul_unit_right w σ_loc t'
    (algebraMap A (Localization.Away s) s_D)).mpr
    (h_per_t_chain w hw_spa hw_f τ hτ hστ t' ht')

/-- **α_s_D-branch unfactored per-`t'` chain target**. Specialises
`UnfactoredPerTChainTarget` to the `τ = algebraMap s_D` branch of the
canonical localized test family. Matches the `h_per_t_chain` shape
consumed by `h_T_test_compat_loc_branch_α_s_D`
(`WedhornLocalCompatFromTestFamily.lean`). -/
def UnfactoredPerTChainBranchAlphaS_D
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
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle t' (algebraMap A (Localization.Away s) s_D)

/-- **α_T_D-branch unfactored per-`t'` chain target**. Specialises
`UnfactoredPerTChainTarget` to the `τ ∈ T_D.image algebraMap` branch
of the canonical localized test family. Matches the per-τ shape
needed by `h_T_test_compat_loc_branch_α_T_D`
(`WedhornLocalCompatFromTestFamily.lean`). -/
def UnfactoredPerTChainBranchAlphaT_D
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
  ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w.vle (σ_loc : Localization.Away s) τ ∧
        ¬ w.vle τ (σ_loc : Localization.Away s) →
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **Combiner: `UnfactoredPerTChainTarget` from per-branch chains**.

Discharges the unified `UnfactoredPerTChainTarget` from the two
per-branch chain hypotheses (α_s_D and α_T_D) by case-splitting on
`mem_localizedTestFamily_iff`.

Each branch's chain consumes the same `(w, hf, hστ_at_τ)` data with
τ-specialised σ-strict-domination, and outputs the per-`t'`
inequality `w.vle t' (algebraMap s_D)` for every t' ∈ T_D.image. The
combiner unifies them into the named target. -/
theorem UnfactoredPerTChainTarget_via_branches
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_α_s_D : UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc)
    (h_α_T_D : UnfactoredPerTChainBranchAlphaT_D P T s hopen T_D s_D σ_loc) :
    UnfactoredPerTChainTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f τ hτ hστ t' ht'
  -- Case-split on τ ∈ localizedTestFamily.
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- α_s_D branch.
    exact h_α_s_D w hw_spa hw_f hστ t' ht'
  · -- α_T_D branch.
    exact h_α_T_D τ hτ_in_T_D w hw_spa hw_f hστ t' ht'

/-- **Per-`t'` α_s_D-branch fact** — single-`t'` slice of
`UnfactoredPerTChainBranchAlphaS_D`.

Carries the single Wedhorn-content fact for one specific `t' ∈
T_D.image algebraMap`. The full branch chain is the conjunction of
this fact across all `t' ∈ T_D.image`. Used to break the residual
into per-`t'` pieces with explicit naming. -/
def UnfactoredPerTChainBranchAlphaS_DPerTFact
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (t' : Localization.Away s) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle ((σ_loc : Localization.Away s) *
        (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
      (algebraMap A (Localization.Away s) s) →
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    w.vle t' (algebraMap A (Localization.Away s) s_D)

omit [PlusSubring A] in
/-- **α_s_D branch trivial closure at `t' = algebraMap s_D`**.

The per-`t'` α_s_D-branch fact closes trivially at `t' = algebraMap s_D`
by `vle_total` reflexivity (regardless of `(w, hf, hστ)`).

This closes the `t' = algebraMap s_D` sub-piece of
`UnfactoredPerTChainBranchAlphaS_D` whenever `algebraMap s_D ∈
T_D.image algebraMap` (i.e., `s_D ∈ T_D` in the typical
`insertDenom`-normalised setup). -/
theorem UnfactoredPerTChainBranchAlphaS_DPerTFact_at_algebraMap_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) :
    UnfactoredPerTChainBranchAlphaS_DPerTFact
      P T s hopen T_D s_D σ_loc
      (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w _hw_spa _hw_f _hστ
  exact (w.vle_total _ _).elim id id

omit [PlusSubring A] in
/-- **α_s_D branch chain via per-`t'` facts**.

Combines per-`t'` α_s_D-branch facts (one for each `t' ∈ T_D.image
algebraMap`) into the full `UnfactoredPerTChainBranchAlphaS_D` branch
chain.

This is the per-`t'` decomposition: the branch chain is the
conjunction across all `t'` of the per-`t'` fact. The discharger
exposes per-`t'` granularity to the caller, which can then close
specific `t'`s (e.g., `t' = algebraMap s_D` via the trivial closure
above) and leave only the genuinely-residual `t'`s. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_per_t_facts
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        UnfactoredPerTChainBranchAlphaS_DPerTFact
          P T s hopen T_D s_D σ_loc t') :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  exact h_per_t t' ht' w hw_spa hw_f hστ

/-- **α_s_D M-power-decay structural target** — the per-`t'` Wedhorn
8.34(ii) M-power-decay structural fact for the α_s_D branch.

For each `(w, hf, hστ_α_s_D, t')`, gives the structural inequality
`w.vle (algebraMap s) (algebraMap s_D * σ_loc * ∏ erase t')`. This is
the natural shape of Wedhorn 8.34(ii)'s σ-power-decay output (cf.
the documented `subset_inequality_target` at
`WedhornDominatingBranchInequality.lean:104`); it carries the genuine
Wedhorn σ-power decay content but is **distinct** from
`AlphaS_DFactoredChainTarget`: the M-power-decay form is the inequality
chain through `algebraMap s`, whereas `AlphaS_DFactoredChainTarget`
is the σ-factored per-`t'` form. The two differ by cancellation of
`∏ erase t'` (per-`t'` non-vanishing condition). -/
def AlphaS_DMPowerDecayTarget
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
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (algebraMap A (Localization.Away s) s)
        (algebraMap A (Localization.Away s) s_D *
          (σ_loc : Localization.Away s) *
          (∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t))

/-- **α_s_D per-`t'` `∏ erase t'` non-vanishing target** — the algebraic
companion residual to `AlphaS_DMPowerDecayTarget`.

For each `(w, hf, hστ_α_s_D, t')`, asserts non-vanishing of
`∏ T_D.image α \ {t'}` at `w`. This is the cancellation condition
needed to extract the σ-factored chain from the M-power decay (via
`ValuativeRel.mul_vle_mul_iff_left`). -/
def AlphaS_DProdEraseNonVanishTarget
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
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      ¬ w.vle (∏ t ∈ (T_D.image
        (algebraMap A (Localization.Away s))).erase t', t) 0

/-- **σ-factored α_s_D-branch chain target** — the genuine Wedhorn
8.34(ii) Route B σ-power-decay residual for the α_s_D branch.

Matches the `h_factored` parameter shape of
`h_α_s_D_per_t_via_factored_chain` (`WedhornLocalArithmeticPerTChain.lean`):
the per-`t'` σ-factored inequality
`w.vle (t' * σ_loc) (algebraMap s_D * σ_loc)`
under f-membership and σ-strict-domination by `algebraMap s_D`. Carries
the genuine Wedhorn-content per-`t'` arithmetic; equivalent under
σ-cancellation to the unfactored α_s_D-branch chain. -/
def AlphaS_DFactoredChainTarget
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
    w.vle (σ_loc : Localization.Away s)
        (algebraMap A (Localization.Away s) s_D) ∧
      ¬ w.vle (algebraMap A (Localization.Away s) s_D)
        (σ_loc : Localization.Away s) →
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle (t' * (σ_loc : Localization.Away s))
        ((algebraMap A (Localization.Away s) s_D) *
          (σ_loc : Localization.Away s))

omit [PlusSubring A] in
/-- **α_s_D-branch chain via σ-factored chain residual**.

Closes `UnfactoredPerTChainBranchAlphaS_D` from the named σ-factored
chain residual `AlphaS_DFactoredChainTarget` via the existing
σ-cancellation reducer
`h_α_s_D_per_t_via_factored_chain` (`WedhornLocalArithmeticPerTChain.lean`).

This is the **strongest reduction** of the α_s_D branch chain
achievable from the existing σ-factored API: the residual hypothesis
is the genuine Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay content,
in the canonical σ-factored form matching Wedhorn's natural candidate
shape `f := σ_loc * (∏ T_D.image algebraMap)`. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_factored_chain
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_factored : AlphaS_DFactoredChainTarget P T s hopen T_D s_D σ_loc) :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc :=
  h_α_s_D_per_t_via_factored_chain P T s hopen T_D s_D σ_loc h_factored

omit [PlusSubring A] in
/-- **α_s_D factored chain via M-power decay + ∏-erase non-vanishing**.

Sharper reducer: closes `AlphaS_DFactoredChainTarget` from two
SEPARATED genuine Wedhorn-content residuals:

1. `AlphaS_DMPowerDecayTarget` — the σ-power-decay structural
   inequality chain through `algebraMap s` (the natural Cor 7.32 +
   compactness output).
2. `AlphaS_DProdEraseNonVanishTarget` — per-`t'` non-vanishing of
   `∏ T_D.image α \ {t'}` (the algebraic cancellation premise).

The proof chains f-membership through the M-power decay then cancels
`∏ erase t'` via `ValuativeRel.mul_vle_mul_iff_left`, after rewriting
products to expose the cancelled factor on both sides. -/
theorem AlphaS_DFactoredChainTarget_via_M_power_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_decay : AlphaS_DMPowerDecayTarget P T s hopen T_D s_D σ_loc)
    (h_erase_ne :
      AlphaS_DProdEraseNonVanishTarget P T s hopen T_D s_D σ_loc) :
    AlphaS_DFactoredChainTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ t' ht'
  have h_struct := h_decay w hw_spa hw_f hστ t' ht'
  have h_erase := h_erase_ne w hw_spa hw_f hστ t' ht'
  -- Notation shorthand.
  set α_s_D : Localization.Away s := algebraMap A (Localization.Away s) s_D
  set σ : Localization.Away s := (σ_loc : Localization.Away s)
  set Pi_full : Localization.Away s :=
    ∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t
  set Pi_erase : Localization.Away s :=
    ∏ t ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t', t
  -- Product split via `Finset.mul_prod_erase`.
  have h_prod_split : Pi_full = t' * Pi_erase :=
    (Finset.mul_prod_erase _ _ ht').symm
  -- Chain f-membership through the structural decay.
  have h_chain : w.vle (σ * Pi_full) (α_s_D * σ * Pi_erase) :=
    w.vle_trans hw_f h_struct
  -- Rewrite LHS with product split: σ * Pi_full = σ * (t' * Pi_erase) = (t' * σ) * Pi_erase.
  have h_LHS_eq : σ * Pi_full = (t' * σ) * Pi_erase := by
    rw [h_prod_split]; ring
  -- Rewrite RHS to expose Pi_erase factor on the right.
  have h_RHS_eq : α_s_D * σ * Pi_erase = (α_s_D * σ) * Pi_erase := by
    rw [mul_assoc]
  -- Apply rewrites.
  rw [h_LHS_eq, h_RHS_eq] at h_chain
  -- Cancel Pi_erase via mul_vle_mul_iff_left.
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  exact (ValuativeRel.mul_vle_mul_iff_left (z := Pi_erase) h_erase).mp h_chain

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Trivial subcase: `t' = algebraMap s_D`**.

When the per-`t'` quantifier ranges over `t' = algebraMap s_D` (which
happens iff `s_D ∈ T_D`), the σ-factored conclusion
`w.vle (algebraMap s_D * σ_loc) (algebraMap s_D * σ_loc)` is reflexive.

This subcase closes by `vle_total` regardless of the branch τ or
σ-strict-domination structure. Useful for `insertDenom`-normalised
covers where `s_D ∈ T_D` is enforced. -/
theorem WedhornMPowerStructuralDataHonest_t_eq_s_D_branch
    [DecidableEq A]
    (s : A) (s_D : A) (σ_loc : (Localization.Away s)ˣ)
    (w : Spv (Localization.Away s)) :
    w.vle ((algebraMap A (Localization.Away s) s_D) *
        (σ_loc : Localization.Away s))
      ((algebraMap A (Localization.Away s) s_D) *
        (σ_loc : Localization.Away s)) :=
  (w.vle_total _ _).elim id id

end ValuationSpectrum
