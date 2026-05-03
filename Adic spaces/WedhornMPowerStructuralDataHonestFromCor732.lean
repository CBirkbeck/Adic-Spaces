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

/-- **Spa-uniform σ-power-decay** for the localized α_s_D branch.

Captures the genuine Wedhorn 8.34(ii) σ-power-decay output in its
natural shape: a single power of `algebraMap s_D` controlled by the
cardinality of the `algebraMap`-image of `T_D`. Concretely:

`∀ w ∈ Spa, w.vle (algebraMap s) (σ_loc * (algebraMap s_D) ^ |T_D.image|)`.

This is the natural Cor 7.32 + `Spa`-compactness M-choice output (cf.
`WedhornFactorExtractionPowerDecay.lean:144-163` and
`WedhornSigmaPowerDecay.lean:51-78`); it is **strictly closer to
Cor 7.32** than `AlphaS_DMPowerDecayTarget` since the RHS is a single
power, not a per-`t'` `∏ erase` product. -/
def AlphaS_DUniformSigmaPowerDecay
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
    w.vle (algebraMap A (Localization.Away s) s)
      ((σ_loc : Localization.Away s) *
        (algebraMap A (Localization.Away s) s_D) ^
          (T_D.image (algebraMap A (Localization.Away s))).card)

/-- **`s_D`-lower-bound on `T_D.image \ {t'}`** — algebraic cancellation
premise needed to exchange a single `(algebraMap s_D)`-power for the
per-`t'` `∏ erase t'` shape.

For each `(w, t', t'')` with `t' ∈ T_D.image` and `t'' ∈ erase t'`,
asserts `w.vle (algebraMap s_D) t''`. Lifting pointwise via
`Spv.vle_prod_of_pointwise` then yields
`w.vle ((algebraMap s_D)^|erase t'|) (∏ erase t')`, the cancellation
step that bridges the σ-power-decay shape to the M-power-decay target. -/
def AlphaS_DProdEraseLowerBound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      ∀ t'' ∈ (T_D.image (algebraMap A (Localization.Away s))).erase t',
        w.vle (algebraMap A (Localization.Away s) s_D) t''

omit [PlusSubring A] in
/-- **`AlphaS_DMPowerDecayTarget` via Spa-uniform σ-power-decay +
`s_D`-lower-bound**. The genuine sharper reducer.

Takes two SEPARATED inputs strictly closer to Cor 7.32:

1. `AlphaS_DUniformSigmaPowerDecay` — Spa-uniform σ-power-decay shape
   `w.vle (algebraMap s) (σ_loc * (algebraMap s_D) ^ |T_D.image|)`,
   matching the natural Cor 7.32 σ-construction + Spa-compactness
   M-choice output (single power form).
2. `AlphaS_DProdEraseLowerBound` — pointwise `w.vle (algebraMap s_D) t''`
   for `t'' ∈ T_D.image.erase t'`, the algebraic cancellation premise.

The proof:
* Lift the lower bound via `Spv.vle_prod_of_pointwise`:
  `w.vle ((algebraMap s_D) ^ (|T_D.image| - 1)) (∏ erase t')`.
* Multiply by `algebraMap s_D * σ_loc` on the left:
  `w.vle (σ_loc * (algebraMap s_D) ^ |T_D.image|)
    (algebraMap s_D * σ_loc * ∏ erase t')`
  (using `s_D * s_D^(c-1) = s_D^c` and ring commutativity).
* Chain through the σ-power-decay via `vle_trans`. -/
theorem AlphaS_DMPowerDecayTarget_via_uniform_decay_and_lower_bound
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_decay : AlphaS_DUniformSigmaPowerDecay P T s hopen T_D s_D σ_loc)
    (h_lower : AlphaS_DProdEraseLowerBound P T s hopen T_D s_D) :
    AlphaS_DMPowerDecayTarget P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa _hw_f _hστ t' ht'
  letI : ValuativeRel (Localization.Away s) := w.toValuativeRel
  -- Local notation for the carriers in `Localization.Away s`.
  set imgT := T_D.image (algebraMap A (Localization.Away s)) with himgT_def
  set sD : Localization.Away s := algebraMap A (Localization.Away s) s_D
    with hsD_def
  set σL : Localization.Away s := (σ_loc : Localization.Away s) with hσL_def
  -- Step 1: Lift `h_lower` to a product lower bound on `imgT.erase t'`.
  have h_lower_at : ∀ t'' ∈ imgT.erase t', w.vle sD t'' :=
    h_lower w hw_spa t' ht'
  have h_prod_lift :
      w.vle (∏ _t ∈ imgT.erase t', sD) (∏ t ∈ imgT.erase t', t) :=
    Spv.vle_prod_of_pointwise w (imgT.erase t') h_lower_at
  -- Replace the constant product by a power and the cardinality by `c - 1`.
  have h_const_prod :
      (∏ _t ∈ imgT.erase t', sD) = sD ^ (imgT.erase t').card := by
    simp [Finset.prod_const]
  have h_card_erase : (imgT.erase t').card = imgT.card - 1 :=
    Finset.card_erase_of_mem ht'
  rw [h_const_prod, h_card_erase] at h_prod_lift
  -- Step 2: Multiply both sides by `sD * σL` on the LEFT.
  have h_prod_mul :
      w.vle ((sD * σL) * sD ^ (imgT.card - 1))
            ((sD * σL) * (∏ t ∈ imgT.erase t', t)) :=
    ValuativeRel.mul_vle_mul_right h_prod_lift (sD * σL)
  -- Step 3: Rewrite LHS as `σL * sD ^ imgT.card` using `pow_succ'` + `ring`.
  have h_card_pos : 1 ≤ imgT.card := Finset.card_pos.mpr ⟨t', ht'⟩
  have h_pow_split : sD ^ imgT.card = sD * sD ^ (imgT.card - 1) := by
    conv_lhs =>
      rw [show imgT.card = imgT.card - 1 + 1 from
        (Nat.sub_add_cancel h_card_pos).symm]
    exact pow_succ' sD (imgT.card - 1)
  have h_lhs_eq : (sD * σL) * sD ^ (imgT.card - 1) = σL * sD ^ imgT.card := by
    rw [h_pow_split]; ring
  rw [h_lhs_eq] at h_prod_mul
  -- Step 4: Chain `h_decay` (giving `s ≤ σL * sD ^ imgT.card`) through `h_prod_mul`.
  have h_decay_at :
      w.vle (algebraMap A (Localization.Away s) s)
        (σL * sD ^ imgT.card) := h_decay w hw_spa
  exact w.vle_trans h_decay_at h_prod_mul

/-- **Spa-uniform π-power-decay** — the Cor 7.32-internal, π-power form
of `AlphaS_DUniformSigmaPowerDecay`. Captures the natural pseudo-
uniformizer-power output of `Cor732.exists_dominating_unit` (whose
internal construction sets `s := π^(N+1)` per `Cor732.lean:225`):

`∀ w ∈ Spa, w.vle (algMap s)
  ((π_loc : Localization.Away s) ^ (M+1) * (algMap s_D) ^ |T_D.image|)`.

The element `π_loc : locSubring P T s` is a member of the localized
ring of definition `D = A₀[t₁/s, …, tₙ/s]`, definitionally equal to
`(locPairOfDefinition P T s hopen).A₀`; its image
`(π_loc : Localization.Away s)` plays the role of the pseudo-
uniformizer-power-base. The interpretation as a pseudo-uniformizer is
conveyed by the companion σ-as-π-power equation
`(σ_loc : Localization.Away s) = (π_loc : Localization.Away s) ^ (M + 1)`
(see `AlphaS_DUniformSigmaPowerDecay_via_pi_power`).

This is **strictly closer to Cor 7.32** than `AlphaS_DUniformSigmaPowerDecay`
since it expresses the σ-factor as an explicit pseudo-uniformizer power
`π_loc^(M+1)`, exposing the σ-as-π-power identification internal to
Cor 7.32's construction. The genuine Wedhorn 8.34(ii) M-choice content
is now isolated as the Spa-uniform inequality with `π_loc^(M+1) * s_D^k`
on the RHS, ready for a Spa-quasicompactness + topological-nilpotence
discharge in a future ticket. -/
def AlphaS_DUniformPiPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (π_loc : locSubring P T s) (M : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    w.vle (algebraMap A (Localization.Away s) s)
      ((π_loc : Localization.Away s) ^ (M + 1) *
        (algebraMap A (Localization.Away s) s_D) ^
          (T_D.image (algebraMap A (Localization.Away s))).card)

omit [PlusSubring A] in
/-- **`AlphaS_DUniformSigmaPowerDecay` via π-power decay + σ-as-π-power
identification**. Sharper supplier whose remaining assumptions are
exactly the **exposed Cor 7.32 σ-construction data**:

* `hσ_loc_eq_pow` — σ-as-π-power identification:
  `(σ_loc : Localization.Away s) = (π_loc : Localization.Away s) ^ (M + 1)`,
  the σ-construction internal to `Cor732.exists_dominating_unit`
  (where `s := π^(N+1)` per `Cor732.lean:225`); the natural choice
  for `π_loc : locSubring P T s` is the lift `algebraMapD P T s π̃` of
  a global pseudo-uniformizer `π̃ : P.A₀`.
* `AlphaS_DUniformPiPowerDecay P T s hopen T_D s_D π_loc M` — Spa-uniform
  M-choice in π-power form, the Spa-quasicompactness +
  topological-nilpotence input residual.

The π_loc parameter is `locSubring P T s` (which is definitionally
`(locPairOfDefinition P T s hopen).A₀`); using `locSubring` directly
keeps the binder type free of `TopologicalSpace`-instance dependencies.

The proof: substitute `(σ_loc : Localization.Away s)` by
`(π_loc : Localization.Away s) ^ (M + 1)` in the goal via `hσ_loc_eq_pow`,
then apply the π-power decay residual at `w`. The genuine Cor 7.32
σ-construction data is now decomposed into the algebraic σ-as-π-power
equation (internal to Cor 7.32) and the analytic π-power Spa-uniform
decay (the next-step residual). -/
theorem AlphaS_DUniformSigmaPowerDecay_via_pi_power
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (π_loc : locSubring P T s) (M : ℕ)
    (hσ_loc_eq_pow :
      (σ_loc : Localization.Away s) =
        (π_loc : Localization.Away s) ^ (M + 1))
    (h_pi_decay : AlphaS_DUniformPiPowerDecay P T s hopen T_D s_D π_loc M) :
    AlphaS_DUniformSigmaPowerDecay P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa
  rw [hσ_loc_eq_pow]
  exact h_pi_decay w hw_spa

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

/-- **Per-`t'` Wedhorn σ-power-decay residual at the `α s_D`
specialisation**. Bundled named residual carrying the genuinely-new
Wedhorn 8.34(ii) Route B content for the α_s_D branch in the
**classical Wedhorn shape** (single-`t'` candidate `σ_loc * t' *
(α s_D)^N`).

For each `(w, t')` with `w ∈ Spa(Loc s, ⁺)` and
`t' ∈ T_D.image (algebraMap A (Loc s))`:

* the per-`t'` Wedhorn chain through `α s`:
  `w.vle ((σ_loc : Loc s) * t' * (algebraMap A (Loc s) s_D)^N) (algebraMap A (Loc s) s)`;
* the σ-power-decay at `α s` (Wedhorn's Spa-quasi-compactness M-choice):
  `w.vle (algebraMap A (Loc s) s) ((σ_loc : Loc s) * (algebraMap A (Loc s) s_D)^(N+1))`.

Both pieces follow Wedhorn's joint σ + N construction (Cor 7.32 σ +
compactness N-choice). The exponent `N : ℕ` is the Wedhorn N parameter,
chosen via Spa-quasi-compactness so that `σ_loc * (algMap s_D)^(N+1)`
uniformly bounds `algMap s` from above on Spa.

## Why localized Cor 7.32 strict domination is insufficient

Cor 7.32 (`exists_dominating_unit`) outputs only the σ-strict-domination
shape `w(σ_loc) ≤ w(τ_w)` strict — see the explicit warning at
`WedhornSigmaPowerDecay.lean:14-22` flagging that the σ-power-decay
shape requires the OPPOSITE valuation orientation
(`w(α s) ≤ w(σ_loc * (α s_D)^(N+1))`, σ "large from below" times an
`α s_D`-power). The Wedhorn discharge route uses σ_loc as a π-power
(internal to `Cor732.exists_dominating_unit`'s `s := π^(N+1)` at
`Cor732.lean:225`), N chosen via `exists_dominatedBy_cover` for
Spa-quasi-compactness, plus topological-nilpotence of π. None of this
is exposed by Cor 7.32's output type. -/
def AlphaS_DBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle ((σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s) ∧
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **Sharper alternative path to `UnfactoredPerTChainBranchAlphaS_D`
via the abstract Wedhorn algebraic core**.

Bypasses the M-power-decay structural form (`AlphaS_DMPowerDecayTarget`
+ `AlphaS_DProdEraseLowerBound`) and consumes the SINGLE bundled
per-`t'` Wedhorn σ-power-decay residual `AlphaS_DBranchPerTSigmaPowerDecay`,
proving `UnfactoredPerTChainBranchAlphaS_D` directly via the abstract
algebraic core `vle_t_D_s_of_sigma_decay_chain_at` from
`WedhornMultiBranchSubsetInequality.lean`.

The α s_D non-vanishing premise is auto-derived from σ-strict-domination
via `not_vle_zero_of_strict_dominator` (the strict half of
α_s_D-branch σ-strict-domination forces `α s_D` to not vanish at `w`).

**This leaves exactly ONE named residual**:
`AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`,
the Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay content (with N
chosen via Spa-quasi-compactness / topological-nilpotence of σ_loc).

## Valuation-orientation handoff

The localized Cor 7.32 σ-strict-domination output (per
`WedhornLocalizedCor732Consumer.lean`) supplies σ_loc with
σ-strict-domination over `localizedTestFamily s T_D s_D`. It does
**not** supply `AlphaS_DBranchPerTSigmaPowerDecay`:

* The σ-power-decay component requires the OPPOSITE orientation
  `w(α s) ≤ w(σ_loc * (α s_D)^(N+1))` from Cor 7.32's σ-strict-dom
  `w(σ_loc) ≤ w(τ_w)` strict — see `WedhornSigmaPowerDecay.lean:14-22`.
* The per-`t'` chain `w(σ_loc * t' * (α s_D)^N) ≤ w(α s)` is the
  per-`t'` slice of Wedhorn 8.34(ii) Step 2's denominator-clearing
  ratio choice, also outside Cor 7.32's output.
* Wedhorn's discharge uses Spa-quasi-compactness M-choice for
  topologically-nilpotent π_loc with σ_loc = π_loc^(M+1), per
  `Cor732.lean:225` and `WedhornFactorExtractionPowerDecay.lean:144-163`. -/
theorem UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_residual :
      AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    UnfactoredPerTChainBranchAlphaS_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa _hw_f hστ t' ht'
  have hα_s_D_ne :
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
    not_vle_zero_of_strict_dominator hστ.2
  obtain ⟨h_chain_t', h_C_decay⟩ := h_residual w hw_spa t' ht'
  exact vle_t_D_s_of_sigma_decay_chain_at w N hα_s_D_ne h_chain_t' h_C_decay

/-- **Per-(τ, t') Wedhorn σ-power-decay residual at the `α_T_D`
specialisation**. Bundled named residual analogous to
`AlphaS_DBranchPerTSigmaPowerDecay`, indexed by the dominating
`τ ∈ T_D.image (algebraMap A (Localization.Away s))` (the α_T_D
branch's σ-strict-dominator).

For each `(τ, w, t')` with `τ, t' ∈ T_D.image (algebraMap)` and
`w ∈ Spa(Loc s, ⁺)`:

* `α s_D` non-vanishing at `w`:
  `¬ w.vle (algebraMap A (Loc s) s_D) 0` — this is **not** auto-derivable
  from `hστ` in the α_T_D branch (since the strict dominator is `τ`,
  not `α s_D`), so it is included as part of the bundled residual;
* the per-`t'` Wedhorn chain through `α s`:
  `w.vle ((σ_loc : Loc s) * t' * (algebraMap A (Loc s) s_D)^N) (algebraMap A (Loc s) s)`;
* the σ-power-decay at `α s`:
  `w.vle (algebraMap A (Loc s) s) ((σ_loc : Loc s) * (algebraMap A (Loc s) s_D)^(N+1))`.

The chain and decay components are τ-independent algebraically (they
involve only `σ_loc`, `t'`, `α s`, `α s_D`) but the residual is
τ-indexed for symmetry with `UnfactoredPerTChainBranchAlphaT_D`'s
per-τ structure: the user may discharge the conjunction at each τ
independently if needed.

## Why localized Cor 7.32 strict domination is insufficient

Same valuation-orientation considerations as
`AlphaS_DBranchPerTSigmaPowerDecay`: σ-power-decay requires the
OPPOSITE orientation to Cor 7.32's σ-strict-domination (per
`WedhornSigmaPowerDecay.lean:14-22`); discharge requires
Spa-quasicompactness M-choice for topologically-nilpotent π_loc with
σ_loc = π_loc^(M+1). Additionally, the α_T_D branch needs explicit
`α s_D` non-vanishing data since the branch's σ-strict-dominator is
some `τ ∈ T_D.image`, not `α s_D` itself. -/
def AlphaT_DBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  ∀ τ ∈ T_D.image (algebraMap A (Localization.Away s)),
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 ∧
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle ((σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) ∧
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))

omit [PlusSubring A] in
/-- **`UnfactoredPerTChainBranchAlphaT_D` via the abstract Wedhorn
algebraic core**. Symmetric counterpart to
`UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay` for the
α_T_D branch.

Consumes the bundled `AlphaT_DBranchPerTSigmaPowerDecay` residual
(carrying per-(τ, w, t') the chain + decay + α s_D non-vanishing) and
applies the abstract algebraic core `vle_t_D_s_of_sigma_decay_chain_at`
per `t'` for each branch dominator τ.

Unlike the α_s_D path, α s_D non-vanishing is **not** auto-derived from
σ-strict-domination here (since the strict dominator is some
`τ ∈ T_D.image`, not `α s_D`); it is read off the bundled residual.

**Leaves exactly ONE named residual**:
`AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`. -/
theorem UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_residual :
      AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    UnfactoredPerTChainBranchAlphaT_D P T s hopen T_D s_D σ_loc := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ_mem w hw_spa _hw_f _hστ t' ht'
  obtain ⟨hα_s_D_ne, h_per_t⟩ := h_residual τ hτ_mem w hw_spa
  obtain ⟨h_chain_t', h_C_decay⟩ := h_per_t t' ht'
  exact vle_t_D_s_of_sigma_decay_chain_at w N hα_s_D_ne h_chain_t' h_C_decay

omit [PlusSubring A] in
/-- **Top-level honest-supplier wrapper via classical σ-decay residuals
for both branches**.

Composes the two branch theorems:

* `UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay` for
  the α_s_D branch (consuming `AlphaS_DBranchPerTSigmaPowerDecay`);
* `UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay` for
  the α_T_D branch (consuming `AlphaT_DBranchPerTSigmaPowerDecay`);

with the existing combiners
`UnfactoredPerTChainTarget_via_branches` and
`WedhornMPowerStructuralDataHonest_via_unfactored_chain`, producing
the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from the two bundled per-branch
σ-power-decay residuals (sharing a common Wedhorn N).

**Leaves exactly TWO named residuals** (one per branch of the localized
canonical test family):

* `AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`
* `AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N`

Both are the genuine Wedhorn 8.34(ii) Route B per-`t'` σ-power-decay
content; see the per-branch theorems' docstrings for the
valuation-orientation handoff explaining why localized Cor 7.32
σ-strict-domination is insufficient. -/
theorem WedhornMPowerStructuralDataHonest_via_classical_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_α_s_D :
      AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N)
    (h_α_T_D :
      AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_unfactored_chain P T s hopen
    T_D s_D σ_loc
    (UnfactoredPerTChainTarget_via_branches P T s hopen T_D s_D σ_loc
      (UnfactoredPerTChainBranchAlphaS_D_via_classical_sigma_decay
        P T s hopen T_D s_D σ_loc N h_α_s_D)
      (UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay
        P T s hopen T_D s_D σ_loc N h_α_T_D))

/-! ### Joint Wedhorn σ-power-decay supplier (T154)

Single bundled named residual unifying both `AlphaS_DBranchPerTSigmaPowerDecay`
and `AlphaT_DBranchPerTSigmaPowerDecay` into a common joint supplier.

Audit observation justifying the unification: the consumer
`UnfactoredPerTChainBranchAlphaT_D_via_classical_sigma_decay` (above)
introduces the per-`τ` quantifier of `AlphaT_DBranchPerTSigmaPowerDecay`
but does **not** consume the per-`τ` σ-strict-domination data — only the
chain + decay + `α s_D` non-vanishing payload (which is τ-independent).
The per-`τ` quantifier of `AlphaT_D` is therefore redundant downstream;
the joint supplier replaces it with a single uniform `α s_D`
non-vanishing on `Spa(Localization.Away s, ⁺)`.

Concretely, the joint supplier carries:

* a uniform `α s_D` non-vanishing on the local Spa
  (the sole piece distinguishing `AlphaT_D` from `AlphaS_D` after the
  redundant per-`τ` quantifier is dropped);
* the per-(`w`, `t'`) Wedhorn 8.34(ii) Route B chain + decay payload
  (shared verbatim with `AlphaS_DBranchPerTSigmaPowerDecay`).

Both branch residuals extract trivially from the joint supplier (see
`AlphaS_DBranchPerTSigmaPowerDecay_via_joint` and
`AlphaT_DBranchPerTSigmaPowerDecay_via_joint`); composed with
`WedhornMPowerStructuralDataHonest_via_classical_sigma_decay`, this
gives a top-level honest σ-factored structural supplier consuming only
the joint residual (`WedhornMPowerStructuralDataHonest_via_joint_sigma_decay`).

The remaining mathematical content collapses to a single theorem-level
target: `AlphaJointBranchPerTSigmaPowerDecay`, with the genuine Wedhorn
8.34(ii) Step 2 N-choice / σ-as-π-power content identified as the per-(w, t')
chain and per-w decay pieces, plus the rational-subset-structure
`α s_D` non-vanishing piece (separable via
`AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces` below).
-/

/-- **Joint Wedhorn σ-power-decay supplier** — single bundled named
residual unifying the two branch residuals `AlphaS_DBranchPerTSigmaPowerDecay`
and `AlphaT_DBranchPerTSigmaPowerDecay`.

Carries:

* `(∀ w ∈ Spa, ¬ w.vle (algebraMap A (Loc s) s_D) 0)` — uniform `α s_D`
  non-vanishing on `Spa(Localization.Away s, ⁺)`;
* `(∀ w ∈ Spa, ∀ t' ∈ T_D.image (algebraMap A (Loc s)),
    chain_t' w ∧ decay w)` — per-(w, t') Wedhorn 8.34(ii) chain + decay.

The two branch residuals trivially extract from this joint supplier.
The remaining mathematical content reduces to a single
theorem-level target. -/
def AlphaJointBranchPerTSigmaPowerDecay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ) : Prop :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) ∧
  (∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle ((σ_loc : Localization.Away s) * t' *
            (algebraMap A (Localization.Away s) s_D) ^ N)
          (algebraMap A (Localization.Away s) s) ∧
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))

omit [PlusSubring A] in
/-- **Reducer: `AlphaS_DBranchPerTSigmaPowerDecay` from joint supplier**.

Trivial extraction: the joint supplier's chain+decay component is
literally `AlphaS_DBranchPerTSigmaPowerDecay` by definition. -/
theorem AlphaS_DBranchPerTSigmaPowerDecay_via_joint
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    AlphaS_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N :=
  h_joint.2

omit [PlusSubring A] in
/-- **Reducer: `AlphaT_DBranchPerTSigmaPowerDecay` from joint supplier**.

The per-`τ` quantifier of `AlphaT_DBranchPerTSigmaPowerDecay` is
redundant: the inner payload (`α s_D` non-vanishing + per-`t'` chain
+ decay) is τ-independent, so the joint supplier suffices. The
extraction introduces τ vacuously and assembles the conjunction from
the joint's two components. -/
theorem AlphaT_DBranchPerTSigmaPowerDecay_via_joint
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    AlphaT_DBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ _hτ w hw_spa
  exact ⟨h_joint.1 w hw_spa, fun t' ht' => h_joint.2 w hw_spa t' ht'⟩

omit [PlusSubring A] in
/-- **Top-level honest supplier from joint residual** — uniform-N
consumer.

Composes `AlphaS_DBranchPerTSigmaPowerDecay_via_joint` and
`AlphaT_DBranchPerTSigmaPowerDecay_via_joint` with the existing
`WedhornMPowerStructuralDataHonest_via_classical_sigma_decay`,
producing the top-level honest σ-factored structural supplier
`WedhornMPowerStructuralDataHonest` from the **single** joint
`AlphaJointBranchPerTSigmaPowerDecay` residual.

This is the cleanest end-to-end consumer signature for downstream
Wedhorn 8.34(ii) callers: only the joint residual remains as the single
named mathematical target. -/
theorem WedhornMPowerStructuralDataHonest_via_joint_sigma_decay
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_joint :
      AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N) :
    WedhornMPowerStructuralDataHonest P T s hopen T_D s_D σ_loc :=
  WedhornMPowerStructuralDataHonest_via_classical_sigma_decay
    P T s hopen T_D s_D σ_loc N
    (AlphaS_DBranchPerTSigmaPowerDecay_via_joint
      P T s hopen T_D s_D σ_loc N h_joint)
    (AlphaT_DBranchPerTSigmaPowerDecay_via_joint
      P T s hopen T_D s_D σ_loc N h_joint)

omit [PlusSubring A] in
/-- **Three-piece structural decomposition of the joint residual** —
splits `AlphaJointBranchPerTSigmaPowerDecay` into three independent atomic
Lean targets, decoupling the genuine Wedhorn 8.34(ii) Step 2 content from
the rational-subset-structure non-vanishing piece:

1. `h_nv` — `α s_D` non-vanishing uniform on `Spa(Localization.Away s, ⁺)`
   (rational-subset-structure / global hypothesis);
2. `h_chain` — per-(w, t') σ-factored chain
   `w.vle (σ_loc * t' * (α s_D)^N) (α s)` (Wedhorn f-membership content,
   N-choice for σ * t' clearing);
3. `h_decay` — per-w σ-power decay
   `w.vle (α s) (σ_loc * (α s_D)^(N+1))` (Wedhorn 8.34(ii) Step 2
   N-choice for the backward bound).

Each piece is a standalone target ready to be discharged via its own
dedicated mathematical content — pieces (2) and (3) carry the genuine
Wedhorn 8.34(ii) Step 2 N-choice / σ-as-π-power material. -/
theorem AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_nv :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0)
    (h_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle ((σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N)
            (algebraMap A (Localization.Away s) s))
    (h_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) :
    AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  refine ⟨h_nv, ?_⟩
  intro w hw_spa t' ht'
  exact ⟨h_chain w hw_spa t' ht', h_decay w hw_spa⟩

omit [PlusSubring A] in
/-- **Joint residual via chain + decay + `IsUnit` `α s_D`**.

Strengthened constructor for the joint residual that auto-derives the
`α s_D` non-vanishing piece from `IsUnit (algebraMap A (Loc s) s_D)`.

Useful when `s_D` is a unit in `A` (or more generally when its image in
`Localization.Away s` is a unit), removing one of the three named
pieces. The remaining pieces are the genuine Wedhorn 8.34(ii) Step 2
content. -/
theorem AlphaJointBranchPerTSigmaPowerDecay_via_chain_decay_and_unit_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ) (N : ℕ)
    (h_unit_s_D : IsUnit (algebraMap A (Localization.Away s) s_D))
    (h_chain :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle ((σ_loc : Localization.Away s) * t' *
              (algebraMap A (Localization.Away s) s_D) ^ N)
            (algebraMap A (Localization.Away s) s))
    (h_decay :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle (algebraMap A (Localization.Away s) s)
          ((σ_loc : Localization.Away s) *
            (algebraMap A (Localization.Away s) s_D) ^ (N + 1))) :
    AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N :=
  AlphaJointBranchPerTSigmaPowerDecay_via_three_pieces
    P T s hopen T_D s_D σ_loc N
    (fun w _ => not_vle_zero_of_isUnit h_unit_s_D w)
    h_chain h_decay

/-! ### Remaining single mathematical statement (T154 fallback target)

After the joint reduction landed in this section, the mathematical
content reduces to discharging
`AlphaJointBranchPerTSigmaPowerDecay P T s hopen T_D s_D σ_loc N` —
i.e., producing the per-(w, t') chain + decay pair plus the `α s_D`
non-vanishing on `Spa(Localization.Away s, ⁺)` — which is the
**genuine Wedhorn 8.34(ii) Step 2 N-choice content** (σ-as-π-power
identification + Spa-quasi-compactness M-choice for topologically
nilpotent π_loc + denominator-clearing N).

Concretely, the residual to be discharged is the conjunction recorded in
`AlphaJointBranchPerTSigmaPowerDecay`:

```
(∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) ∧
(∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
    ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
      w.vle ((σ_loc : Localization.Away s) * t' *
          (algebraMap A (Localization.Away s) s_D) ^ N)
        (algebraMap A (Localization.Away s) s) ∧
      w.vle (algebraMap A (Localization.Away s) s)
        ((σ_loc : Localization.Away s) *
          (algebraMap A (Localization.Away s) s_D) ^ (N + 1)))
```

Discharge route: take `π_loc : (locPairOfDefinition P T s hopen).A₀`
topologically nilpotent (with `(locPairOfDefinition P T s hopen).I =
Ideal.span {π_loc}`, etc.), choose `σ_loc = π_loc^(M+1)` and `N` via
`Cor732.exists_dominatedBy_cover` applied to a sufficiently rich test
family on the local Spa. -/

end ValuationSpectrum
