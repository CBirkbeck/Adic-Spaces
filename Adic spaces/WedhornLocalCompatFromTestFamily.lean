/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornLocalPerBranchChain
import «Adic spaces».WedhornLocalizedCor732Application
import «Adic spaces».WedhornMultiDominatingUnit

/-!
# Wedhorn local-compatibility from canonical test family

Defines the canonical localized Wedhorn 8.34(ii) test family
`T_test_loc := insert (algebraMap s_D) (T_D.image algebraMap)` on
`Localization.Away s` and lands the per-branch compatibility theorems
needed to consume `rationalOpen_subset_base_via_local_Cor732_chain`
(commit `4197d87`).

## Strategy

The Wedhorn 8.34(ii) σ-construction uses a finite test family
`T_test_loc` on the localized Spa. The natural canonical choice is

`T_test_loc := insert (algebraMap s_D) (T_D.image algebraMap)`

— the image of `T_D` plus the `algebraMap` of the cover-piece
denominator `s_D`. With this choice, the σ-strict-domination output of
`exists_dominating_unit_in_localization` (commit accepted upstream)
gives, at every `w ∈ Spa(A_loc, locSubring)`:

* either `τ = algebraMap s_D` (the **`α_s_D` branch**),
* or `τ ∈ T_D.image algebraMap` (the **`α_T_D` branches**).

The `¬ w.vle (algebraMap s_D) 0` half of the per-branch conclusion
**discharges automatically** in the `α_s_D` branch via
`not_vle_zero_of_strict_dominator` (`WedhornMultiDominatingUnit.lean:189`).
For the `α_T_D` branches, both halves are taken as explicit inputs;
that is the genuine Wedhorn-content residual at this lane.

## What this file provides

* `localizedTestFamily` — the canonical test family
  `insert (algebraMap s_D) (T_D.image algebraMap)` on
  `Localization.Away s`.

* `h_T_test_compat_loc_branch_α_s_D` — single-branch compatibility for
  `τ = algebraMap s_D`. The `¬ w.vle (algebraMap s_D) 0` half is
  automatic; the per-`t'` half is the explicit input.

* `h_T_test_compat_loc_branch_α_T_D` — single-branch compatibility for
  `τ ∈ T_D.image algebraMap`. Both per-`t'` and `¬ w.vle (algebraMap s_D) 0`
  halves are explicit inputs.

* `h_T_test_compat_loc_canonical` — combined compatibility for the
  canonical test family `localizedTestFamily`, dispatching on the
  branch via `Finset.mem_insert`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness / Zavyalov / bivariate-overlap content.
* Reuses `not_vle_zero_of_strict_dominator`
  (`WedhornMultiDominatingUnit.lean:189`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Canonical localized test family for Wedhorn 8.34(ii)**:
`insert (algebraMap s_D) (T_D.image algebraMap)` on `Localization.Away s`.

The natural test family for the σ-construction at the localization:
contains the `algebraMap`-image of every `t ∈ T_D` (for the test family's
"main" branch) plus `algebraMap s_D` (for the cover-piece-denominator
branch). Used as `T_test_loc` in
`rationalOpen_subset_base_via_local_Cor732_chain`. -/
noncomputable def localizedTestFamily
    (s : A) (T_D : Finset A) (s_D : A) : Finset (Localization.Away s) :=
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  insert (algebraMap A (Localization.Away s) s_D)
    (T_D.image (algebraMap A (Localization.Away s)))

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- Membership lemma for `localizedTestFamily`: an element belongs
either via the `algebraMap s_D` slot or via `T_D.image`. -/
theorem mem_localizedTestFamily_iff
    (s : A) (T_D : Finset A) (s_D : A) (x : Localization.Away s) :
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    x ∈ localizedTestFamily s T_D s_D ↔
      x = algebraMap A (Localization.Away s) s_D ∨
      x ∈ T_D.image (algebraMap A (Localization.Away s)) := by
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  unfold localizedTestFamily
  exact Finset.mem_insert

omit [PlusSubring A] in
/-- **Single-branch compatibility for `τ = algebraMap s_D`**.

The `¬ w.vle (algebraMap s_D) 0` half is **discharged automatically**
via `not_vle_zero_of_strict_dominator`: strict σ-domination of
`algebraMap s_D` (i.e., `¬ w.vle (algebraMap s_D) (σ_loc : _)`) implies
`¬ w.vle (algebraMap s_D) 0`. The per-`t'` half is the explicit
Wedhorn-content residual at this branch. -/
theorem h_T_test_compat_loc_branch_α_s_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain :
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
          w.vle t' (algebraMap A (Localization.Away s) s_D)) :
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
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
            w.vle t' (algebraMap A (Localization.Away s) s_D)) ∧
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f hστ
  exact ⟨h_per_t_chain w hw_spa hw_f hστ,
    not_vle_zero_of_strict_dominator hστ.2⟩

omit [PlusSubring A] in
/-- **Single-branch compatibility for `τ ∈ T_D.image algebraMap`**.

For the `α_T_D` branches, both per-`t'` and `¬ w.vle (algebraMap s_D) 0`
halves are taken as explicit inputs; neither is automatic from
σ-strict-domination at this τ alone. -/
theorem h_T_test_compat_loc_branch_α_T_D
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_t_chain :
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
            w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_per_α_T_D_s_D_ne :
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
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
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
  intro τ hτ w hw_spa hw_f hστ
  exact ⟨h_per_t_chain τ hτ w hw_spa hw_f hστ,
    h_per_α_T_D_s_D_ne τ hτ w hw_spa hw_f hστ⟩

omit [PlusSubring A] in
/-- **Combined canonical compatibility theorem** — composes the two
branch compatibility theorems above to produce a `h_T_test_compat_loc`
witness for the canonical test family `localizedTestFamily s T_D s_D`,
ready for direct consumption by
`rationalOpen_subset_base_via_local_Cor732_chain`.

The per-branch chain hypotheses are split: one for the `α_s_D` branch
(per-`t'` only — `¬ w.vle (algebraMap s_D) 0` is automatic), and two
for the `α_T_D` branches (per-`t'` and explicit `¬ w.vle (algebraMap s_D) 0`).
This is the cleanest factoring honoring the strict-domination
auto-discharge available only at the `α_s_D` branch. -/
theorem h_T_test_compat_loc_canonical
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_α_s_D_per_t :
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
          w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_α_T_D_per_t :
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
            w.vle t' (algebraMap A (Localization.Away s) s_D))
    (h_α_T_D_s_D_ne :
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
          ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ τ ∈ localizedTestFamily s T_D s_D,
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
  intro τ hτ w hw_spa hw_f hστ
  rw [mem_localizedTestFamily_iff] at hτ
  rcases hτ with rfl | hτ_in_T_D
  · -- Branch α_s_D.
    exact ⟨h_α_s_D_per_t w hw_spa hw_f hστ,
      not_vle_zero_of_strict_dominator hστ.2⟩
  · -- Branch α_T_D.
    exact ⟨h_α_T_D_per_t τ hτ_in_T_D w hw_spa hw_f hστ,
      h_α_T_D_s_D_ne τ hτ_in_T_D w hw_spa hw_f hστ⟩

omit [PlusSubring A] in
/-- **T168: `h_α_T_D_s_D_ne` supplier via Cor 7.32 σ-strict-dom branch
splitting + the corrected multi-dominating-unit inequality**.

Produces the α_T_D branch s_D non-vanishing supplier consumed by
`h_T_test_compat_loc_canonical` (third parameter, line 261) and
`h_T_test_compat_loc_branch_α_T_D` (second parameter), using the
**corrected branch-clearing route** (Wedhorn 8.34(ii) Route B, PDF
page 84) — combining:

* **Cor 7.32 σ-strict-domination branch splitting** via
  `not_vle_zero_of_strict_dominator` applied to `hστ.2`: at the α_T_D
  branch (τ ∈ T_D.image), σ-strict-dom hands `¬ w.vle τ 0`.

* **Multi-dominating-unit inequality** via
  `vle_of_dominating_unit_multi_corrected_at` (in
  `WedhornDominatingUnitInequality.lean`): from a multi-element bound
  `w.vle (∏ T_D.image) (algebraMap s_D)` and a per-element lower bound
  `∀ t' ∈ T_D.image, w.vle 1 t'`, the first conjunct yields the per-`t'`
  upper bound `∀ t' ∈ T_D.image, w.vle t' (algebraMap s_D)`. Specialised
  at the σ-strict-dom witness `τ ∈ T_D.image` together with `¬ w.vle τ 0`,
  transitivity through `w.vle (algebraMap s_D) 0` produces a contradiction
  — yielding `¬ w.vle (algebraMap s_D) 0`.

Replaces the previously-attempted T021/T023 σ-power-decay residual
(`AlphaT_DBranchPerTSigmaPowerDecay`, parked at commit `1cdea0d`): T023
showed the σ-power-decay shape is mathematically false uniformly on Spa
(`vle_of_dominating_unit_multi` counter-example documented in
`WedhornDominatingUnitInequality.lean`); the corrected approach uses the
multi-element bound + per-element lower bound, which is exactly the
data naturally available in the cover plus-piece via Wedhorn's Laurent
cover refinement.

Hypotheses match the existing per-w consumer pattern: f-membership and
σ-strict-dom-by-τ both available at `w`, plus the corrected-route
suppliers for the multi-element bound and per-element lower bound at
`w`. -/
theorem h_α_T_D_s_D_ne_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
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
        ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro τ hτ w hw_spa hw_f hστ
  -- Cor 7.32 σ-strict-dom branch splitting at τ ∈ T_D.image: τ is
  -- non-vanishing at w (via `not_vle_zero_of_strict_dominator` from `hστ.2`).
  have h_τ_ne : ¬ w.vle τ 0 := not_vle_zero_of_strict_dominator hστ.2
  -- Corrected multi-dominating-unit inequality's first conjunct: per-`t'`
  -- upper bound by `algebraMap s_D` (using the multi-element bound +
  -- per-element lower bound at this `w`).
  have h_per_t' :
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w.vle t' (algebraMap A (Localization.Away s) s_D) :=
    (vle_of_dominating_unit_multi_corrected_at w
      (h_T_D_multi_bound w hw_spa hw_f)
      (h_T_D_lower_bound w hw_spa hw_f)).1
  -- Specialize the per-t' upper bound at the σ-strict-dom witness τ.
  have h_τ_le_s_D :
      w.vle τ (algebraMap A (Localization.Away s) s_D) :=
    h_per_t' τ hτ
  -- Combine via transitivity: if `w.vle (algebraMap s_D) 0` then
  -- `w.vle τ 0`, contradicting `h_τ_ne`.
  intro h_s_D_zero
  exact h_τ_ne (w.vle_trans h_τ_le_s_D h_s_D_zero)

omit [PlusSubring A] in
/-- **T168: `h_α_T_D_per_t` supplier via the corrected multi-dominating-unit
inequality**.

Companion to `h_α_T_D_s_D_ne_via_multi_corrected` above: produces the
α_T_D branch per-`t'` upper-bound supplier consumed by
`h_T_test_compat_loc_canonical` (second parameter, line 247) and
`h_T_test_compat_loc_branch_α_T_D` (first parameter), using the same
**corrected branch-clearing route** as the s_D-nonvanishing branch.

The conclusion `∀ t' ∈ T_D.image, w.vle t' (algebraMap s_D)` is exactly
the **first conjunct** of `vle_of_dominating_unit_multi_corrected_at`
applied to the multi-element bound + per-element lower bound at `w`.
The σ-strict-dom-by-τ premise is **not used** in the proof: the
per-`t'` upper bound is uniform over `T_D.image`, independent of which
τ ∈ T_D.image won σ-domination at `w`.

Hypotheses match `h_α_T_D_s_D_ne_via_multi_corrected` exactly: the
multi-element bound and per-element lower bound at each `w` in the
cover plus-piece (under f-membership). This shared hypothesis shape is
the natural interface for the corrected-route producers, so a single
pair `(h_T_D_multi_bound, h_T_D_lower_bound)` discharges both α_T_D
branch suppliers consumed by `h_T_test_compat_loc_branch_α_T_D`. -/
theorem h_α_T_D_per_t_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
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
          w.vle t' (algebraMap A (Localization.Away s) s_D) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro _τ _hτ w hw_spa hw_f _hστ
  -- First conjunct of vle_of_dominating_unit_multi_corrected_at.
  exact (vle_of_dominating_unit_multi_corrected_at w
    (h_T_D_multi_bound w hw_spa hw_f)
    (h_T_D_lower_bound w hw_spa hw_f)).1

omit [PlusSubring A] in
/-- **T168: α_T_D branch closed via the corrected multi-dominating-unit
inequality**.

Reusable theorem packaging the α_T_D branch single-branch compatibility
output by feeding the two corrected-route suppliers
(`h_α_T_D_per_t_via_multi_corrected` and
`h_α_T_D_s_D_ne_via_multi_corrected`) into
`h_T_test_compat_loc_branch_α_T_D`. The α_T_D branch is now closed
**modulo the corrected-route hypotheses** (multi-element bound +
per-element lower bound at each `w` in the cover plus-piece, under
f-membership).

After this lemma, the remaining content for the α_T_D branch is the
**Laurent cover refinement producer** for `h_T_D_multi_bound` and
`h_T_D_lower_bound` — Wedhorn's actual cover-piece data on
`V_{D_s} = {w | ∀ t ∈ insert D_s T_D, w.vle t D_s}` (PDF page 84 /
Lemma 8.33). That producer is the genuine remaining T168 content; this
branch closure makes it the **single** open input. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_multi_corrected
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
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
  h_T_test_compat_loc_branch_α_T_D P T s hopen T_D s_D σ_loc
    (h_α_T_D_per_t_via_multi_corrected P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)
    (h_α_T_D_s_D_ne_via_multi_corrected P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)

omit [PlusSubring A] in
/-- **T168: localized Laurent-piece producer for the corrected-route
suppliers** `h_T_D_multi_bound` and `h_T_D_lower_bound`.

Localized analogue of T051's `T050_supplier_via_laurent_piece_membership`
(in `WedhornLaurentProductBoundSupplier.lean`), specialised at
`A := Localization.Away s` with the localized topology / plus-subring
instances. From per-`w` Laurent-piece rationalOpen data on
`Spa(Loc s, ⁺)`:

* `w ∈ rationalOpen ({∏ T_D.image (algebraMap)} : Finset (Loc s))
    (algebraMap s_D)` — singleton-product upper bound at `α s_D`;
* `∀ t' ∈ T_D.image (algebraMap), w ∈ rationalOpen ({(1 : Loc s)})
    t'` — per-element lower bound at `1`,

derive the corrected-route hypothesis pair consumed by
`h_α_T_D_per_t_via_multi_corrected` and
`h_α_T_D_s_D_ne_via_multi_corrected`:

```
w.vle (∏ T_D.image (algebraMap)) (algebraMap s_D) ∧
∀ t' ∈ T_D.image (algebraMap), w.vle (1 : Loc s) t'
```

**Proof**: at each `w` satisfying f-membership, extract the supplied
Laurent-piece data; the multi-element bound and per-element lower bound
follow from the singleton-element rationalOpen membership conjunct
(`v.vle t s` for the singleton `t`).

This is the **localized analogue** of the natural Wedhorn 8.34(ii)
Laurent-cover-refinement output at the base side (PDF page 84 /
Lemma 8.33), expressed in localized rationalOpen vocabulary and
matching the `h_T_D_multi_bound` / `h_T_D_lower_bound` interface
exactly.

After this producer, the **single open input** for the α_T_D branch
closure is the per-`w` localized Laurent-piece rationalOpen data —
paralleling `localized_cor732_laurent_piece_membership_at` (in
`WedhornLocalCor732ToFactoredChain.lean`) for the σ-strict-domination
output. -/
theorem T_D_multi_and_lower_bound_via_localized_laurent_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_w_laurent_piece :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w ∈ rationalOpen
            ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
              : Finset (Localization.Away s))
            (algebraMap A (Localization.Away s) s_D) ∧
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D) ∧
        (∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f
  obtain ⟨h_prod_open, h_per_t_open⟩ :=
    h_per_w_laurent_piece w hw_spa hw_f
  refine ⟨?_, ?_⟩
  · -- Multi-element bound: extract from singleton-product rationalOpen.
    obtain ⟨_hw_spa', h_bound, _h_α_s_D_ne⟩ := h_prod_open
    exact h_bound _ (Finset.mem_singleton.mpr rfl)
  · -- Per-element lower bound: extract from each per-element rationalOpen.
    intro t' ht'
    obtain ⟨_hw_spa', h_bound, _h_t'_ne⟩ := h_per_t_open t' ht'
    exact h_bound _ (Finset.mem_singleton.mpr rfl)

omit [PlusSubring A] in
/-- **T168: end-to-end α_T_D branch closure from localized Laurent-piece
data**.

Composes the localized Laurent-piece producer
`T_D_multi_and_lower_bound_via_localized_laurent_piece` with the α_T_D
branch closer `h_T_test_compat_loc_branch_α_T_D_via_multi_corrected`
to produce the α_T_D branch's full single-branch compatibility output
directly from per-`w` localized Laurent-piece rationalOpen data.

This is the **end-to-end α_T_D branch theorem** for the corrected
branch-clearing route: the only remaining input is the natural Wedhorn
8.34(ii) Laurent-cover-refinement output at the localized base side,
which parallels `localized_cor732_laurent_piece_membership_at` for the
σ-strict-domination output.

After this theorem, the T168 α_T_D branch is closed modulo a single
named per-`w` localized Laurent-piece rationalOpen data hypothesis —
the natural Wedhorn 8.34(ii) PDF page 84 / Lemma 8.33 Laurent-piece
output expressed in localized rationalOpen vocabulary. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_per_w_laurent_piece :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w ∈ rationalOpen
            ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
              : Finset (Localization.Away s))
            (algebraMap A (Localization.Away s) s_D) ∧
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t') :
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
  -- Extract the corrected-route hypothesis pair from Laurent-piece data.
  have h_pair :=
    T_D_multi_and_lower_bound_via_localized_laurent_piece P T s hopen
      T_D s_D σ_loc h_per_w_laurent_piece
  -- Feed the two halves into h_T_test_compat_loc_branch_α_T_D_via_multi_corrected.
  exact h_T_test_compat_loc_branch_α_T_D_via_multi_corrected P T s hopen
    T_D s_D σ_loc
    (fun w hw_spa hw_f => (h_pair w hw_spa hw_f).1)
    (fun w hw_spa hw_f => (h_pair w hw_spa hw_f).2)

omit [PlusSubring A] in
/-- **T169: localized Laurent-piece rationalOpen producer**
(`h_per_w_laurent_piece_target`).

Produces the per-`w` localized Laurent-piece rationalOpen data consumed
by `h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece` (and
its underlying `T_D_multi_and_lower_bound_via_localized_laurent_piece`)
from the **natural Wedhorn 8.34(ii) Laurent cover refinement output at
the localized level**: the pair

* `h_T_D_multi_bound` — multi-element bound at `α s_D`:
  `w.vle (∏ T_D.image (algebraMap)) (algebraMap s_D)` per `w` under
  f-membership;
* `h_T_D_lower_bound` — per-element lower bound at `1`:
  `∀ t' ∈ T_D.image (algebraMap), w.vle 1 t'` per `w` under
  f-membership.

These are the same two hypotheses consumed by the corrected-route
α_T_D-branch suppliers `h_α_T_D_per_t_via_multi_corrected` /
`h_α_T_D_s_D_ne_via_multi_corrected` (from T168 commits `8316474` /
`d954344`). Wedhorn's actual cover-refinement (PDF page 84 / Lemma 8.33)
produces exactly this pair on each Laurent piece by construction; this
producer **packages** it into the rationalOpen vocabulary used by the
downstream T168 caller.

The rationalOpen non-vanishing clauses follow:

* `¬ w.vle (algebraMap s_D) 0` — the second conjunct of
  `vle_of_dominating_unit_multi_corrected_at` (in
  `WedhornDominatingUnitInequality.lean`), derived from
  `h_T_D_multi_bound + h_T_D_lower_bound` via the chain
  `1 ≤ (∏ T_D.image) ≤ algebraMap s_D` plus `not_vle_one_zero`.

* `¬ w.vle t' 0` for each `t' ∈ T_D.image (algebraMap)` — derived from
  `h_T_D_lower_bound` via the chain `1 ≤ t'` (under `w.vle 1 t'`) plus
  `not_vle_one_zero` and transitivity.

This is the **inverse direction** of T168's
`T_D_multi_and_lower_bound_via_localized_laurent_piece`: that lemma
unwraps the rationalOpen form into multi+lower bounds; this lemma
wraps multi+lower bounds back into the rationalOpen form. Both
directions are honest Wedhorn 8.34(ii) packaging, with no σ-power-decay,
locSubring integrality, or product-from-per-t bound. -/
theorem h_per_w_laurent_piece_target
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    letI : PlusSubring (Localization.Away s) :=
      localizationLocSubringPlusSubring P T s
    letI : DecidableEq (Localization.Away s) := Classical.decEq _
    ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
      w.vle ((σ_loc : Localization.Away s) *
          (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
        (algebraMap A (Localization.Away s) s) →
      w ∈ rationalOpen
          ({∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t}
            : Finset (Localization.Away s))
          (algebraMap A (Localization.Away s) s_D) ∧
      ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
        w ∈ rationalOpen
            ({(1 : Localization.Away s)} : Finset (Localization.Away s)) t' := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  letI : PlusSubring (Localization.Away s) :=
    localizationLocSubringPlusSubring P T s
  letI : DecidableEq (Localization.Away s) := Classical.decEq _
  intro w hw_spa hw_f
  have h_prod := h_T_D_multi_bound w hw_spa hw_f
  have h_lower := h_T_D_lower_bound w hw_spa hw_f
  -- s_D non-vanishing: second conjunct of vle_of_dominating_unit_multi_corrected_at.
  have h_s_D_ne : ¬ w.vle (algebraMap A (Localization.Away s) s_D) 0 :=
    (vle_of_dominating_unit_multi_corrected_at w h_prod h_lower).2
  refine ⟨⟨hw_spa, ?_, h_s_D_ne⟩, ?_⟩
  · -- Singleton-product upper bound: w.vle (∏ T_D.image) (algebraMap s_D).
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact h_prod
  · -- Per-element lower bound + non-vanishing for each t' ∈ T_D.image.
    intro t' ht'
    refine ⟨hw_spa, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      exact h_lower t' ht'
    · -- ¬ w.vle t' 0: from w.vle 1 t' + not_vle_one_zero.
      intro h_t'_zero
      have h_one_zero : w.vle (1 : Localization.Away s) 0 :=
        w.vle_trans (h_lower t' ht') h_t'_zero
      exact w.not_vle_one_zero h_one_zero

omit [PlusSubring A] in
/-- **T169 caller: end-to-end α_T_D branch closure from
multi+lower bounds**.

Composes T169's `h_per_w_laurent_piece_target` with T168's
`h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece` to give
the α_T_D branch's full single-branch compatibility output directly
from the per-`w` multi-element bound + per-element lower bound
hypotheses. This shows T169's producer feeds the T168 caller as
intended.

After this caller, the α_T_D branch closure consumes only the natural
Wedhorn 8.34(ii) Laurent cover refinement output (the multi-element
bound + per-element lower bound at each `w` in the cover plus-piece);
no further rationalOpen-shape conversion is needed downstream. -/
theorem h_T_test_compat_loc_branch_α_T_D_via_multi_lower
    [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (T_D : Finset A) (s_D : A)
    (σ_loc : (Localization.Away s)ˣ)
    (h_T_D_multi_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        w.vle (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t)
              (algebraMap A (Localization.Away s) s_D))
    (h_T_D_lower_bound :
      letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
      letI : PlusSubring (Localization.Away s) :=
        localizationLocSubringPlusSubring P T s
      letI : DecidableEq (Localization.Away s) := Classical.decEq _
      ∀ w ∈ Spa (Localization.Away s) (Localization.Away s)⁺,
        w.vle ((σ_loc : Localization.Away s) *
            (∏ t ∈ T_D.image (algebraMap A (Localization.Away s)), t))
          (algebraMap A (Localization.Away s) s) →
        ∀ t' ∈ T_D.image (algebraMap A (Localization.Away s)),
          w.vle (1 : Localization.Away s) t') :
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
  h_T_test_compat_loc_branch_α_T_D_via_localized_laurent_piece P T s hopen
    T_D s_D σ_loc
    (h_per_w_laurent_piece_target P T s hopen T_D s_D σ_loc
      h_T_D_multi_bound h_T_D_lower_bound)

end ValuationSpectrum
