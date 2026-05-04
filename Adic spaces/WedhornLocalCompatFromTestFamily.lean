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

end ValuationSpectrum
