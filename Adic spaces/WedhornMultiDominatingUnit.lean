/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Cor732
import «Adic spaces».Presheaf
import «Adic spaces».RationalSubsets

/-!
# Wedhorn multi-element dominating-unit step (smallest reusable lemmas)

Building blocks toward the **multi-element σ-clearing lemma** identified
as the residual blocker of `WedhornStandardCoverRefinement.lean`'s
`exists_single_f_refinement_at_t_via_dominating_unit` target signature.

## API audit (state of the repository as of this file)

### Cor 7.32 output shape (the σ supplier)

```
ValuationSpectrum.exists_dominating_unit
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, ...)
    (T : Finset A)
    (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A)
```
(`Adic spaces/Cor732.lean:206`).

The **strict-dominance pair** `v.vle (s : A) t ∧ ¬ v.vle t (s : A)` is
the key per-Spa-point output to be transferred into the multi-`t'`
inequality at every plus-piece point.

### Available valuation-inequality API

* `Spv.mul_vle_mul_left`, `Spv.vle_mul_cancel`
  (`Adic spaces/ValuationSpectrum.lean:63-65`) — single-multiplication
  cancellation at units.
* `ValuativeRel.mul_vle_mul` — bilinear product propagation
  `(x ≤ᵥ y → x' ≤ᵥ y' → x*x' ≤ᵥ y*y')` (Mathlib).
* `ValuativeRel.mul_vle_mul_iff_left` — iff form of cancellation at a
  non-zero element (Mathlib).
* `ValuativeRel.pow_vle_pow` — power propagation
  `(a ≤ᵥ b → ∀ n, a^n ≤ᵥ b^n)` (Mathlib).
* `ValuativeRel.not_vle_zero_of_isUnit` — units are non-zero in
  valuation (Mathlib via `Adic spaces/ValuationSpectrum.lean:224`).

### Missing (this file lands the first piece)

* **Finset.prod propagation in Spv form** — landed below as
  `Spv.vle_prod_of_pointwise`. This is the smallest reusable building
  block needed to package multi-element products `∏ t ∈ T, x t` under
  pointwise `vle`-bounds, which the Wedhorn σ-clearing uses to bound
  `w(∏ t ∈ D.T, t) ≤ w(D.s ^ |D.T|)` from per-`t` bounds
  `w.vle t D.s`.

* **Strict σ-dominance + finite-product transfer** — the genuinely
  new content. Documented as the missing target signature
  `rationalOpen_subset_via_strict_sigma_domination` at the end of this
  file; the proof requires a non-trivial case analysis on which
  `τ ∈ T_test` wins σ-domination at each `w` and is the next concrete
  formalisation target.

## What this file provides

1. `Spv.vle_prod_of_pointwise` — pointwise-`vle` to product-`vle` for
   any indexed family over a `Finset`. Proved by `Finset.induction_on`
   using `ValuativeRel.mul_vle_mul`. Generic / reusable.

2. Documented target signature
   (`rationalOpen_subset_via_strict_sigma_domination`) for the
   full multi-element σ-clearing lemma — the next missing layer
   above `Spv.vle_prod_of_pointwise`.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content.
No new final acyclicity hypotheses. Strict adherence to the Wedhorn
8.34(ii) σ-domination route. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Finset.prod monotonicity for valuations (Spv form)**.

For any indexed family `x, y : α → A` and a finite index set `T`, if
`v.vle (x t) (y t)` holds pointwise for every `t ∈ T`, then the product
inequality `v.vle (∏ t ∈ T, x t) (∏ t ∈ T, y t)` holds.

**Use case**: in the Wedhorn σ-clearing argument, this lemma packages
per-`t` valuation bounds `w.vle t D.s` (for `t ∈ D.T`) into the global
product bound `w.vle (∏ t ∈ D.T, t) (∏ t ∈ D.T, D.s) = w.vle (∏ t,
t) (D.s ^ |D.T|)` (after rewriting the constant product by power), which
is one half of the algebraic core of the multi-element σ-clearing step.

**Proof**: `Finset.induction_on` using `ValuativeRel.mul_vle_mul`
(bilinear propagation) and `vle_total 1 1` for the empty base case. -/
lemma Spv.vle_prod_of_pointwise
    {α : Type*} (v : Spv A) (T : Finset α) {x y : α → A}
    (h : ∀ t ∈ T, v.vle (x t) (y t)) :
    v.vle (∏ t ∈ T, x t) (∏ t ∈ T, y t) := by
  classical
  letI : ValuativeRel A := v.toValuativeRel
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (v.vle_total 1 1).elim id id
  | insert a T' ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ValuativeRel.mul_vle_mul (h a (Finset.mem_insert_self a T'))
      (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))

/-- **Logical reducer: rational-open containment from `T_test`-compatibility
of σ-strict-domination**.

This is the **callsite shape** of the multi-element σ-clearing step: it
takes Cor 7.32-style σ-domination of a test family `T_test` plus an
**explicit τ-case-analysis hypothesis** `hT_test_compat` and produces
the rational-open subset conclusion

```
R(insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T, C.base.s) ⊆ R(D.T, D.s)
```

for arbitrary finite `D.T`. The reducer itself contains no genuinely
new Wedhorn content: it is purely the logical step from the per-Spa-point
existential `hσ` plus the per-τ algebraic transfer `hT_test_compat` to
the membership-of-rational-open conclusion at every `w` in the LHS
plus-piece.

**The genuine Wedhorn 8.34(ii) content** is now isolated as the
discharge of `hT_test_compat` for a specific test family `T_test`. The
canonical Wedhorn choice — `T_test := D.T.image (· * C.base.s) ∪ {D.s}`
with the power-product f-shape `(σ : A) * (∏ t ∈ D.T, t) * D.s ^ N` —
is the next concrete formalisation target; the present reducer fixes
the callsite shape so that the τ-case-analysis discharge can be
attempted in isolation. Detailed obligation pinned in the docblock at
the end of this file.

**Proof**: pointwise on the LHS plus-piece: extract the `f`-membership
inequality from the `insert`-clause, apply `hσ` at `w` to pick a
witness `τ`, then apply `hT_test_compat` at `τ` to extract the per-`t'`
inequalities and non-degeneracy clause comprising the RHS rational-open
membership. -/
theorem rationalOpen_subset_via_strict_sigma_domination
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCovering A) (D : RationalLocData A)
    (σ : Aˣ) (T_test : Finset A)
    (hσ : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    (hT_test_compat : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0) :
    rationalOpen (insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T) C.base.s ⊆
      rationalOpen D.T D.s := by
  intro w hw
  obtain ⟨hw_spa, hwIns, _hwCs⟩ := hw
  -- Extract f-membership at w from the `insert`-clause.
  have hw_f : w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s :=
    hwIns _ (Finset.mem_insert_self _ _)
  -- Apply σ-domination at w to pick the witnessing τ.
  obtain ⟨τ, hτ_mem, hστ⟩ := hσ w hw_spa
  -- Apply the τ-case-analysis hypothesis to extract D.T inequalities + non-degeneracy.
  obtain ⟨hwD, hwDs⟩ := hT_test_compat τ hτ_mem w hw_spa hw_f hστ
  -- Conclude w ∈ R(D.T, D.s).
  exact ⟨hw_spa, hwD, hwDs⟩

/-- **Strict-domination forces non-degeneracy** (smallest valuation
arithmetic helper toward multi-element σ-clearing).

For any `w : Spv A` and any `x, y : A`, if `w` strictly dominates
`x` by `y` (i.e., `¬ w.vle x y`), then `x` is non-degenerate at `w`
(`¬ w.vle x 0`).

**Proof (contrapositive)**: if `w.vle x 0`, then by `≤ᵥ` transitivity
against the always-true `0 ≤ᵥ y` (i.e., `ValuativeRel.zero_vle`), we
get `w.vle x y`, contradicting the strict hypothesis.

**Use case in σ-clearing**: Cor 7.32's σ-strict-domination output
`w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` produces `¬ w.vle τ (σ : A)`,
which by this lemma yields `¬ w.vle τ 0` — i.e., `τ` is non-degenerate
at `w`. With `τ := D.s` (when `D.s ∈ T_test` is the σ-witness at `w`),
this discharges the **non-degeneracy half** of the multi-element
σ-clearing conjunction `(∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0`. -/
lemma not_vle_zero_of_strict_dominator
    {w : Spv A} {x y : A} (h_strict : ¬ w.vle x y) :
    ¬ w.vle x 0 := by
  intro hw_x0
  apply h_strict
  letI : ValuativeRel A := w.toValuativeRel
  exact ValuativeRel.vle_trans hw_x0 (ValuativeRel.zero_vle y)

/-- **Discharge of `hT_test_compat` for the empty `D.T` case** with
`T_test := {D.s}`.

The `D.T = ∅` case is the simplest non-trivial cover-piece shape: it
captures basic-open-at-`D.s` cover pieces `D` with no test elements.
The conjunction `(∀ t' ∈ ∅, ...) ∧ ¬ w.vle D.s 0` reduces to just
`¬ w.vle D.s 0`, which is discharged by `not_vle_zero_of_strict_dominator`
applied to the σ-strict-domination by `D.s`.

**Plug-in callsite**: feed this into `rationalOpen_subset_via_strict_sigma_domination`
with `T_test := {D.s}` to obtain
```
rationalOpen (insert (σ : A) C.base.T) C.base.s ⊆ rationalOpen ∅ D.s
```
(noting `(σ : A) * (∏ t ∈ ∅, t) = (σ : A)` after `Finset.prod_empty`).

The σ supplier is `Cor732.exists_dominating_unit` applied to
`T := {D.s}`, requiring the no-common-zero hypothesis
`∀ v ∈ Spa A A⁺, ¬ v.vle D.s 0` (a non-degeneracy precondition on the
cover-piece denominator that holds when the cover is non-trivially
contained in the basic open at `D.s`). -/
lemma hT_test_compat_of_empty_D_T
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCovering A) (D : RationalLocData A)
    (hD_empty : D.T = ∅) (σ : Aˣ) :
    ∀ τ ∈ ({D.s} : Finset A), ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0 := by
  intro τ hτ w _hw_spa _hw_f hστ
  rw [Finset.mem_singleton] at hτ
  subst hτ
  refine ⟨?_, not_vle_zero_of_strict_dominator hστ.2⟩
  intro t' ht'
  rw [hD_empty] at ht'
  exact absurd ht' (Finset.notMem_empty t')

/-! ## Remaining obligation: per-`t'` inequalities for arbitrary `D.T`

### Status of the canonical T_test choice (CORRECTED)

The earlier docblock proposed `T_test := D.T.image (· * C.base.s) ∪
{D.s * C.base.s}` as a "canonical choice" that would discharge
`hT_test_compat` uniformly. **This choice does not work** for the
per-`t'` half of the conjunction:

* In the case `τ = t₀ * C.base.s` for `t₀ ∈ D.T`, σ-strict-domination
  gives only `w(σ) ≤ w(t₀) * w(C.base.s)` — i.e., information about a
  single `t₀`, not all `t' ∈ D.T`. There is no algebraic route from
  this single-`t₀` bound and the f-membership to the uniform per-`t'`
  conclusion `∀ t' ∈ D.T, w.vle t' D.s`.

* In the case `τ = D.s * C.base.s`, σ-strict-domination gives
  `w(σ) ≤ w(D.s) * w(C.base.s)`. Combined with the f-membership
  `w(σ) * (∏ t ∈ D.T, w(t)) ≤ w(C.base.s)`, one cannot derive
  `w(t') ≤ w(D.s)` without additional information about
  `w(C.base.s) / (w(σ) * ∏_{t ≠ t'} w(t))` versus `w(D.s)`.

The genuine Wedhorn 8.34(ii) approach almost certainly requires
**pre-localisation at `C.base.s`** (treating `R(C.base.T, C.base.s)`
as a Spa over a localised ring `A_loc`) so that the σ-construction
operates on the localised space rather than `Spa A A⁺` directly. This
is structural, not a simple test-family-choice question.

### What this file currently provides

* `not_vle_zero_of_strict_dominator` — generic helper extracting
  non-degeneracy from a strict `≤ᵥ` inequality. Single-line proof via
  `vle_trans` against `zero_vle`.

* `hT_test_compat_of_empty_D_T` — concrete discharge of `hT_test_compat`
  in the trivial `D.T = ∅` case (basic-open-at-`D.s` cover pieces),
  using `T_test := {D.s}`. Plugged into
  `rationalOpen_subset_via_strict_sigma_domination`, this discharges
  the C1 single-`f` containment for the `D.T = ∅` subcase.

### Smallest missing valuation arithmetic lemma

The remaining obligation — the per-`t'` inequality discharge for
`|D.T| ≥ 1` — admits TWO possible routes; both are open:

**Route A (direct, valuation arithmetic only)**: identify a test family
`T_test` and an f-shape `f := σ * (something involving D.T, D.s,
C.base.s, exponents)` such that, at every `w ∈ Spa A A⁺`, the
combination of f-membership and σ-strict-domination by some `τ ∈ T_test`
forces `w.vle t' D.s` for every `t' ∈ D.T`. **This appears to fail**
under the natural canonical choices (see analysis above) and likely
requires a non-uniform (per-`w`) argument outside the scope of the
present `hT_test_compat` shape.

**Route B (structural / pre-localisation)**: pre-localise `A` at
`C.base.s` to obtain `A_loc`, then apply Cor 7.32 / σ-construction
inside `Spa(A_loc, A_loc⁺)`. The standard Wedhorn 8.34(ii) proof
follows this route. The smallest missing lemma is then a **transfer
lemma** `rationalOpen_subset_localisation_transfer` between
rational opens of `A` and `A_loc` along the localisation map; its
precise signature involves the `Localization.Away C.base.s` ring
structure plus the comap behaviour of Spa-points across this map.

### Status

* The reducer `rationalOpen_subset_via_strict_sigma_domination` provides
  the right **callsite shape** for either route.
* The `D.T = ∅` discharge above is a concrete sanity-check that the
  reducer integrates correctly with the σ-strict-domination output.
* The `|D.T| ≥ 1` per-`t'` discharge remains the genuine Wedhorn
  content; the present file does not claim a "canonical choice" without
  a verified discharge.

### Why this is still Wedhorn-route

No faithful-flatness / Cor 8.32 / Jacobson / T001 content is invoked
anywhere in this file. The framework is purely Wedhorn 8.34(ii) /
Cor 7.32 σ-domination. -/

end ValuationSpectrum
