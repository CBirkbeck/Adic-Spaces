/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Cor732
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

/-! ## Target signature: full multi-element σ-clearing

The **next missing layer** above `Spv.vle_prod_of_pointwise`. It packages
the Wedhorn 8.34(ii) σ-domination cancellation at every Spa point into
the rational-open containment

```
rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

for an arbitrary finite `D.T`, where `f` is constructed from the σ
output of `Cor732.exists_dominating_unit` applied to a carefully chosen
test family `T_test`.

### Target signature

```
theorem rationalOpen_subset_via_strict_sigma_domination
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCovering A) (D : RationalLocData A)
    (σ : Aˣ)
    -- σ-domination over the test family `T_test`:
    (T_test : Finset A)
    (hσ : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    -- T_test is "C1-compatible" with D and C.base — the precise shape
    -- of the test family that makes the σ-clearing succeed:
    (hT_test_compat : ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0) :
    rationalOpen (insert ((σ : A) * (∏ t ∈ D.T, t)) C.base.T) C.base.s ⊆
      rationalOpen D.T D.s
```

### Status of the target

* The σ supplier `Cor732.exists_dominating_unit` is available.
* The Finset.prod propagation building block `Spv.vle_prod_of_pointwise`
  is landed in this file.
* The **case analysis** captured in `hT_test_compat` is the genuinely
  Wedhorn-specific content: it specifies which `τ ∈ T_test` admits which
  algebraic transfer, and is the next concrete formalisation target.
  Without supplying `hT_test_compat`, the lemma reduces to a tautology;
  the *reduction* `hT_test_compat → conclusion` is purely logical.
* The **discharge** of `hT_test_compat` from a concrete choice of
  `T_test` (Wedhorn's choice: `T_test := D.T.image (· * C.base.s) ∪
  {D.s}`, plus a power product) is the genuinely missing case-analysis
  content. It uses `mul_vle_mul_iff_left` at `σ` (a unit) plus the
  arithmetic of `≤ᵥ` over a `Finset.prod` (the building block landed
  above) plus careful disjunction over the τ-cases.

### Where it slots in

After `rationalOpen_subset_via_strict_sigma_domination` lands, combined
with `WedhornStandardCoverRefinement.exists_single_f_refinement_at_t_of_singleton_unit_rescaled`
(the `|D.T| = 1` discharge), the full
`exists_single_f_refinement_at_t_via_dominating_unit` target signature
discharges by case-splitting on `|D.T|` and using `Cor732.exists_dominating_unit`
to supply σ.

### Why this is genuinely Wedhorn-content

The case-analysis content of `hT_test_compat` is precisely Wedhorn's
"dominating unit clears the multi-element denominator" lemma (Wedhorn
8.34(ii) / Hübner 3.7). It is purely a valuation-inequality manipulation
using σ's `Cor732`-supplied strict domination plus the
`Spv.vle_prod_of_pointwise` building block landed above.

No faithful-flatness / Cor 8.32 / Jacobson / T001 content is invoked. -/

end ValuationSpectrum
