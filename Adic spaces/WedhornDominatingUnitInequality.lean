/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationSpectrum

/-!
# Wedhorn dominating-unit valuation-inequality core

Pure valuation-inequality building blocks for the Wedhorn 8.34(ii)
σ-clearing argument. These are point-level lemmas that combine
`ValuativeRel.mul_vle_mul`, `ValuativeRel.pow_vle_pow`, and
transitivity of `vle` into reusable shapes that consumers (notably
`WedhornC1StrongSupplierCore.lean`) can apply repeatedly when chaining
through

```
v(f) = v(σ) * v(t) * v(D.s)^N ≤ v(C.base.s)
```

at a fixed Spa-point `v`.

## Strategy

The full multi-element σ-clearing lemma
(`vle_of_dominating_unit_multi`, target signature documented at
`WedhornStandardCoverRefinement.lean:301`) is genuinely a per-Spa-point
case analysis on which `τ ∈ T_test ∪ {D_s}` wins σ-domination. This
file does **not** attempt that full case analysis; it provides the
two algebraic building blocks that participate in any branch of that
case analysis:

1. **σ-monotonicity at a constant**: from `v.vle (σ : A) τ`, deduce
   `v.vle ((σ : A) * c) (τ * c)` and the power version
   `v.vle ((σ : A)^N * c) (τ^N * c)`.
2. **σ-replacement via transitivity**: from `v.vle (σ : A) τ` and
   `v.vle (τ * a) b`, deduce `v.vle ((σ : A) * a) b`. Power version
   analogous.

Together these compose into the pointwise candidate inequality
`v.vle f C.base.s` once the user supplies the per-`τ`-branch
intermediate `v.vle (τ^N * intermediate) C.base.s`.

## What this file provides

* `vle_mul_const_of_dominating_at` — σ-domination → product inequality
  with a constant right factor.
* `vle_pow_mul_const_of_dominating_at` — power σ-domination version
  using `ValuativeRel.pow_vle_pow`.
* `vle_replace_dominating_at` — σ-replacement via transitivity:
  `v.vle σ τ → v.vle (τ * a) b → v.vle (σ * a) b`.
* `vle_replace_pow_dominating_at` — power version of replacement.
* `vle_pow_mul_pow_const_of_dominating_at` — bilinear σ-power and
  τ-power product inequality (the Wedhorn-shape `σ^N * t^M ≤ τ^N * t^M`
  appearing in Step 3 of the dominating-unit argument).

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`, or any in-flight file.
* Imports only `«Adic spaces».ValuationSpectrum` plus its transitive
  closure (Spv, vle, ValuativeRel infrastructure).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **σ-domination at a constant right factor**. For a Spa-point `v`
and σ-domination `v.vle (σ : A) τ`, multiplying both sides by a constant
`c : A` preserves the inequality: `v.vle ((σ : A) * c) (τ * c)`. -/
theorem vle_mul_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ : A} (hστ : v.vle (σ : A) τ) (c : A) :
    v.vle ((σ : A) * c) (τ * c) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul hστ ((v.vle_total c c).elim id id)

/-- **σ-domination at a power constant**. Power-product version of
`vle_mul_const_of_dominating_at`: σ-domination raised to the `N`-th
power transfers to a product with any constant `c : A`. -/
theorem vle_pow_mul_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ : A} (hστ : v.vle (σ : A) τ) (c : A) (N : ℕ) :
    v.vle ((σ : A) ^ N * c) (τ ^ N * c) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
    ((v.vle_total c c).elim id id)

/-- **σ-replacement via transitivity** (point-level Wedhorn 8.34(ii)
Step 3 building block). From σ-domination `v.vle (σ : A) τ` and a
known intermediate inequality `v.vle (τ * a) b`, deduce
`v.vle ((σ : A) * a) b`. -/
theorem vle_replace_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ)
    (h_chain : v.vle (τ * a) b) :
    v.vle ((σ : A) * a) b := by
  letI : ValuativeRel A := v.toValuativeRel
  exact v.vle_trans
    (ValuativeRel.mul_vle_mul hστ ((v.vle_total a a).elim id id)) h_chain

/-- **Power version of σ-replacement**. From σ-domination
`v.vle (σ : A) τ` and an intermediate `v.vle (τ ^ N * a) b`, deduce
`v.vle ((σ : A) ^ N * a) b`. Used when the candidate carries a σ-power
factor `σ^N`. -/
theorem vle_replace_pow_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ) (N : ℕ)
    (h_chain : v.vle (τ ^ N * a) b) :
    v.vle ((σ : A) ^ N * a) b := by
  letI : ValuativeRel A := v.toValuativeRel
  exact v.vle_trans
    (ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
      ((v.vle_total a a).elim id id)) h_chain

/-- **Bilinear σ-power / τ-power inequality**. From σ-domination
`v.vle (σ : A) τ` and an unrelated `v.vle a b`, deduce the bilinear
power-product inequality
`v.vle ((σ : A) ^ N * a ^ M) (τ ^ N * b ^ M)`. The exact algebraic
shape appearing in Wedhorn 8.34(ii)'s Step 3 chain
`v(σ)^N * v(t)^M ≤ v(τ)^N * v(D.s)^M` after picking
`a := t, b := D.s`. -/
theorem vle_pow_mul_pow_const_of_dominating_at
    (v : Spv A) {σ : Aˣ} {τ a b : A} (hστ : v.vle (σ : A) τ)
    (hab : v.vle a b) (N M : ℕ) :
    v.vle ((σ : A) ^ N * a ^ M) (τ ^ N * b ^ M) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact ValuativeRel.mul_vle_mul (ValuativeRel.pow_vle_pow hστ N)
    (ValuativeRel.pow_vle_pow hab M)

end ValuationSpectrum
