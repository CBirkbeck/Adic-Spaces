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

/-! ## Remaining obligation: discharging `hT_test_compat`

`rationalOpen_subset_via_strict_sigma_domination` reduces the multi-element
σ-clearing problem to a single concrete obligation:

* Choose a test family `T_test ⊆ A` with no common zero on `Spa(A, A⁺)`
  (so that `Cor732.exists_dominating_unit` supplies the σ-domination
  hypothesis `hσ`).
* Discharge `hT_test_compat`: prove that at every `w ∈ Spa(A, A⁺)`, the
  conjunction of `w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s` (the
  f-membership) and `w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` (the strict
  σ-domination at τ) implies the per-`t'` inequalities and the
  non-degeneracy clause for `D.s`.

### Wedhorn's canonical choice

```
T_test := D.T.image (· * C.base.s) ∪ {D.s * C.base.s}
       (or a power-product variant: ∪ {D.s ^ N * C.base.s})
```

The τ-case-analysis splits into two cases at each `w`:

**Case `τ = t' * C.base.s` for some `t' ∈ D.T`**: σ-strict-domination
gives `w.vle (σ : A) (t' * C.base.s)` with strict, i.e.
`w(σ) ≤ w(t') * w(C.base.s)`. Combined with the f-membership
`w(σ) * w(∏ t ∈ D.T, t) ≤ w(C.base.s)` and the non-degeneracy of
`C.base.s` (carried by `hw_spa`/`hwCs` if needed), one derives
`w.vle t' D.s` for every `t' ∈ D.T` via `Spv.vle_mul_cancel` at
`C.base.s` plus `Spv.vle_prod_of_pointwise` (landed above) for the
multi-element factor. The non-degeneracy clause `¬ w.vle D.s 0`
follows from σ-domination's strict component.

**Case `τ = D.s * C.base.s` (or power-variant)**: σ-strict-domination
gives `w.vle (σ : A) (D.s * C.base.s)` with strict. Combined with the
f-membership, this case directly gives the non-degeneracy clause and
the per-`t'` inequalities through a parallel cancellation argument.

### What is the next formalisation target

```
lemma hT_test_compat_of_canonical_choice
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] (C : RationalCovering A) (D : RationalLocData A)
    (σ : Aˣ) :
    let T_test : Finset A :=
      D.T.image (· * C.base.s) ∪ {D.s * C.base.s}
    ∀ τ ∈ T_test, ∀ w ∈ Spa A A⁺,
      w.vle ((σ : A) * (∏ t ∈ D.T, t)) C.base.s →
      (w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) →
        (∀ t' ∈ D.T, w.vle t' D.s) ∧ ¬ w.vle D.s 0
```

This is the genuinely Wedhorn-specific content. Its proof is a careful
case analysis on `τ ∈ T_test` followed by `Spv.vle_mul_cancel` at the
unit factor `C.base.s` (using `¬ w.vle C.base.s 0` from `w` lying in a
plus-piece over `C.base.s`) plus `Spv.vle_prod_of_pointwise` to handle
the multi-element factor. No new mathematical input beyond the
σ-domination and basic valuation arithmetic; the difficulty is the
length and case-management of the proof.

### Why this is genuinely Wedhorn-content

The τ-case-analysis is precisely Wedhorn's "dominating unit clears the
multi-element denominator" lemma (Wedhorn 8.34(ii) / Hübner 3.7). It is
purely a valuation-inequality manipulation using σ's `Cor732`-supplied
strict domination plus the `Spv.vle_prod_of_pointwise` building block
landed above.

No faithful-flatness / Cor 8.32 / Jacobson / T001 content is invoked. -/

end ValuationSpectrum
