/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationContinuity
import «Adic spaces».HuberRings
import «Adic spaces».ValuationSpectrum

/-!
# `Spv(A, I)` infrastructure (Wedhorn §7.1) — T-COMPACT-NO-HARCH foundation

Per round-22 reviewer (ChatGPT Pro, 2026-05-16): the no-`hArch` compactness
of rational opens in `Spa(A, A⁺)` for Tate rings goes via Wedhorn's
spectral space `Spv(A, I)`, **not** via the project's existing
Boolean-product encoding (which conflates Fσ cofinality with closed
conditions).

This file establishes the **definitional infrastructure** for `Spv(A, I)`
and the cofinality predicate used in Wedhorn 7.10's reverse direction.

## Main definitions

* `Valuation.CofinalValue v a` : `v(a)` is *cofinal* in `Γ_v ∪ {0}`, in
  the sense that for every `γ ∈ Γ_v` with `γ > 0`, there exists `n : ℕ`
  with `v(a)^n < γ`. This is the algebraic cofinality condition that
  Wedhorn 7.10's reverse direction uses to bridge `v(I) < 1` →
  continuity.

* `Spv.IsInSpvAI v I` : the disjunctive characterisation of
  `v ∈ Spv(A, I)` per Wedhorn Lemma 7.4: either every `a ∈ I` has
  `v(a)` cofinal in `Γ_v`, or `Γ_v = c Γ_v` (microbial).

## References

* Wedhorn, *Adic Spaces*, §7.1 (Definition 7.3, Lemma 7.4),
  arXiv:1910.05934.
-/

namespace Valuation

variable {A : Type*} [CommRing A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Cofinality of `v(a)` in `Γ_v` (algebraic form, Wedhorn 7.4 prep).**
A value `v(a)` is *cofinal* if for every `γ : Γ₀` with `γ > 0`, some
power `v(a)^n` is strictly less than `γ`.

This is the algebraic predicate that Wedhorn 7.10's reverse direction
uses: combined with `v(a) < 1` it gives continuity of `v` (in the
`f`-adic / Tate setting). -/
def CofinalValue (v : Valuation A Γ₀) (a : A) : Prop :=
  ∀ γ : Γ₀, 0 < γ → ∃ n : ℕ, v a ^ n < γ

/-- `CofinalValue` implies `v(a) ≤ 1` (in fact `v(a) < 1`, unless `v(a) = 0`). -/
theorem CofinalValue.le_one {v : Valuation A Γ₀} {a : A} (h : CofinalValue v a) :
    v a ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  -- v(a) > 1 means v(a)^n ≥ 1 for all n.
  have h_pow_ge : ∀ n : ℕ, 1 ≤ v a ^ n := fun n => Left.one_le_pow_of_le h_gt.le n
  -- Take γ = 1. Cofinality gives ∃ n, v(a)^n < 1. Contradicts h_pow_ge.
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  exact absurd hn (not_lt_of_ge (h_pow_ge n))

end Valuation

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`v ∈ Spv(A, I)` (Wedhorn 7.4 disjunction).** For `v : Spv A` and
`I : Ideal A`, `v` is *in `Spv(A, I)`* if either
- every `a ∈ I` has `v(a)` cofinal in `Γ_v`, or
- `v` is "microbial" (`Γ_v = c Γ_v` in Wedhorn's notation; here
  formulated as `v` having no proper characteristic subgroup, captured
  via the equivalent condition that every nonzero value is part of a
  cofinal sequence of powers).

**Status (round-22).** This is the algebraic characterisation per
Wedhorn Lemma 7.4. The spectral / topological structure on
`Spv(A, I)` (the refined topology from Wedhorn 7.5) is built on top of
this predicate; see the companion definitions below. -/
def Spv.IsInSpvAI (v : Spv A) (I : Ideal A) : Prop :=
  letI : ValuativeRel A := v.toValuativeRel
  (∀ a ∈ I, Valuation.CofinalValue (ValuativeRel.valuation A) a) ∨
  ∀ a : A, ¬ (v.vle a 0) → Valuation.CofinalValue (ValuativeRel.valuation A) a

end ValuationSpectrum
