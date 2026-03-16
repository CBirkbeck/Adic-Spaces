/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AdicSpectrum

/-!
# Nonarchimedean Scottish Book — Problem 10

**Proposer:** Kiran Kedlaya
**Date:** 18 December 2015

## Problem Statement

Let (A, A+) be a Huber pair with Spa(A, A+) analytic (i.e., having no trivial valuation
points). Does it follow that A is Tate?

## Notes

None.

## Status

RESOLVED: No (counterexample by Kedlaya, 19 December 2016).

## Mathematical Background

A valuation `v` on `A` is **trivial** if all nonzero elements are equivalent under `v`,
i.e., `v(a) ≤ v(b)` whenever `a` is in the support or `b` is not in the support. In our
`ValuativeRel` framework, this means every two elements outside the support satisfy
`v(a) ≤ v(b)`. See `ValuationSpectrum.IsTrivialValuation` in `AnalyticPoints.lean`.

An adic spectrum `Spa(A, A⁺)` is **analytic** if it contains no points corresponding to
trivial valuations. This is equivalent to saying every point `v ∈ Spa(A, A⁺)` has the
property that `supp(v)` is not open (Definition 8.35 of Wedhorn), since for a Huber pair
the trivial valuations are precisely those whose support is open.
See `ValuationSpectrum.SpaIsAnalytic` in `AnalyticPoints.lean`.

The problem asks whether analyticity of `Spa(A, A⁺)` forces `A` to be a Tate ring. Kedlaya
gave a counterexample showing the answer is no.

## Definitions formalized

1. `ValuationSpectrum.IsTrivialValuation v` -- all elements outside the support are
   `v`-equivalent (in `AnalyticPoints.lean`)
2. `ValuationSpectrum.SpaIsAnalytic A` -- no trivial valuation point lies in `Spa(A, A⁺)`
   (in `AnalyticPoints.lean`)
3. `problem10_counterexample` -- existence of an analytic non-Tate Huber pair

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 10
* Wedhorn, *Adic Spaces*, Definition 8.35, Proposition 8.36
-/

open ValuationSpectrum

namespace ScottishBook

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### Properties of trivial valuations -/

/-- A trivial valuation satisfies `v(a) ≤ v(b)` iff `a ∈ supp(v)` or `b ∉ supp(v)`. -/
theorem IsTrivialValuation.vle_iff {v : Spv A} (hv : IsTrivialValuation v)
    (a b : A) : v.vle a b ↔ (a ∈ v.supp ∨ b ∉ v.supp) := by
  sorry

/-- If `v` is a trivial valuation and `v ∈ Spa(A, A⁺)`, then `v` is not analytic in the
sense of `ValuationSpectrum.IsAnalytic` (i.e., `supp(v)` is open) when `A` is a Huber ring
with open topological nilradical. -/
theorem IsTrivialValuation.supp_isOpen_of_isHuberRing [IsTopologicalRing A] [IsHuberRing A]
    [IsLinearTopology A A] {v : Spv A} (hv : IsTrivialValuation v) :
    IsOpen (v.supp : Set A) := by
  sorry

/-! ### Analytic adic spectra: properties -/

/-- In a Tate ring, `Spa(A, A⁺)` is analytic (Proposition 8.36 of Wedhorn).
This is one direction of the relationship explored in Problem 10. -/
theorem ValuationSpectrum.IsTateRing.spaIsAnalytic [IsTopologicalRing A] [PlusSubring A]
    [IsLinearTopology A A] [IsTateRing A] : SpaIsAnalytic A := by
  sorry

/-! ### Problem 10: the (false) conjecture and its negation -/

/-- **Scottish Book Problem 10** (Kedlaya, 18 Dec 2015, resolved 19 Dec 2016):

*If `Spa(A, A⁺)` is analytic, is `A` necessarily Tate?*

The answer is **no**. We state the negation: there exists a Huber pair `(A, A⁺)` such that
`Spa(A, A⁺)` is analytic but `A` is not a Tate ring.

The `sorry` stands for Kedlaya's counterexample construction. -/
theorem problem10_counterexample :
    ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (_ : PlusSubring A),
      SpaIsAnalytic A ∧ ¬ IsTateRing A := by
  sorry

end ScottishBook
