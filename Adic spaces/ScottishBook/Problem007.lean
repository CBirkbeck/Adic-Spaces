/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».Uniform

/-!
# Nonarchimedean Scottish Book — Problem 7

**Proposer:** Kiran S. Kedlaya | **Date:** 18 December 2015

## Statement

> Let `(A, A⁺)` be a sheafy uniform Huber pair. Is `(A, A⁺)` necessarily stably uniform?

## Notes

Remains open even for strongly noetherian `A` (Alex Mathers, 26 Apr 2022).

## Mathematical Background

A Huber pair `(A, A⁺)` is **uniform** if the subring `A°` of power-bounded elements is
bounded (Definition 7.36 of Wedhorn). It is **stably uniform** if for every rational
localization `(A, A⁺) → (B, B⁺)`, the pair `(B, B⁺)` is again uniform.

The importance of this problem: stably uniform implies sheafy (Buzzard–Verberkmoes), so
this asks whether the converse holds among uniform Huber pairs.

## Definitions to formalize

1. `IsUniform A` — the set `A°` of power-bounded elements is bounded
2. `IsStablyUniform A` — every rational localization is uniform
3. The problem statement: `IsSheafy A → IsUniform A → IsStablyUniform A`

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 7
* Wedhorn, *Adic Spaces*, §7 (Definitions 7.36, 7.37)
* Buzzard–Verberkmoes, *Stably uniform affinoids are sheafy*
-/

open TopologicalRing ValuationSpectrum

namespace ScottishBook

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Re-export uniform definitions

The classes `IsUniform` and `IsStablyUniform` are defined in
`TopologicalRing` namespace in `Adic spaces/Uniform.lean`
(Definitions 7.36, 7.37 of Wedhorn). We re-export them here
for use in the ScottishBook namespace. -/

/-- Alias for `TopologicalRing.IsUniform` in the ScottishBook namespace. -/
abbrev IsUniform := TopologicalRing.IsUniform A

/-- Alias for `TopologicalRing.IsStablyUniform` in the ScottishBook namespace. -/
abbrev IsStablyUniform [PlusSubring A] [HasRestrictionMaps A] :=
  TopologicalRing.IsStablyUniform A

/-! ### The open problem -/

/-- **Scottish Book Problem 7** (Kedlaya, 18 Dec 2015):
*Every sheafy uniform Huber pair is stably uniform.*

This is an **open problem** — the `sorry` is intentional and represents the open question.
Formalized here as an axiom-free statement to serve as a target for partial results. -/
theorem problem7 [PlusSubring A] [HasRestrictionMaps A] [IsSheafy A]
    [TopologicalRing.IsUniform A] :
    TopologicalRing.IsStablyUniform A := by
  sorry

/-! ### Partial results and related facts -/

/-- Stably uniform implies uniform (the converse direction is trivial). -/
theorem IsStablyUniform.isUniform [PlusSubring A] [HasRestrictionMaps A]
    [TopologicalRing.IsStablyUniform A] : TopologicalRing.IsUniform A := by
  sorry -- needs: identify A with its own trivial localization

/-- Stably uniform implies sheafy (Buzzard–Verberkmoes).
This is the known implication; Problem 7 asks about the converse for uniform pairs. -/
theorem IsStablyUniform.isSheafy [PlusSubring A] [HasRestrictionMaps A]
    [TopologicalRing.IsStablyUniform A] : IsSheafy A := by
  sorry -- needs: Buzzard–Verberkmoes argument

end ScottishBook
