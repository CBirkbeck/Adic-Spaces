/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PseudoUniformizer
import «Adic spaces».Uniform
import «Adic spaces».StructureSheaf

/-!
# Perfectoid Rings and Fields

We define **perfectoid rings** and **perfectoid fields** following Scholze's
*Perfectoid Spaces* (2012), Definition 3.5.

## Main definitions

* `IsPerfectoidRing p A` : A Tate ring `A` is perfectoid (for a prime `p`) if it is
  complete, separated, uniform, and admits a pseudo-uniformizer `ϖ` such that `ϖ^p | p`
  in `A°` and the Frobenius is surjective on `A°/ϖ`.
* `IsPerfectoidField p K` : A perfectoid field is a perfectoid ring that is also a field.

## Implementation notes

The Frobenius surjectivity condition is expressed directly as:
for all power-bounded `x`, there exists power-bounded `y` and `z` with `x = y^p + ϖ·z`
and `z` power-bounded. This avoids forming the quotient ring `A°/ϖ` and establishing
`CharP` on it, which would require considerable typeclass infrastructure.

The condition `ϖ^p | p` is expressed as: there exists a power-bounded `c` with
`(p : A) = c * ϖ^p`. This says `p/ϖ^p ∈ A°`, which is the standard formulation.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], Definition 3.5
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7
-/

open TopologicalRing ValuationSpectrum

universe u

/-! ### Perfectoid rings -/

/-- A Tate ring `A` is a **perfectoid ring** (for a prime `p`) if:

1. `A` is complete and separated (T₀),
2. `A` is uniform (A° is bounded),
3. there exists a pseudo-uniformizer `ϖ` that is power-bounded, such that `ϖ^p | p`
   in `A°` (i.e., `p = c · ϖ^p` for some power-bounded `c`), and
4. the `p`-th power (Frobenius) map is surjective on `A°/ϖ` (i.e., for every
   power-bounded `x`, there exist power-bounded `y, z` with `x = y^p + ϖ · z`).

(Scholze, *Perfectoid Spaces*, Definition 3.5) -/
class IsPerfectoidRing (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] : Prop
    extends IsTateRing A where
  /-- The ring is complete with respect to its uniform structure. -/
  complete : CompleteSpace A
  /-- The topology is T₀ (separated). -/
  t0 : T0Space A
  /-- The ring is uniform: `A°` is bounded. -/
  uniform : IsUniform A
  /-- There exists a pseudo-uniformizer `ϖ` that is power-bounded, with `ϖ^p | p` in `A°`
  and Frobenius surjective on `A°/ϖ`. -/
  exists_pseudoUniformizer :
    ∃ (ϖ : PseudoUniformizer A),
      -- ϖ is power-bounded
      IsPowerBounded (ϖ.val : A) ∧
      -- ϖ^p divides p in A°: there exists power-bounded c with p = c · ϖ^p
      (∃ c : A, IsPowerBounded c ∧ (p : A) = c * ((ϖ.val : A) ^ p)) ∧
      -- Frobenius is surjective on A°/ϖ: for every power-bounded x,
      -- there exist power-bounded y, z with x = y^p + ϖ · z
      (∀ x : A, IsPowerBounded x →
        ∃ y : A, IsPowerBounded y ∧
          ∃ z : A, IsPowerBounded z ∧ x = y ^ p + (ϖ.val : A) * z)

/-! ### Perfectoid fields -/

/-- A **perfectoid field** is a field that is also a perfectoid ring
(Scholze, *Perfectoid Spaces*, Definition 3.5). -/
class IsPerfectoidField (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K] : Prop
    extends IsPerfectoidRing p K where

/-! ### Basic properties -/

namespace IsPerfectoidRing

/-- Extract a pseudo-uniformizer with the perfectoid property from a perfectoid ring. -/
noncomputable def perfectoidPseudoUniformizer (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    PseudoUniformizer A :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose

/-- The perfectoid pseudo-uniformizer is power-bounded. -/
theorem perfectoidPseudoUniformizer_isPowerBounded (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    IsPowerBounded ((perfectoidPseudoUniformizer p A).val : A) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.1

/-- The perfectoid pseudo-uniformizer satisfies ϖ^p | p. -/
theorem perfectoidPseudoUniformizer_divides_p (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∃ c : A, IsPowerBounded c ∧
      (p : A) = c * (((perfectoidPseudoUniformizer p A).val : A) ^ p) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.2.1

/-- Frobenius is surjective on A°/ϖ for the perfectoid pseudo-uniformizer. -/
theorem perfectoidPseudoUniformizer_frobenius_surj (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∀ x : A, IsPowerBounded x →
      ∃ y : A, IsPowerBounded y ∧
        ∃ z : A, IsPowerBounded z ∧
          x = y ^ p + ((perfectoidPseudoUniformizer p A).val : A) * z :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.2.2

/-! ### Sorry'd deep theorems -/

/-- **Perfectoid rings are stably uniform** (Scholze, *Perfectoid Spaces*, Theorem 5.2).

This is a deep result: the key step is to show that for any rational localization
`R(T/s)` of a perfectoid ring, the completed localization is again uniform. The
proof goes through almost mathematics and tilting. -/
theorem toIsStablyUniform (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [HasRestrictionMaps A] :
    IsStablyUniform A := sorry

/-- **Perfectoid rings are sheafy** (Scholze, *Perfectoid Spaces*, Theorem 6.3).

This follows from stable uniformity: Buzzard--Verberkmoes showed that stably
uniform Tate rings are sheafy. -/
theorem toIsSheafy (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [HasRestrictionMaps A] :
    IsSheafy A := sorry

end IsPerfectoidRing
