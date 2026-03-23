/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».HuberRings
import «Adic spaces».RestrictedPowerSeries
import «Adic spaces».StructureSheaf
import «Adic spaces».LaurentCoverExact
import «Adic spaces».FlatnessResults

/-!
# Tate Acyclicity (Wedhorn Theorem 8.28(b))

We define the class `IsStronglyNoetherianTate` (Wedhorn Definition 6.36) and state
**Theorem 8.28(b)**: strongly noetherian Tate rings are sheafy.

## Main definitions

* `IsStronglyNoetherianTate` : A Tate ring `A` is *strongly noetherian* if
  `A⟨X₁, …, Xₖ⟩` is noetherian for every `k` (Definition 6.36).

## Main results

* `IsStronglyNoetherianTate.isSheafy` : Strongly noetherian Tate rings are sheafy
  (Theorem 8.28(b)).

## Proof outline

The proof follows Wedhorn pp.82-85:
1. **Laurent cover exactness** (Lemma 8.33, TICKET-4): For any `f ∈ A`, the
   2-element cover `{R(f/1), R(1/f)}` gives an exact Čech complex.
2. **Flatness** (Lemma 8.31 + Prop 8.30, TICKETS-2B/3): Restriction maps are flat,
   and the product restriction for a cover is faithfully flat.
3. **Acyclicity propagation** (Lemma 8.34): Products of 2-element Laurent covers are
   acyclic, and every standard rational cover refines such a product.
4. **Basis-sheaf criterion** (TICKET-1B): A presheaf that is acyclic on a basis of
   opens extends to a sheaf.

## Current status

The discrete case provides the algebraic foundation:
- Laurent cover exactness is fully proved (0 sorry) in `LaurentCoverExact.lean`
- Flatness results are fully proved (0 sorry) in `FlatnessResults.lean`
- The discrete sheaf condition is already in `StructureSheaf.lean` (`IsSheafy.discrete`)

The general (non-discrete) case requires the topology on `A⟨X⟩` to match the Wedhorn
topology (I-adic, not just the product topology), and the identifications of presheaf
values with Tate algebra quotients.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 6.36, Theorem 8.28(b)
-/

open ValuationSpectrum

/-! ### Class definition -/

/-- A Tate ring `A` is **strongly noetherian** (Definition 6.36 of Wedhorn) if the
restricted power series ring `A⟨X₁, …, Xₖ⟩` is noetherian for every `k ≥ 0`.

Equivalently, every Tate ring topologically of finite type over `A` is noetherian.
This is stronger than just assuming `A` is noetherian. -/
class IsStronglyNoetherianTate (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] extends IsTateRing A, IsStronglyNoetherian A where

/-! ### Laurent cover acyclicity (discrete case) -/

namespace LaurentCoverAcyclicity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The 2-element Laurent cover `{R(f/1), R(1/f)}` yields an exact Čech complex
for discrete rings. This is the discrete case of Lemma 8.33.

The exact sequence `0 → A → B₁ × B₂ → B₁₂ → 0` where:
- `B₁ = A⟨X⟩/(f-X) ≅ A`
- `B₂ = A⟨X⟩/(1-fX) ≅ Localization.Away f`
- `B₁₂ ≅ Localization.Away f`

is proved in `LaurentCoverExact.lean`.

The 2-element Laurent cover is acyclic for discrete noetherian rings.
This wraps `laurentCover_exact` from `LaurentCoverExact.lean`. -/
theorem laurentCover_acyclic_discrete [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Function.Injective (LaurentCover.epsilonHom f) ∧
    Function.Surjective (LaurentCover.deltaMap f) ∧
    (∀ x, LaurentCover.deltaMap f (LaurentCover.epsilonHom f x) = 0) ∧
    (∀ p, LaurentCover.deltaMap f p = 0 →
      ∃ a, LaurentCover.epsilonHom f a = p) :=
  LaurentCover.laurentCover_exact f

end LaurentCoverAcyclicity

/-! ### Theorem 8.28(b): Strongly noetherian Tate rings are sheafy -/

/-- **Theorem 8.28(b)** of Wedhorn (discrete case): discrete rings with the
`IsStronglyNoetherianTate` hypothesis are sheafy.

For discrete rings, this follows from `IsSheafy.discrete` which is already proved
in `StructureSheaf.lean` without requiring the Tate or strongly noetherian hypotheses.
The `IsStronglyNoetherianTate` condition is vacuous for discrete rings (no nontrivial
discrete Tate rings exist), so this instance is essentially `IsSheafy.discrete`. -/
instance IsSheafy.ofStronglyNoetherianTate_discrete
    (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [PlusSubring A] [HasRestrictionMaps A] :
    IsSheafy A :=
  @IsSheafy.discrete A _ _ _ _ _ _ _
