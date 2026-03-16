import «Adic spaces».RestrictedPowerSeries
import Mathlib.RingTheory.RingHom.Flat

/-!
# Nonarchimedean Scottish Book — Problem 29

**Proposer:** Alexander Zavyalov
**Date:** 6 June 2019

## Problem Statement

Let A → B be a flat continuous morphism of complete strongly noetherian Tate-Huber rings.
Does flatness of A⟨T⟩ → B⟨T⟩ follow?

## Notes

None.

## Status

RESOLVED: No (Gabber counterexample).

## Definitions needed

- **Strongly noetherian**: A Tate ring A such that A⟨T_1, ..., T_n⟩ is noetherian for
  all n.
- **Tate algebra A⟨T⟩**: The ring of restricted power series in one variable over A,
  i.e., `restrictedMvPowerSeriesSubring 1 A`.
-/

namespace ScottishBook

universe u

/-! ### Functorial map on restricted power series -/

/-- The canonical ring homomorphism `A⟨T⟩ → B⟨T⟩` induced by a continuous ring
homomorphism `f : A →+* B`. This is the functorial action of the restricted power
series construction on morphisms.

Uses `restrictedMvPowerSeriesSubring 1 A` as the canonical one-variable restricted
power series ring. -/
noncomputable def restrictedPowerSeriesMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) :
    restrictedMvPowerSeriesSubring 1 A →+* restrictedMvPowerSeriesSubring 1 B := sorry

/-! ### Problem 29: Counterexample -/

/-- **Scottish Book Problem 29** (Zavyalov, 6 June 2019; resolved: No, by Gabber):

*Let `A → B` be a flat continuous morphism of complete strongly noetherian Tate-Huber
rings. Does `A⟨T⟩ → B⟨T⟩` remain flat?*

Gabber constructed a counterexample showing that flatness of restricted power series
does **not** follow from flatness of the base morphism, even under the strong
hypotheses of completeness, strong noetherianity, and the Tate condition.

The existential asserts: there exist complete strongly noetherian Tate rings `A`, `B`
with a flat continuous ring homomorphism `f : A →+* B` such that the induced map
`restrictedPowerSeriesMap f : A⟨T⟩ →+* B⟨T⟩` is **not** flat.

The `sorry` represents Gabber's counterexample construction. -/
theorem problem29_counterexample :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : @IsTopologicalRing A _ _) (_ : @IsTopologicalRing B _ _)
      (_ : @IsStronglyNoetherian A _ _ _) (_ : @IsStronglyNoetherian B _ _ _)
      (f : A →+* B),
      Continuous f ∧
      f.Flat ∧
      ¬ (@restrictedPowerSeriesMap A B _ _ _ _ _ _ f).Flat := by
  sorry

end ScottishBook
