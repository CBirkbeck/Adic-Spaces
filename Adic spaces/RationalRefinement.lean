/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf

/-!
# Concrete Refinement for Rational Coverings

If a finer covering (same base, each piece inside some piece of the original)
has the separation property (jointly injective restriction maps), then so does
the original covering. This is the concrete version of Proposition A.3 of Wedhorn.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition A.3
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [HasRestrictionMaps A]

/-- A rational covering has the *separation property* if the restriction
maps to the covering pieces are jointly injective. -/
def RationalCovering.HasSeparation (C : RationalCovering A) : Prop :=
  ∀ x y : presheafValue C.base,
    (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMap C.base D (C.hsubset D hD) x =
      restrictionMap C.base D (C.hsubset D hD) y) → x = y

/-- **Refinement preserves separation (Proposition A.3 of Wedhorn).**

Given a covering `C` and a finer covering `V_covers` of the same base,
if V has separation then C has separation. Uses `restrictionMap_comp`. -/
theorem separation_of_finer_rational (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (hV_sep : ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ V_covers),
        restrictionMap C.base D (hV_subset D hD) x =
        restrictionMap C.base D (hV_subset D hD) y) → x = y)
    (x y : presheafValue C.base)
    (hC : ∀ (E : RationalLocData A) (hE : E ∈ C.covers),
      restrictionMap C.base E (C.hsubset E hE) x =
      restrictionMap C.base E (C.hsubset E hE) y) :
    x = y := by
  apply hV_sep
  intro D hD
  let E := (τ ⟨D, hD⟩).1
  have hE : E ∈ C.covers := (τ ⟨D, hD⟩).2
  have hDE : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s := hτ ⟨D, hD⟩
  have hE_eq := hC E hE
  have hcomp := restrictionMap_comp C.base E D (C.hsubset E hE) hDE
  have hsub : hV_subset D hD = hDE.trans (C.hsubset E hE) :=
    Subsingleton.elim _ _
  rw [hsub, ← congr_fun hcomp x, ← congr_fun hcomp y]
  exact congrArg (restrictionMap E D hDE) hE_eq

end ValuationSpectrum
