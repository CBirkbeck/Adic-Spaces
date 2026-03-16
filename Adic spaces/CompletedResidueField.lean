/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicSpectrum

/-!
# Completed Residue Fields of the Adic Spectrum

For a Huber pair `(A, A⁺)` and a point `v ∈ Spa(A, A⁺)`, the *completed residue field*
at `v` is the completion of `Frac(A / supp(v))` with respect to the valuation topology
induced by `v`.

## Main definitions

* `ValuationSpectrum.completedResidueField A x` : The completed residue field at a point
  `x ∈ Spa(A, A⁺)`. This is currently a placeholder (`sorry`-based) definition; the full
  construction requires the valuation topology on the fraction field.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Section 2.4
-/

universe u

namespace ValuationSpectrum

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- The completed residue field at a point of the adic spectrum.

For `v ∈ Spa(A, A⁺)`, this should be the completion of `FractionRing (A ⧸ v.supp)` with
respect to the valuation topology induced by `v`. This is a placeholder definition; the
full construction requires the valuation topology on the fraction field. -/
noncomputable def completedResidueField (_ : ↥(Spa A A⁺)) : Type u := sorry

/-- The completed residue field carries a commutative ring structure (placeholder). -/
noncomputable instance completedResidueField.instCommRing
    (x : ↥(Spa A A⁺)) : CommRing (completedResidueField A x) := sorry

end ValuationSpectrum
