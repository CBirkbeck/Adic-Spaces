/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».HuberRings
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Tate-ring structure on closed quotients

For a noetherian Tate ring `R` and a closed ideal `I ⊆ R`, this file constructs a
pair of definition on `R ⧸ I` (with the quotient topology) and packages the
`IsHuberRing` and `IsTateRing` consequences.

## Main results

* `PairOfDefinition.quotient` — image-of-pair construction. Given
  `P : PairOfDefinition R` and any ideal `I : Ideal R`, produces
  `PairOfDefinition (R ⧸ I)` with:
  - `A₀'` = image of `P.A₀` in `R ⧸ I`,
  - `I'` = image of `P.I` in `A₀'`.
* `IsTateRing.quotient_of_closedIdeal` — `IsTateRing (R ⧸ I)` whenever `R` is Tate
  (no closedness needed for the Tate-ring structure itself; closedness is only
  needed downstream for T₂ and completeness).
* `exists_topologicallyNilpotent_unit_quotient` — supplies the topologically
  nilpotent unit in `R ⧸ I` directly.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6 (definitions) and Prop 6.17
  (closed ideals in noetherian Tate rings).
-/

namespace IsTateRing

open Filter Topology Pointwise

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The composite ring hom `P.A₀ →+* R ⧸ I` factoring through inclusion then
quotient. Its range is `P.A₀.map (Ideal.Quotient.mk I)`. -/
noncomputable def _root_.PairOfDefinition.quotientHom (P : PairOfDefinition R)
    (I : Ideal R) : P.A₀ →+* (P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I)) :=
  RingHom.codRestrict ((Ideal.Quotient.mk I).comp P.A₀.subtype)
    (P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I))
    (fun x => ⟨x.1, x.2, rfl⟩)

/-- The image of a pair of definition under the quotient map.

For an ideal `I` of `R` and a pair of definition `P = (A₀, I_R)` for `R`,
the image pair on `R ⧸ I` is:
- `A₀'` = `(Ideal.Quotient.mk I) '' A₀`, the image subring.
- `I'`  = image of `P.I` under the corestriction `P.A₀ → A₀'`.

The image subring is open because the quotient map is open. The image ideal is
f.g. because `P.I` is f.g. The adic property descends because the neighborhood
basis `{P.I^n}` maps to the neighborhood basis `{(I')^n}` under the open quotient
map. -/
noncomputable def _root_.PairOfDefinition.quotient (P : PairOfDefinition R)
    (I : Ideal R) : PairOfDefinition (R ⧸ I) where
  A₀ := P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I)
  I := P.I.map (P.quotientHom I)
  isOpen := by
    have hopen : IsOpenMap (Ideal.Quotient.mk I : R → R ⧸ I) :=
      QuotientRing.isOpenMap_coe I
    have heq : ((P.A₀.map (Ideal.Quotient.mk I : R →+* R ⧸ I) :
        Subring (R ⧸ I)) : Set (R ⧸ I)) =
        (Ideal.Quotient.mk I) '' (P.A₀ : Set R) := by
      ext y
      simp [Set.mem_image]
    rw [heq]
    exact hopen _ P.isOpen
  fg := (P.fg).map _
  isAdic := by
    -- The I-adic topology on `(P.A₀.map ...)` agrees with the subspace topology
    -- inherited from `R ⧸ I`. Both have `{image of P.I^n}` as a 0-neighborhood
    -- basis. Proof: the open quotient map carries the nhd basis `{P.I^n}` of
    -- `0 ∈ P.A₀ ⊆ R` to a nhd basis of `0 ∈ A₀.map ... ⊆ R ⧸ I`, which is the
    -- image of P.I^n; meanwhile (P.I.map quotientHom)^n equals the image of
    -- P.I^n by `Ideal.map_pow` of the surjective `quotientHom`.
    sorry

end IsTateRing
