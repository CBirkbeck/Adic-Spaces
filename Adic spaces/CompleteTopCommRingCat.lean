/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing

/-!
# Category of Complete Topological Commutative Rings

We define `CompleteTopCommRingCat`, the category of complete separated (T₀)
topological commutative rings with continuous ring homomorphisms as morphisms.

This is the target category for the structure presheaf `𝒪_X` on adic spectra,
following §8.1 of [Wedhorn, *Adic Spaces*]. The presheaf values `A⟨T/s⟩`
(completions of localizations) are objects of this category.

## Main definitions

* `CompleteTopCommRingCat` : Bundled complete separated topological commutative ring.
* `CompleteTopCommRingCat.of R` : Constructor from a type with appropriate instances.
* `hasForgetToTopCommRingCat` : Forgetful functor to `TopCommRingCat`.
* `hasForgetToCommRingCat` : Forgetful functor to `CommRingCat`.
* `hasForgetToTopCat` : Forgetful functor to `TopCat`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1
-/

universe u

open CategoryTheory

/-- A bundled complete separated topological commutative ring.

Objects are commutative rings equipped with a compatible uniform space structure
that is complete and T₀ (separated). Morphisms are continuous ring homomorphisms.

This is the target category for presheaf values in the theory of adic spaces
(§8.1 of Wedhorn): each `A⟨T/s⟩` is a completion of a localization, hence
a complete separated topological ring. -/
structure CompleteTopCommRingCat where
  of ::
  /-- The carrier type. -/
  α : Type u
  [instCommRing : CommRing α]
  [instTopologicalSpace : TopologicalSpace α]
  [instIsTopologicalRing : IsTopologicalRing α]
  [instUniformSpace : UniformSpace α]
  [instIsUniformAddGroup : IsUniformAddGroup α]
  [instCompleteSpace : CompleteSpace α]
  [instT0Space : T0Space α]

namespace CompleteTopCommRingCat

instance : CoeSort CompleteTopCommRingCat.{u} (Type u) :=
  ⟨CompleteTopCommRingCat.α⟩

attribute [instance] instCommRing instTopologicalSpace instIsTopologicalRing
  instUniformSpace instIsUniformAddGroup instCompleteSpace instT0Space

instance : Category CompleteTopCommRingCat.{u} where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, continuous_id⟩
  comp f g := ⟨g.val.comp f.val, g.2.comp f.2⟩

instance (R S : CompleteTopCommRingCat.{u}) :
    FunLike { f : R →+* S // Continuous f } R S where
  coe f := f.val
  coe_injective' _ _ h := Subtype.ext (DFunLike.coe_injective h)

instance : ConcreteCategory CompleteTopCommRingCat.{u}
    (fun R S => { f : R →+* S // Continuous f }) where
  hom f := f
  ofHom f := f

/-- The forgetful functor to `TopCommRingCat` (forget completeness and separation). -/
def forgetToTopCommRingCat : CompleteTopCommRingCat.{u} ⥤ TopCommRingCat.{u} where
  obj R := TopCommRingCat.of R
  map f := ⟨f.val, f.2⟩

/-- The forgetful functor to `CommRingCat` (forget topology). -/
def forgetToCommRingCat : CompleteTopCommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R
  map f := CommRingCat.ofHom f.val

/-- The forgetful functor to `TopCat` (forget ring structure). -/
def forgetToTopCat : CompleteTopCommRingCat.{u} ⥤ TopCat.{u} where
  obj R := TopCat.of R
  map f := TopCat.ofHom ⟨⇑f.1, f.2⟩

end CompleteTopCommRingCat
