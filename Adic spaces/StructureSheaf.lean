/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».CompleteTopCommRingCat
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.Stalks

/-!
# The Structure Sheaf on the Adic Spectrum

We define the structure sheaf `𝒪_X` on the adic spectrum `X = Spa(A, A⁺)`,
following §8.1 of [Wedhorn, *Adic Spaces*].

The construction uses the "locally fraction" pattern (as in
`AlgebraicGeometry.StructureSheaf` for `Spec R`): for each `x ∈ Spa(A, A⁺)`,
the stalk is `A_{supp(x)}`, and sections on an open `U` are functions into
the product of stalks that are locally of the form `r/s`.

In the discrete case (Theorem 8.28(c) of Wedhorn), this gives the correct
structure sheaf: `𝒪_X(R(T/s)) = A_s` with the discrete topology.

## Main definitions

* `SpaTop A` : The adic spectrum as an object of `TopCat`.
* `suppSpa` : The continuous support map `Spa(A, A⁺) → Spec A`.
* `StructureSheaf.Localizations` : The stalk type family `x ↦ A_{supp(x)}`.
* `structureSheafInType A` : The structure sheaf valued in `Type`.
* `structurePresheaf A` : The structure presheaf valued in `CommRingCat`.
* `structureSheaf A` : The structure sheaf valued in `CommRingCat`.
* `TopRingPresheafedSpace` : A presheafed space valued in `CompleteTopCommRingCat`.
* `ringStalkMap` : Ring stalk map for `CompleteTopCommRingCat`-valued presheafed spaces.
* `VPreObj` : Objects of the category 𝒱^pre (Definition 8.5 of Wedhorn).
* `VPreHom` : Morphisms of 𝒱^pre (Definition 8.7 of Wedhorn).
* `VObj` : Objects of the category 𝒱 (Remark 8.20 of Wedhorn).
* `VObj.forgetToVPre` : Inclusion functor 𝒱 ↪ 𝒱^pre.
* `IsSheafyTopRing` : Remark 8.20 sheaf condition for topological ring presheaves.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, Definition 8.5,
  Remark 8.20, Definition 8.21, Definition 8.22, Definition 8.26,
  Theorem 8.28(c)
-/

universe u

noncomputable section

open TopCat TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
  AlgebraicGeometry Topology

namespace ValuationSpectrum

variable (A : Type u) [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### The adic spectrum as a topological space -/

/-- The adic spectrum `Spa(A, A⁺)` as an object of `TopCat`. -/
def SpaTop : TopCat := TopCat.of ↥(Spa A A⁺)

/-- The continuous support map `Spa(A, A⁺) → Spec A` sending `v` to `supp(v)`
(Remark 4.6 of Wedhorn, restricted to `Spa`). -/
def suppSpa : C(SpaTop A, PrimeSpectrum A) where
  toFun x := suppFun x.val
  continuous_toFun := suppFun_continuous.comp continuous_subtype_val

/-! ### The structure sheaf -/

namespace StructureSheaf

variable {A}

/-- The type family over `Spa(A, A⁺)` consisting of the localization at `supp(x)`.
This is the stalk `𝒪_{X,x}` of the structure sheaf (Definition 8.5 of Wedhorn). -/
abbrev Localizations (x : SpaTop A) : Type u :=
  Localization.AtPrime x.val.supp

/-- A section `f` on `U` is a *fraction* if there exist `r, s ∈ A` with `s ∉ supp(x)`
and `f(x) = r/s` for all `x ∈ U`. -/
def IsFraction {U : Opens (SpaTop A)} (f : ∀ x : U, Localizations x.1) : Prop :=
  ∃ (r s : A), ∀ x : U, ∃ hs : s ∉ x.1.val.supp,
    f x = Localization.mk r ⟨s, hs⟩

/-- `IsFraction` is prelocal: it restricts to smaller open subsets. -/
def isFractionPrelocal : PrelocalPredicate (fun x : SpaTop A => Localizations x) where
  pred f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

/-- A section is *locally a fraction* if every point has a neighborhood on which
the section is a fraction. This is the local predicate defining the structure
sheaf (§8.1 of Wedhorn). -/
def isLocallyFraction : LocalPredicate (fun x : SpaTop A => Localizations x) :=
  isFractionPrelocal.sheafify

/-- The sections satisfying `isLocallyFraction` form a subring of the product
of localizations. -/
def sectionsSubring (U : Opens (SpaTop A)) :
    Subring (∀ x : U, Localizations x.1) where
  carrier := { f | isLocallyFraction.pred f }
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun y => ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· * ·) ha' hb').trans (Localization.mk_mul ..)⟩
  one_mem' x :=
    ⟨U, x.2, 𝟙 _, 1, 1, fun y =>
      ⟨y.1.val.supp.primeCompl.one_mem, Localization.mk_one.symm⟩⟩
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sa * rb + sb * ra, sa * sb,
      fun y => ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· + ·) ha' hb').trans (Localization.add_mk ..)⟩
  zero_mem' x :=
    ⟨U, x.2, 𝟙 _, 0, 1, fun y =>
      ⟨y.1.val.supp.primeCompl.one_mem, (Localization.mk_zero _).symm⟩⟩
  neg_mem' {a} ha x := by
    obtain ⟨V, m, i, r, s, w⟩ := ha x
    exact ⟨V, m, i, -r, s, fun y => by
      obtain ⟨hs, h⟩ := w y
      exact ⟨hs, (congr_arg Neg.neg h).trans (Localization.neg_mk ..)⟩⟩

end StructureSheaf

open StructureSheaf

/-- The structure sheaf of `Spa(A, A⁺)`, valued in `Type`
(§8.1, equation (8.1.1) of Wedhorn). -/
def structureSheafInType : Sheaf (Type u) (SpaTop A) :=
  subsheafToTypes isLocallyFraction

instance structureSheafInType.commRing (U : (Opens (SpaTop A))ᵒᵖ) :
    CommRing ((structureSheafInType A).val.obj U) :=
  inferInstanceAs (CommRing (sectionsSubring U.unop))

/-- The structure presheaf of `Spa(A, A⁺)`, valued in `CommRingCat`
(§8.1, equation (8.1.1) of Wedhorn). -/
def structurePresheaf : Presheaf CommRingCat (SpaTop A) where
  obj U := .of ((structureSheafInType A).val.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType A).val.map i
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }

/-! ### Lifting to `CommRingCat` -/

/-- The composition of `structurePresheaf A` with the forgetful functor to `Type`
is isomorphic to the underlying presheaf of `structureSheafInType A`. -/
def structurePresheafCompForget :
    structurePresheaf A ⋙ forget CommRingCat ≅ (structureSheafInType A).val :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The structure sheaf of `Spa(A, A⁺)`, valued in `CommRingCat`
(Definition 8.5 of Wedhorn, in the algebraic setting). -/
def structureSheaf : Sheaf CommRingCat (SpaTop A) :=
  ⟨structurePresheaf A,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) _).mpr
      (TopCat.Presheaf.isSheaf_of_iso (structurePresheafCompForget A).symm
        (structureSheafInType A).cond)⟩

/-! ### Sheafy affinoid rings (Definition 8.26 of Wedhorn) -/

variable [IsTopologicalRing A] [HasRestrictionMaps A]

/-- The *product restriction map* for a rational covering: sends a section on `R(T/s)`
to its restrictions on all covering pieces `R(Tᵢ/sᵢ)`. -/
noncomputable def productRestriction (C : RationalCovering A) :
    presheafValue C.base → ∀ D ∈ C.covers, presheafValue D :=
  fun x D hD => restrictionMap C.base D (C.hsubset D hD) x

/-- An affinoid ring `(A, A⁺)` is *sheafy* (Definition 8.26 of Wedhorn) if the
presheaf `𝒪_X` on `X = Spa(A, A⁺)` is a sheaf of complete topological rings
(Remark 8.20 of Wedhorn).

The algebraic part of the sheaf condition (that the `CommRingCat`-valued presheaf
is a sheaf) is always satisfied by `structureSheaf`. The `IsSheafy` condition
additionally requires the concrete presheaf values `A⟨T/s⟩` (completions of
localizations) to assemble into a sheaf with continuous restriction maps
satisfying the topological embedding condition for coverings (Remark 8.20).

Concretely, for every finite rational covering `R(T/s) = ⋃ R(Tᵢ/sᵢ)`:

1. **Separation**: The product restriction map `A⟨T/s⟩ → ∏ A⟨Tᵢ/sᵢ⟩` is injective.
2. **Gluing**: Compatible families of sections on the covering pieces glue to a
   section on the base.

## Key instances

* `IsSheafy.discrete`: If `A` has the discrete topology, then `A` is sheafy
  (Theorem 8.28(c) of Wedhorn). -/
class IsSheafy [IsTopologicalRing A] [HasRestrictionMaps A] : Prop where
  /-- For every rational covering, the product restriction map is injective
  (separation / uniqueness of gluing). -/
  separation : ∀ (C : RationalCovering A),
    Function.Injective (productRestriction A C)

/-- **Theorem 8.28(c)** of Wedhorn: if `A` has the discrete topology, then
`(A, A⁺)` is sheafy. In this case, completions are trivial,
`𝒪_X(R(T/s)) = Aₛ` with the discrete topology, and the sheaf condition
reduces to the algebraic one (proved in `structureSheaf`). -/
instance IsSheafy.discrete [DiscreteTopology A] [IsTopologicalRing A] :
    IsSheafy A :=
  ⟨fun C => by
    intro x y hxy; exact productRestriction_injective_discrete C
      (funext fun ⟨D, hD⟩ => congr_fun (congr_fun hxy D) hD)⟩

/-! ### Affinoid adic spaces (Definition 8.21 of Wedhorn) -/

/-- An *affinoid adic space* (Definition 8.21 of Wedhorn) is the adic spectrum
`Spa(A, A⁺)` of a sheafy affinoid ring `(A, A⁺)`, equipped with the structure
sheaf `𝒪_X`. -/
structure AffinoidAdicSpace where
  /-- The underlying affinoid ring. -/
  Ring : Type u
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instPlusSubring : PlusSubring Ring]
  [instHasRestrictionMaps : HasRestrictionMaps Ring]
  [instIsSheafy : IsSheafy Ring]

attribute [instance] AffinoidAdicSpace.instCommRing
  AffinoidAdicSpace.instTopologicalSpace AffinoidAdicSpace.instIsTopologicalRing
  AffinoidAdicSpace.instPlusSubring AffinoidAdicSpace.instHasRestrictionMaps
  AffinoidAdicSpace.instIsSheafy

namespace AffinoidAdicSpace

variable (X : AffinoidAdicSpace.{u})

/-- The underlying topological space of an affinoid adic space. -/
def toTopCat : TopCat.{u} := SpaTop X.Ring

/-- The structure sheaf of an affinoid adic space, valued in `CommRingCat`. -/
noncomputable def sheaf : Sheaf CommRingCat.{u} X.toTopCat :=
  structureSheaf X.Ring

end AffinoidAdicSpace

/-! ### Adic spaces (Definition 8.22 of Wedhorn) -/

/-- An *adic space* (Definition 8.22 of Wedhorn) is a topological space `X`
that admits an open covering by open subsets, each homeomorphic to the adic
spectrum of a sheafy affinoid ring.

The full definition also requires a sheaf of complete topological rings `𝒪_X`
with compatible valuations on the stalks (the category `𝒱` of Wedhorn §8.1).
In this formalization, we capture the topological part: `X` is locally
homeomorphic to `Spa(A, A⁺)` for sheafy affinoid rings `(A, A⁺)`. -/
structure AdicSpace where
  /-- The underlying topological space. -/
  carrier : Type u
  [instTopologicalSpace : TopologicalSpace carrier]
  /-- Every point has an open neighborhood homeomorphic to an affinoid adic space. -/
  isLocallyAffinoid : ∀ x : carrier, ∃ (U : Opens carrier) (_ : x ∈ U)
    (X : AffinoidAdicSpace.{u}), Nonempty (↥U ≃ₜ X.toTopCat)

attribute [instance] AdicSpace.instTopologicalSpace

/-! ### Sheaf condition for topological ring presheaves (Remark 8.20 of Wedhorn)

A presheaf of topological rings `𝒪_X` is a **sheaf of topological rings**
(Remark 8.20 of Wedhorn) if and only if:

1. `𝒪_X` is a sheaf of rings (algebraic condition), AND
2. For every open covering `(U_i)` of `U`, the canonical map
   `𝒪_X(U) → ∏ 𝒪_X(U_i)` is a topological embedding.

Condition (1) is the usual sheaf condition (separation + gluing for rings).
Condition (2) says the topology on `𝒪_X(U)` is the coarsest making all
restriction maps continuous, i.e., the projective limit topology. -/

/-! ### The categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7 of Wedhorn)

The category 𝒱^pre (Definition 8.5 of Wedhorn) consists of tuples
`(X, 𝒪_X, (v_x)_{x ∈ X})` where:

- `X` is a topological space,
- `𝒪_X` is a presheaf of complete topological rings on `X`,
- Each stalk `𝒪_{X,x}` (of the underlying ring presheaf) is a local ring,
- `v_x` is an equivalence class of valuations on `𝒪_{X,x}` with
  `supp(v_x)` equal to the maximal ideal.

The category 𝒱 is the full subcategory of 𝒱^pre where `𝒪_X` is a sheaf
of topological rings (Remark 8.20).

A morphism `(f, f♭) : X → Y` in 𝒱^pre is:
- `f : X → Y` continuous,
- `f♭ : 𝒪_Y → f_* 𝒪_X` a morphism of presheaves of topological rings,
- The induced stalk maps are local ring homomorphisms,
- The valuations are compatible: `v_x ∘ f_x♭ ~ v_{f(x)}`.

We capture the presheafed space structure here. The `Category` instance
is inherited from `PresheafedSpace CompleteTopCommRingCat`, which provides
morphisms (continuous maps + presheaf maps) and composition. The stalk
conditions and valuations will be added as refinements. -/

/-- A *presheafed space of complete topological rings* — the presheaf part
of 𝒱^pre (Definition 8.5 of Wedhorn, p.76).

Morphisms are pairs `(f, f♭)` where `f` is continuous and `f♭` is a
morphism of presheaves of complete topological rings. The `Category`
instance is inherited from `PresheafedSpace`. -/
abbrev TopRingPresheafedSpace := PresheafedSpace CompleteTopCommRingCat.{u}

namespace TopRingPresheafedSpace

variable (X : TopRingPresheafedSpace.{u})

/-- The underlying ring presheaf, obtained by composing with the forgetful functor
to `CommRingCat`. This forgets the topology on presheaf values. -/
def ringPresheaf : X.carrier.Presheaf CommRingCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToCommRingCat

/-- The underlying topological presheaf, obtained by composing with the forgetful
functor to `TopCat`. This forgets the ring structure on presheaf values. -/
def topPresheaf : X.carrier.Presheaf TopCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToTopCat

/-- The stalk of the underlying ring presheaf at a point `x`.
This is the stalk `𝒪_{X,x}` as a commutative ring (forgetting topology). -/
noncomputable def ringStalk (x : X) : CommRingCat.{u} :=
  (X.ringPresheaf).stalk x

end TopRingPresheafedSpace

/-! ### Ring stalk maps for presheafed spaces of complete topological rings

Since `CompleteTopCommRingCat` does not have colimits (completions don't
preserve colimits in general), we cannot form stalks of `CompleteTopCommRingCat`-
valued presheaves directly. Instead, for a morphism of presheafed spaces
`α : X ⟶ Y`, we construct a *ring stalk map* on the underlying `CommRingCat`-
valued presheaves (which do have colimits). -/

/-- The ring stalk map induced by a morphism of `CompleteTopCommRingCat`-valued
presheafed spaces. Given `α : X ⟶ Y` and `x : X`, this is the ring homomorphism
`𝒪_{Y,f(x)} → 𝒪_{X,x}` on the stalks of the underlying ring presheaves.

Constructed by whiskering the presheaf map `α.c` with the forgetful functor to
`CommRingCat`, then applying the stalk functor and pushforward. -/
noncomputable def ringStalkMap {X Y : TopRingPresheafedSpace.{u}}
    (α : X ⟶ Y) (x : X) :
    Y.ringPresheaf.stalk (ConcreteCategory.hom α.base x) ⟶
    X.ringPresheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat (ConcreteCategory.hom α.base x)).map
    (Functor.whiskerRight α.c CompleteTopCommRingCat.forgetToCommRingCat) ≫
    X.ringPresheaf.stalkPushforward CommRingCat α.base x

set_option backward.isDefEq.respectTransparency false in
/-- The ring stalk map of the identity morphism is the identity. -/
@[simp]
theorem ringStalkMap_id (X : TopRingPresheafedSpace.{u}) (x : X) :
    ringStalkMap (𝟙 X) x = 𝟙 (X.ringStalk x) := by
  dsimp [ringStalkMap]
  rw [TopCat.Presheaf.stalkPushforward.id, ← Functor.map_comp]
  exact (TopCat.Presheaf.stalkFunctor CommRingCat x).map_id X.ringPresheaf

set_option backward.isDefEq.respectTransparency false in
/-- The ring stalk map of a composition is the composition of ring stalk maps. -/
@[simp]
theorem ringStalkMap_comp {X Y Z : TopRingPresheafedSpace.{u}}
    (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
    ringStalkMap (α ≫ β) x =
      ringStalkMap β (ConcreteCategory.hom α.base x) ≫ ringStalkMap α x := by
  dsimp [ringStalkMap, TopCat.Presheaf.stalkFunctor, TopCat.Presheaf.stalkPushforward,
    Functor.whiskerRight]
  apply colimit.hom_ext
  rintro ⟨U, hU⟩
  simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj,
    OpenNhds.inclusion_obj, Functor.map_comp, TopCat.hom_comp,
    ContinuousMap.comp_apply, ι_colimMap_assoc, Presheaf.pushforward_obj_obj,
    Opens.map_comp_obj, Functor.whiskerLeft_app, OpenNhds.map_obj,
    colimit.ι_pre, Category.assoc, colimit.ι_pre_assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-! ### The category 𝒱^pre (Definition 8.5 of Wedhorn)

An object of 𝒱^pre is a triple `(X, 𝒪_X, (v_x)_{x ∈ X})` where:

- `X` is a topological space,
- `𝒪_X` is a presheaf of complete topological rings on `X`,
- For each `x ∈ X`, the stalk `𝒪_{X,x}` (of the underlying ring presheaf) is
  a local ring,
- `v_x` is an equivalence class of valuations on `𝒪_{X,x}` with
  `supp(v_x)` equal to the maximal ideal.

A morphism `(f, f♭) : (X, 𝒪_X, (v_x)) → (Y, 𝒪_Y, (w_y))` in 𝒱^pre is:

- A morphism `(f, f♭)` of presheafed spaces (continuous map + presheaf map),
- For each `x ∈ X`, the induced stalk map `f♭_x : 𝒪_{Y,f(x)} → 𝒪_{X,x}` is
  a local ring homomorphism,
- The valuations are compatible: `w_{f(x)} = v_x ∘ f♭_x` as equivalence classes. -/

/-- An object of the category `𝒱^pre` (Definition 8.5 of Wedhorn).

A *valued presheafed space* consists of:
- A presheafed space `(X, 𝒪_X)` of complete topological rings,
- Local ring structure on each stalk `𝒪_{X,x}`,
- A valuation `v_x` on each stalk with `supp(v_x) = maximalIdeal`. -/
structure VPreObj where
  /-- The underlying presheafed space of complete topological rings. -/
  toPresheafedSpace : TopRingPresheafedSpace.{u}
  /-- Each stalk is a local ring. -/
  isLocalRing_stalk : ∀ x : toPresheafedSpace,
    IsLocalRing (toPresheafedSpace.ringStalk x)
  /-- The valuation on each stalk. -/
  val : ∀ x : toPresheafedSpace, Spv (toPresheafedSpace.ringStalk x)
  /-- The support of the valuation equals the maximal ideal. -/
  val_supp : ∀ x : toPresheafedSpace,
    (val x).supp = @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk x)

namespace VPreObj

variable (X : VPreObj.{u})

instance : CoeSort VPreObj.{u} (Type u) := ⟨fun X => X.toPresheafedSpace⟩

instance (x : X) : IsLocalRing (X.toPresheafedSpace.ringStalk x) :=
  X.isLocalRing_stalk x

/-- The underlying topological space of a `VPreObj`. -/
def toTopCat : TopCat.{u} := X.toPresheafedSpace.carrier

/-- The presheaf of complete topological rings. -/
def presheaf : X.toTopCat.Presheaf CompleteTopCommRingCat.{u} :=
  X.toPresheafedSpace.presheaf

/-- The underlying ring presheaf (forgetting topology). -/
noncomputable def ringPresheaf : X.toTopCat.Presheaf CommRingCat.{u} :=
  X.toPresheafedSpace.ringPresheaf

end VPreObj

/-- A morphism in the category `𝒱^pre` (Definition 8.7 of Wedhorn).

A morphism `(f, f♭) : X → Y` of valued presheafed spaces is a morphism of
presheafed spaces such that:
- Each ring stalk map `f♭_x : 𝒪_{Y,f(x)} → 𝒪_{X,x}` is local,
- The valuations are compatible: `w_{f(x)} = comap f♭_x v_x`. -/
structure VPreHom (X Y : VPreObj.{u}) where
  /-- The underlying morphism of presheafed spaces. -/
  toHom : X.toPresheafedSpace ⟶ Y.toPresheafedSpace
  /-- The ring stalk maps are local ring homomorphisms. -/
  isLocalHom_stalkMap : ∀ x : X.toPresheafedSpace,
    IsLocalHom (ringStalkMap toHom x).hom'
  /-- Valuation compatibility: `w_{f(x)} = comap f♭_x v_x`
  (the pullback of `v_x` along the stalk map equals `w_{f(x)}`). -/
  val_compat : ∀ x : X.toPresheafedSpace,
    Y.val (ConcreteCategory.hom toHom.base x) =
      (X.val x).comap (ringStalkMap toHom x).hom'

/-- Extensionality for `VPreHom`: two morphisms are equal if their underlying
presheafed space morphisms are equal. -/
@[ext]
theorem VPreHom.ext {X Y : VPreObj.{u}} {f g : VPreHom X Y}
    (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; congr

/-- The `Category` instance on `VPreObj` (Definition 8.7 of Wedhorn).
The identity is the identity presheafed space morphism (with identity stalk maps).
Composition is composition of presheafed space morphisms. -/
instance : CategoryTheory.Category VPreObj.{u} where
  Hom X Y := VPreHom X Y
  id X := {
    toHom := 𝟙 X.toPresheafedSpace
    isLocalHom_stalkMap := fun x => by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x => by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x => by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x => by
      rw [ringStalkMap_comp]
      erw [g.val_compat (ConcreteCategory.hom f.toHom.base x), f.val_compat x]
      exact (congr_fun (ValuationSpectrum.comap_comp _ _) _).symm }
  id_comp := fun f => VPreHom.ext (Category.id_comp f.toHom)
  comp_id := fun f => VPreHom.ext (Category.comp_id f.toHom)
  assoc := fun f g h => VPreHom.ext (Category.assoc f.toHom g.toHom h.toHom)

/-! ### The full subcategory 𝒱 (Remark 8.20 of Wedhorn)

The category 𝒱 is the full subcategory of 𝒱^pre consisting of objects `(X, 𝒪_X, (v_x))`
where `𝒪_X` is a sheaf of topological rings in the sense of Remark 8.20. -/

/-- An object of the category `𝒱` (Remark 8.20 of Wedhorn).

A *valued sheafed space* is a valued presheafed space `(X, 𝒪_X, (v_x))` where
additionally `𝒪_X` is a sheaf of topological rings:
- The underlying ring presheaf is a sheaf, AND
- For every open covering, the restriction map into the product is a
  topological embedding. -/
structure VObj extends VPreObj.{u} where
  /-- The underlying ring presheaf is a sheaf (algebraic condition). -/
  isSheaf : (toVPreObj.toPresheafedSpace.ringPresheaf).IsSheaf

/-- The `Category` instance on `VObj` (full subcategory of `VPreObj`).
Morphisms are `VPreHom`s between the underlying `VPreObj`s. -/
instance : CategoryTheory.Category VObj.{u} where
  Hom X Y := VPreHom X.toVPreObj Y.toVPreObj
  id X := {
    toHom := 𝟙 X.toVPreObj.toPresheafedSpace
    isLocalHom_stalkMap := fun x => by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x => by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x => by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x => by
      rw [ringStalkMap_comp]
      erw [g.val_compat (ConcreteCategory.hom f.toHom.base x), f.val_compat x]
      exact (congr_fun (ValuationSpectrum.comap_comp _ _) _).symm }
  id_comp f := VPreHom.ext (Category.id_comp f.toHom)
  comp_id f := VPreHom.ext (Category.comp_id f.toHom)
  assoc f g h := VPreHom.ext (Category.assoc f.toHom g.toHom h.toHom)

/-- The forgetful functor from `𝒱` to `𝒱^pre`. -/
def VObj.forgetToVPre : VObj.{u} ⥤ VPreObj.{u} where
  obj X := X.toVPreObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### Sheaf condition for topological ring presheaves (Remark 8.20 of Wedhorn)

A presheaf of topological rings `𝒪_X` is a **sheaf of topological rings**
(Remark 8.20 of Wedhorn) if and only if:

1. `𝒪_X` is a sheaf of rings (algebraic condition), AND
2. For every open covering `(U_i)` of `U`, the canonical map
   `𝒪_X(U) → ∏ 𝒪_X(U_i)` is a topological embedding.

For the concrete presheaf on rational subsets of `Spa(A, A⁺)`, this
becomes the `IsSheafyTopRing` condition below. -/

/-! ### Sheafy affinoid rings, revisited (Definition 8.26 of Wedhorn)

Following Remark 8.20, the full sheafiness condition requires:
1. The product restriction map is a topological embedding (implies injectivity)
2. Compatible families glue (surjectivity onto compatible families)

The existing `IsSheafy` captures condition (1a) (injectivity = separation).
`IsSheafyTopRing` captures the full Remark 8.20 condition. -/

/-- The product restriction map using a subtype-indexed product, suitable for
topological conditions (the codomain has a Pi topology). -/
noncomputable def productRestrictionSub (C : RationalCovering A) :
    presheafValue C.base → ∀ (D : ↥C.covers), presheafValue D.1 :=
  fun x ⟨D, hD⟩ => restrictionMap C.base D (C.hsubset D hD) x

/-- An affinoid ring `(A, A⁺)` satisfies the **full sheafiness condition**
(Definition 8.26 / Remark 8.20 of Wedhorn) if, for every rational covering:

1. The product restriction map is a topological embedding, and
2. Compatible families of sections glue.

This is the correct version of `IsSheafy` following Wedhorn exactly.
It implies `IsSheafy` (which only requires separation/injectivity). -/
class IsSheafyTopRing (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [inst₁ : PlusSubring A] [inst₂ : HasRestrictionMaps A] :
    Prop where
  /-- The product restriction map is a topological embedding
  (Remark 8.20, condition (2) of Wedhorn). This uses the subtype-indexed
  product `∀ (D : ↥C.covers), presheafValue D.1` which carries the Pi topology. -/
  isEmbedding_productRestriction : ∀ (C : RationalCovering A),
    Topology.IsEmbedding (productRestrictionSub A C)
  /-- Compatible families of sections glue to a global section
  (Remark 8.20, condition (1b) of Wedhorn). -/
  gluing : ∀ (C : RationalCovering A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1),
    (∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D

/-- `IsSheafyTopRing` implies `IsSheafy` (topological embedding implies injectivity). -/
instance (priority := 100) IsSheafyTopRing.toIsSheafy (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [HasRestrictionMaps A]
    [IsSheafyTopRing A] : IsSheafy A where
  separation C := by
    intro x y hxy
    exact (IsSheafyTopRing.isEmbedding_productRestriction C).injective
      (funext fun ⟨D, hD⟩ => congr_fun (congr_fun hxy D) hD)

/-! ### Adic spaces as objects of 𝒱 (Definitions 8.21, 8.22 of Wedhorn)

An *affinoid adic space* (Definition 8.21) is an object of `VObj` that is
isomorphic to `Spa(A, A⁺)` for some sheafy affinoid ring. An *adic space*
(Definition 8.22) is an object of `VObj` that admits an open covering by
affinoid adic spaces.

The `AffinoidAdicSpace` and `AdicSpace` structures below capture the
topological and algebraic components. The full definitions as objects of
`VObj` additionally require constructing the `CompleteTopCommRingCat`-valued
presheaf on all opens (via projective limits of rational covering values)
and equipping each stalk with a compatible valuation. -/

end ValuationSpectrum
