/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».Prop752
import «Adic spaces».CompleteTopCommRingCat
import «Adic spaces».Lemma745
import «Adic spaces».TopologyComparison
import «Adic spaces».LaurentRefinement
import Mathlib.RingTheory.RingHom.Flat
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

We define the structure sheaf `𝒪_X` on `X = Spa(A, A⁺)` following §8.1 of Wedhorn.

## Main definitions

* `SpaTop A` : The adic spectrum as an object of `TopCat`.
* `structureSheaf A` : The structure sheaf valued in `CompleteTopCommRingCat`.
* `VPreObj` / `VObj` : Categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7, Remark 8.20).
* `IsSheafy` : Sheaf condition for topological ring presheaves (Definition 8.26).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, Definition 8.5,
  Remark 8.20, Definition 8.21, Definition 8.22, Definition 8.26,
  Theorem 8.28(c)
-/

universe u

noncomputable section

open TopCat TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Topology

namespace ValuationSpectrum

variable (A : Type u) [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### The adic spectrum as a topological space -/

/-- The adic spectrum `Spa(A, A⁺)` as an object of `TopCat`. -/
def SpaTop : TopCat := TopCat.of ↥(Spa A A⁺)

/-- The continuous support map `Spa(A, A⁺) → Spec A` (Remark 4.6 of Wedhorn). -/
def suppSpa : C(SpaTop A, PrimeSpectrum A) where
  toFun x := suppFun x.val
  continuous_toFun := suppFun_continuous.comp continuous_subtype_val

/-! ### The structure sheaf -/

namespace StructureSheaf

variable {A}

/-- The stalk type family `x ↦ A_{supp(x)}` (Definition 8.5 of Wedhorn). -/
abbrev Localizations (x : SpaTop A) : Type u :=
  Localization.AtPrime x.val.supp

/-- A section is a *fraction* if `f(x) = r/s` for fixed `r, s`. -/
def IsFraction {U : Opens (SpaTop A)} (f : ∀ x : U, Localizations x.1) : Prop :=
  ∃ (r s : A), ∀ x : U, ∃ hs : s ∉ x.1.val.supp,
    f x = Localization.mk r ⟨s, hs⟩

/-- `IsFraction` is prelocal: it restricts to smaller open subsets. -/
def isFractionPrelocal : PrelocalPredicate (fun x : SpaTop A ↦ Localizations x) where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x ↦ w (i x)⟩

/-- A section is *locally a fraction* if it is a fraction near each point. -/
def isLocallyFraction : LocalPredicate (fun x : SpaTop A ↦ Localizations x) :=
  isFractionPrelocal.sheafify

/-- The sections satisfying `isLocallyFraction` form a subring. -/
def sectionsSubring (U : Opens (SpaTop A)) :
    Subring (∀ x : U, Localizations x.1) where
  carrier := { f | isLocallyFraction.pred f }
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun y ↦ ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· * ·) ha' hb').trans (Localization.mk_mul ..)⟩
  one_mem' x :=
    ⟨U, x.2, 𝟙 _, 1, 1, fun y ↦
      ⟨y.1.val.supp.primeCompl.one_mem, Localization.mk_one.symm⟩⟩
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sa * rb + sb * ra, sa * sb,
      fun y ↦ ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· + ·) ha' hb').trans (Localization.add_mk ..)⟩
  zero_mem' x :=
    ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦
      ⟨y.1.val.supp.primeCompl.one_mem, (Localization.mk_zero _).symm⟩⟩
  neg_mem' {a} ha x := by
    obtain ⟨V, m, i, r, s, w⟩ := ha x
    exact ⟨V, m, i, -r, s, fun y ↦ by
      obtain ⟨hs, h⟩ := w y
      exact ⟨hs, (congr_arg Neg.neg h).trans (Localization.neg_mk ..)⟩⟩

end StructureSheaf

open StructureSheaf

/-! ### Locally-fraction sections as a presheaf valued in CompleteTopCommRingCat

For each open `U ⊆ Spa(A, A⁺)`, the sections `sectionsSubring U` (locally-fraction
functions into stalk localizations) form a commutative ring. We equip this ring
with the discrete uniformity as a placeholder; the correct topology for non-rational
opens is the limit topology over rational covers (§8.1 of Wedhorn). -/

/-- The discrete uniform space on locally-fraction sections. -/
noncomputable instance sectionsUniformSpace (U : Opens (SpaTop A)) :
    UniformSpace ↥(sectionsSubring U) := ⊥

/-- The discrete uniformity on locally-fraction sections. -/
instance sectionsDiscreteUniformity (U : Opens (SpaTop A)) :
    DiscreteUniformity ↥(sectionsSubring U) := DiscreteUniformity.mk rfl

/-- The `IsTopologicalRing` instance on locally-fraction sections (discrete). -/
noncomputable instance sectionsIsTopologicalRing (U : Opens (SpaTop A)) :
    @IsTopologicalRing ↥(sectionsSubring U)
      (sectionsUniformSpace A U).toTopologicalSpace _ := by
  haveI : DiscreteTopology ↥(sectionsSubring U) :=
    DiscreteUniformity.instDiscreteTopology ↥(sectionsSubring U)
  exact { toContinuousMul := ⟨continuous_of_discreteTopology⟩
          toContinuousAdd := ⟨continuous_of_discreteTopology⟩
          toContinuousNeg := ⟨continuous_of_discreteTopology⟩ }

/-- The `IsUniformAddGroup` instance on locally-fraction sections (discrete). -/
noncomputable instance sectionsIsUniformAddGroup (U : Opens (SpaTop A)) :
    @IsUniformAddGroup ↥(sectionsSubring U) (sectionsUniformSpace A U) _ :=
  ⟨DiscreteUniformity.uniformContinuous _ _⟩

/-- The presheaf value on an open `U` as a `CompleteTopCommRingCat` object.

For each open `U`, the presheaf value is the subring of locally-fraction sections
in `∏ₓ Localization.AtPrime x.supp` (Definition 8.5 of Wedhorn), equipped with
the discrete uniformity. For rational subsets `U = R(T/s)`, this is canonically
isomorphic to the completion `A⟨T/s⟩` (Proposition 8.2). -/
noncomputable def presheafSectionsObj (U : Opens (SpaTop A)) :
    CompleteTopCommRingCat.{u} :=
  CompleteTopCommRingCat.of ↥(sectionsSubring U)

/-- The restriction ring homomorphism on locally-fraction sections. -/
noncomputable def presheafSectionsRes {U V : Opens (SpaTop A)} (h : V ≤ U) :
    ↥(sectionsSubring U) →+* ↥(sectionsSubring V) where
  toFun f := ⟨fun x ↦ f.1 ⟨x.1, h x.2⟩,
    isLocallyFraction.toPrelocalPredicate.res (homOfLE h) f.1 f.2⟩
  map_one' := Subtype.ext (funext fun _ ↦ rfl)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ rfl)
  map_zero' := Subtype.ext (funext fun _ ↦ rfl)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ rfl)

/-- The restriction morphism in `CompleteTopCommRingCat`. -/
noncomputable def presheafSectionsMor {U V : Opens (SpaTop A)} (h : V ≤ U) :
    presheafSectionsObj A U ⟶ presheafSectionsObj A V := by
  refine ⟨presheafSectionsRes A h, ?_⟩
  haveI : DiscreteTopology (presheafSectionsObj A U).α := by
    change DiscreteTopology ↥(sectionsSubring U)
    exact DiscreteUniformity.instDiscreteTopology ↥(sectionsSubring U)
  exact continuous_of_discreteTopology

/-- The structure presheaf of `Spa(A, A⁺)`, valued in `CompleteTopCommRingCat`.

For each open `U`, the presheaf value is the subring of locally-fraction sections
in `∏ₓ Localization.AtPrime x.supp` (Definition 8.5 of Wedhorn), equipped with
the discrete uniformity. For rational subsets `U = R(T/s)`, this is canonically
isomorphic to the completion `A⟨T/s⟩` (Proposition 8.2).

The correct topology for general opens is the limit topology over rational
covers; this requires substantial additional infrastructure (§8.1). -/
noncomputable def structurePresheaf [IsHuberRing A] [PlusSubring A] :
    Presheaf CompleteTopCommRingCat (SpaTop A) where
  obj U := presheafSectionsObj A U.unop
  map {U V} i := presheafSectionsMor A (leOfHom i.unop)
  map_id U := by
    simp only [presheafSectionsMor, presheafSectionsRes]
    apply Subtype.ext; ext ⟨f, hf⟩
    exact Subtype.ext (funext fun ⟨x, hx⟩ ↦ rfl)
  map_comp {U V W} i j := by
    simp only [presheafSectionsMor, presheafSectionsRes]
    apply Subtype.ext; ext ⟨f, hf⟩
    exact Subtype.ext (funext fun ⟨x, hx⟩ ↦ rfl)

/-- The structure sheaf of `Spa(A, A⁺)`, valued in `CompleteTopCommRingCat`
(Remark 8.20 of Wedhorn).

**Route to fill:** The type-level sheaf condition is already available
via `subpresheafToTypes.isSheaf isLocallyFraction` (from Mathlib's
`Topology.Sheaves.LocalPredicate`), since `isLocallyFraction` is a
`LocalPredicate` on `Localizations`. The transfer to `CompleteTopCommRingCat`
requires:
1. A forgetful functor `CompleteTopCommRingCat ⥤ Type` that preserves
   limits and reflects isomorphisms.
2. A natural isomorphism `structurePresheaf ⋙ forget ≅ subpresheafToTypes`.
3. Application of `isSheaf_iff_isSheaf_comp` to transfer the sheaf condition.

Alternatively, verify the sheaf condition directly by showing that
`structurePresheaf` satisfies `IsSheafUniqueGluing` in `CompleteTopCommRingCat`.
Both routes need additional category-theoretic infrastructure for
`CompleteTopCommRingCat` (limits, concrete category properties). -/
noncomputable def structureSheaf [IsHuberRing A] [PlusSubring A] :
    Sheaf CompleteTopCommRingCat (SpaTop A) :=
  ⟨structurePresheaf A, sorry⟩

/-! ### Sheafy affinoid rings (Definition 8.26 of Wedhorn) -/

variable [IsHuberRing A]

/-- The product restriction map for a rational covering. -/
noncomputable def productRestriction (C : RationalCovering A) :
    presheafValue C.base → ∀ D ∈ C.covers, presheafValue D :=
  fun x D hD ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- The product restriction map using a subtype-indexed product. -/
noncomputable def productRestrictionSub (C : RationalCovering A) :
    presheafValue C.base → ∀ (D : ↥C.covers), presheafValue D.1 :=
  fun x ⟨D, hD⟩ ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- An affinoid ring `(A, A⁺)` is **sheafy** if the structure presheaf `𝒪_X` on
`Spa(A, A⁺)` is a sheaf of topological rings (Definition 8.26 of Wedhorn).
By Remark 8.20, this is equivalent to two conditions:
1. The product restriction is a topological embedding (condition (2)).
2. Compatible families glue to global sections (condition (1b)). -/
class IsSheafy (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [inst₁ : PlusSubring A] [inst₂ : IsHuberRing A] :
    Prop where
  isEmbedding_productRestriction : ∀ (C : RationalCovering A),
    Topology.IsEmbedding (productRestrictionSub A C)
  gluing : ∀ (C : RationalCovering A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1),
    (∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D

/-- Sheafy implies separation (injectivity of product restriction). -/
theorem IsSheafy.separation [IsTopologicalRing A] [PlusSubring A]
    [IsHuberRing A] [IsSheafy A] (C : RationalCovering A) :
    Function.Injective (productRestriction A C) := by
  intro x y hxy
  exact (IsSheafy.isEmbedding_productRestriction C).injective
    (funext fun ⟨D, hD⟩ ↦ congr_fun (congr_fun hxy D) hD)

/-! ### Affinoid adic spaces (Definition 8.21 of Wedhorn) -/

/-- An *affinoid adic space* is `Spa(A, A⁺)` where `(A, A⁺)` is a sheafy
complete affinoid ring (Definition 8.21 of Wedhorn). Restriction maps are
constructed from the ring data (Proposition 8.2), not assumed separately. -/
structure AffinoidAdicSpace where
  /-- The underlying affinoid ring. -/
  Ring : Type u
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instPlusSubring : PlusSubring Ring]
  [instIsHuberRing : IsHuberRing Ring]
  [instIsSheafy : IsSheafy Ring]

attribute [instance] AffinoidAdicSpace.instCommRing
  AffinoidAdicSpace.instTopologicalSpace AffinoidAdicSpace.instIsTopologicalRing
  AffinoidAdicSpace.instPlusSubring AffinoidAdicSpace.instIsHuberRing
  AffinoidAdicSpace.instIsSheafy

namespace AffinoidAdicSpace

variable (X : AffinoidAdicSpace.{u})

/-- The underlying topological space of an affinoid adic space. -/
def toTopCat : TopCat.{u} := SpaTop X.Ring

/-- The structure sheaf of an affinoid adic space, valued in `CompleteTopCommRingCat`
(Definition 8.21 / Remark 8.20 of Wedhorn). -/
noncomputable def sheaf : Sheaf CompleteTopCommRingCat.{u} X.toTopCat :=
  structureSheaf X.Ring

end AffinoidAdicSpace

/-! ### Adic spaces (Definition 8.22 of Wedhorn) -/

/-- An *adic space* (Definition 8.22 of Wedhorn). -/
structure AdicSpace where
  /-- The underlying topological space. -/
  carrier : Type u
  [instTopologicalSpace : TopologicalSpace carrier]
  /-- Every point has an open neighborhood homeomorphic to an affinoid adic space. -/
  isLocallyAffinoid : ∀ x : carrier, ∃ (U : Opens carrier) (_ : x ∈ U)
    (X : AffinoidAdicSpace.{u}), Nonempty (↥U ≃ₜ X.toTopCat)

attribute [instance] AdicSpace.instTopologicalSpace

/-! ### The categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7, Remark 8.20 of Wedhorn) -/

/-- A presheafed space of complete topological rings (Definition 8.5). -/
abbrev TopRingPresheafedSpace := PresheafedSpace CompleteTopCommRingCat.{u}

namespace TopRingPresheafedSpace

variable (X : TopRingPresheafedSpace.{u})

/-- The underlying ring presheaf (forgetting topology). -/
def ringPresheaf : X.carrier.Presheaf CommRingCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToCommRingCat

/-- The underlying topological presheaf (forgetting ring structure). -/
def topPresheaf : X.carrier.Presheaf TopCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToTopCat

/-- The ring stalk `𝒪_{X,x}` at a point `x`. -/
noncomputable def ringStalk (x : X) : CommRingCat.{u} :=
  (X.ringPresheaf).stalk x

end TopRingPresheafedSpace

/-! ### Ring stalk maps for presheafed spaces of complete topological rings -/

/-- The ring stalk map `𝒪_{Y,f(x)} → 𝒪_{X,x}` induced by `α : X ⟶ Y`. -/
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
/-- The ring stalk map is functorial under composition. -/
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

/-! ### The category 𝒱^pre (Definition 8.5 of Wedhorn) -/

/-- An object of `𝒱^pre` (Definition 8.5 of Wedhorn). -/
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

instance : CoeSort VPreObj.{u} (Type u) := ⟨fun X ↦ X.toPresheafedSpace⟩

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

/-- A morphism in `𝒱^pre` (Definition 8.7 of Wedhorn). -/
structure VPreHom (X Y : VPreObj.{u}) where
  /-- The underlying morphism of presheafed spaces. -/
  toHom : X.toPresheafedSpace ⟶ Y.toPresheafedSpace
  /-- The ring stalk maps are local ring homomorphisms. -/
  isLocalHom_stalkMap : ∀ x : X.toPresheafedSpace,
    IsLocalHom (ringStalkMap toHom x).hom'
  /-- Valuation compatibility: `w_{f(x)} = comap f♭_x v_x`. -/
  val_compat : ∀ x : X.toPresheafedSpace,
    Y.val (ConcreteCategory.hom toHom.base x) =
      (X.val x).comap (ringStalkMap toHom x).hom'

/-- Extensionality for `VPreHom`. -/
@[ext]
theorem VPreHom.ext {X Y : VPreObj.{u}} {f g : VPreHom X Y}
    (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; congr

/-- The `Category` instance on `VPreObj` (Definition 8.7 of Wedhorn). -/
instance : CategoryTheory.Category VPreObj.{u} where
  Hom X Y := VPreHom X Y
  id X := {
    toHom := 𝟙 X.toPresheafedSpace
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x ↦ by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x ↦ by
      rw [ringStalkMap_comp]
      erw [g.val_compat (ConcreteCategory.hom f.toHom.base x), f.val_compat x]
      exact (congr_fun (ValuationSpectrum.comap_comp _ _) _).symm }
  id_comp := fun f ↦ VPreHom.ext (Category.id_comp f.toHom)
  comp_id := fun f ↦ VPreHom.ext (Category.comp_id f.toHom)
  assoc := fun f g h ↦ VPreHom.ext (Category.assoc f.toHom g.toHom h.toHom)

/-! ### The full subcategory 𝒱 (Remark 8.20 of Wedhorn) -/

/-- An object of `𝒱`: a valued sheafed space (Remark 8.20 of Wedhorn). -/
structure VObj extends VPreObj.{u} where
  /-- The underlying ring presheaf is a sheaf (algebraic condition). -/
  isSheaf : (toVPreObj.toPresheafedSpace.ringPresheaf).IsSheaf

/-- The `Category` instance on `VObj` (full subcategory of `VPreObj`). -/
instance : CategoryTheory.Category VObj.{u} where
  Hom X Y := VPreHom X.toVPreObj Y.toVPreObj
  id X := {
    toHom := 𝟙 X.toVPreObj.toPresheafedSpace
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x ↦ by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x ↦ by
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

/-! ### Sheafiness of strongly noetherian Tate rings (Theorem 8.28 of Wedhorn)

Strongly noetherian Tate rings are sheafy via Tate acyclicity. The proof proceeds by:
1. Laurent cover exactness for 2-element covers (Lemma 8.33, sorry-free).
2. Rational coverings refine products of Laurent covers (Lemma 7.54).
3. Refinement preserves separation (Proposition A.3, sorry-free). -/

/-- The product restriction on the dense embedding agrees with the
algebraic restriction: for `z` in the localization,
`productRestriction C (coeRingHom z) D hD = restrictionMapAlg z`.

This is the key factorization: the product restriction on the
completion EXTENDS the algebraic product restriction on the dense
subring. -/
theorem productRestriction_coe_eq
    (C : RationalCovering A) (z : Localization.Away C.base.s)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (C.base.coeRingHom z) D hD =
      restrictionMapAlg C.base D (C.hsubset D hD) z := by
  change restrictionMap C.base D (C.hsubset D hD) (C.base.coeRingHom z) = _
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe (restrictionMapAlg C.base D (C.hsubset D hD))
    (restrictionMapAlg_continuous C.base D (C.hsubset D hD))]

/-- Each component of the product restriction is a ring homomorphism.
This is because `restrictionMap D D' h` is defined via
`extensionHom`, which produces a `RingHom`. -/
theorem productRestriction_map_sub
    (C : RationalCovering A) (x y : presheafValue C.base)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (x - y) D hD =
      productRestriction A C x D hD -
        productRestriction A C y D hD := by
  change restrictionMap C.base D _ (x - y) = _
  exact map_sub (restrictionMapHom C.base D (C.hsubset D hD)) x y

/-! #### Factorization of restrictionMapAlg through localization -/

/-- The algebraic restriction map factors through the completion
embedding: `restrictionMapAlg C.base D h = D.coeRingHom ∘ locLift`
when `C.base.s` is a unit in `Localization.Away D.s`.

Both sides are ring homs from `Localization.Away C.base.s` to
`presheafValue D` that agree on `algebraMap(a)`, so they are equal
by the universal property of localization. -/
theorem restrictionMapAlg_factors (C : RationalCovering A)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hs_unit : IsUnit (algebraMap A (Localization.Away D.s) C.base.s)) :
    D.coeRingHom.comp (IsLocalization.Away.lift (S := Localization.Away C.base.s)
      C.base.s hs_unit) = restrictionMapAlg C.base D (C.hsubset D hD) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers C.base.s)
  ext a
  simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, restrictionMapAlg,
    RationalLocData.canonicalMap, RationalLocData.coeRingHom]

/-! #### The Spa-point radical argument (Wedhorn Theorem 8.28)

Shows `C.base.s ∈ radical(ann(a))` given `D.s^k * a = 0` for each covering piece `D`,
using the covering condition on `Spa(A, A⁺)`. For discrete rings, proved via trivial
valuations; for general Tate rings, requires Lemma 7.45 of Wedhorn. -/

omit [IsHuberRing A] in
/-- For an open prime `p` with `s ∉ p`, the trivial valuation on `Frac(A/p)` pulled back
to `A` lies in `rationalOpen T s`. Continuity follows from `p` being open. -/
theorem exists_spa_point_in_rationalOpen_of_isOpen_prime
    (T : Finset A) (s : A)
    (p : Ideal A) [p.IsPrime]
    (hp_open : IsOpen (p : Set A))
    (hs_notin : s ∉ p) :
    ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  classical
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) (WithZero (Multiplicative ℤ))).comap φ
  let v := ofValuation w
  have hw_mem_iff : ∀ (a : A), w a = 0 ↔ a ∈ p := by
    intro a
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply,
      Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun ha ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]; rfl⟩
  have hv_supp_eq : v.supp = p := by
    rw [supp_ofValuation]; ext a; exact hw_mem_iff a
  have hw_s : w s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero
    intro heq
    apply hs_notin
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hw_one_or_zero : ∀ (a : A), w a = 0 ∨ w a = 1 := by
    intro a
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    rcases eq_or_ne ((algebraMap (A ⧸ p) (FractionRing (A ⧸ p)))
        ((Ideal.Quotient.mk p) a)) 0 with h | h
    · left; rw [h]; simp
    · right; exact Valuation.one_apply_of_ne_zero h
  have hv_spa : v ∈ Spa A A⁺ := by
    refine ⟨?_, ?_⟩
    · apply isContinuous_ofValuation_of; intro γ
      by_cases hγ : γ = 0
      · subst hγ; convert isOpen_empty
        ext a; simp [not_lt_zero']
      · by_cases h1 : (1 : WithZero (Multiplicative ℤ)) < γ
        · convert isOpen_univ; ext a
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, w, Valuation.comap_apply]
          exact lt_of_le_of_lt (Valuation.one_apply_le_one _) h1
        · push_neg at h1
          suffices {a : A | w a < γ} = (p : Set A) by rw [this]; exact hp_open
          ext a
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h
            rcases hw_one_or_zero a with ha0 | ha1
            · exact (hw_mem_iff a).mp ha0
            · exact absurd (ha1 ▸ h |>.trans_le h1) (lt_irrefl _)
          · intro ha
            rw [(hw_mem_iff a).mpr ha]; exact zero_lt_iff.mpr hγ
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_rat : v ∈ rationalOpen T s := by
    refine ⟨hv_spa, ?_, ?_⟩
    · intro t' _
      change w t' ≤ w s; rw [hw_s]
      simp only [w, Valuation.comap_apply]
      exact Valuation.one_apply_le_one _
    · change ¬ (w s ≤ w 0)
      simp only [hw_s, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]
  exact ⟨v, hv_rat, hv_supp_eq ▸ le_refl _⟩

/-- Spa points in rational subsets (Wedhorn Thm 8.28, completion route). Open primes use the
trivial valuation; non-open primes use Lemma 7.45 via the completion. -/
theorem exists_spa_point_in_rationalOpen (D : RationalLocData A)
    [IsAdicComplete D.P.I D.P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D.P.A₀)
    (p : Ideal A) [p.IsPrime] (hs_notin : D.s ∉ p) :
    ∃ v ∈ rationalOpen D.T D.s, p ≤ v.supp := by
  by_cases hp_open : IsOpen (p : Set A)
  · exact @exists_spa_point_in_rationalOpen_of_isOpen_prime A _ _ _ D.T D.s p _ hp_open hs_notin
  · sorry

/-- If `D.s^k * a = 0` for each covering piece `D`, then `C.base.s ∈ radical(ann(a))`
(Wedhorn Theorem 8.28). Uses the Spa-point construction at primes. -/
theorem base_s_in_annihilator_radical_of_covering
    (C : RationalCovering A) (a : A)
    (ha_ann : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∃ k : ℕ, D.s ^ k * a = 0)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    C.base.s ∈ (Ideal.span ({b : A | b * a = 0} : Set A)).radical := by
  classical
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro p ⟨hp_ann, hp_prime⟩
  haveI := hp_prime
  by_contra hs_notin
  obtain ⟨v, hv_rat, hv_supp_ge⟩ := hSpa_points p hp_prime hs_notin
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  have hDs_notin_supp : D.s ∉ v.supp := fun hDs ↦
    hv_D.2.2 ((v.mem_supp_iff D.s).mp hDs)
  have hDs_notin : D.s ∉ p :=
    fun hDs ↦ hDs_notin_supp (hv_supp_ge hDs)
  obtain ⟨k, hk⟩ := ha_ann D hD
  exact hDs_notin (Ideal.IsPrime.mem_of_pow_mem hp_prime k
    (hp_ann (Ideal.subset_span hk)))

/-! **Completion-level kernel reduction.**

If the algebraic product restriction is injective on `Localization.Away C.base.s`,
then the product restriction `presheafValue C.base → ∏ presheafValue D` is injective
on the completion. Requires the `AdicCompletion` bridge (Wedhorn Thm 8.28, Stacks 00MA). -/

/-- The combined restriction map from `presheafValue C.base` to the
product of `presheafValue D` over covering pieces is continuous
(each component is `restrictionMapHom`, which extends the algebraic
restriction map by continuity). -/
private theorem continuous_productRestriction (C : RationalCovering A) :
    Continuous (fun z : presheafValue C.base ↦
      fun (D : ↥C.covers) ↦ restrictionMap C.base D.1 (C.hsubset D.1 D.2) z) := by
  apply continuous_pi
  intro ⟨D, hD⟩
  exact restrictionMapHom_continuous C.base D (C.hsubset D hD)

/-- The combined restriction is a ring homomorphism, so its kernel is
an additive subgroup. -/
private theorem map_sub_productRestriction (C : RationalCovering A)
    (x y : presheafValue C.base) (D : RationalLocData A)
    (hD : D ∈ C.covers) :
    restrictionMap C.base D (C.hsubset D hD) (x - y) =
      restrictionMap C.base D (C.hsubset D hD) x -
        restrictionMap C.base D (C.hsubset D hD) y :=
  map_sub (restrictionMapHom C.base D (C.hsubset D hD)) x y

/-! ### Old direct proof route (QUARANTINED)

These theorems form the old direct proof of Theorem 8.28 via the Spa-point radical
argument. The route has fundamental issues (`localization_isT0` is false when
`locIdeal = T`, `completionKer_eq_bot_of_locKer_eq_bot` needs faithful flatness).
The correct proof routes through `TopologyComparison.lean`. -/

-- REMOVED (T6): completionKer_eq_bot_of_locKer_eq_bot, localization_isT0,
-- loc_algebraic_injectivity_of_tate — quarantined as false/depending on false.
-- Superseded by the Laurent refinement route (rationalCovering_hasSeparation).

/-! #### Separation via the TopologyComparison isomorphism

The new proof of `separation_ofStronglyNoetherianTate` routes through
`presheafValueTateQuotientEquiv : presheafValue D ≃+* A⟨X⟩/(1-sX)`.

**Proof outline:** The isomorphism `e : presheafValue C.base ≃+* Q₀`
(where `Q₀ = A⟨X⟩/(1-s₀X)`) and the isomorphisms `eD : presheafValue D ≃+* QD`
transfer the product restriction to a ring hom `Q₀ → ∏ QD` between
Tate algebra quotients. This ring hom is injective because it factors
through the localization product map, which is injective by the
covering condition (Spa-point radical argument). -/

/-- If `s ∈ radical(ann(a))` and `s` is a unit in `A⟨X⟩/(1-sX)`,
then `mk(algebraMap a) = 0` in the quotient. -/
private theorem algebraMap_zero_of_radical_ann
    [NonarchimedeanRing A] (s a : A)
    (hs_rad : s ∈ (Ideal.span ({b : A | b * a = 0} : Set A)).radical) :
    (Ideal.Quotient.mk (oneSubfXIdeal s)) (algebraMap A _ a) = 0 := by
  rw [Ideal.mem_radical_iff] at hs_rad
  obtain ⟨N, hN⟩ := hs_rad
  have hs_ann : s ^ N * a = 0 := by
    let ann_a : Ideal A :=
      { carrier := {b : A | b * a = 0}
        add_mem' := fun {x y} (hx : x * a = 0) (hy : y * a = 0) => by
          change (x + y) * a = 0; rw [add_mul, hx, hy, add_zero]
        zero_mem' := zero_mul a
        smul_mem' := fun r {x} (hx : x * a = 0) => by
          change r * x * a = 0; rw [mul_assoc, hx, mul_zero] }
    have hspan : Ideal.span ({b : A | b * a = 0} : Set A) = ann_a :=
      le_antisymm (Ideal.span_le.mpr (fun _ h => h)) (fun _ h => Ideal.subset_span h)
    rw [hspan] at hN
    exact hN
  have hs_unit := isUnit_algebraMap_f_in_quotient_gen s
  rw [RingHom.comp_apply] at hs_unit
  have hmul : (Ideal.Quotient.mk (oneSubfXIdeal s)) (algebraMap A _ (s ^ N * a)) = 0 := by
    rw [hs_ann, map_zero, map_zero]
  rw [map_mul, map_pow] at hmul
  exact (IsUnit.mul_right_eq_zero (IsUnit.pow N hs_unit)).mp hmul

/-- If `z = C.base.canonicalMap a` and the product restriction kills `z`,
then `e_base z = 0`.

The proof uses `rationalCovering_hasSeparation` from the Laurent refinement route:
the product restriction being zero on all covering pieces implies the element is zero
in `presheafValue C.base`, hence its image under `e_base` is zero. -/
theorem tateQuotientProductRestriction_injective_on_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (e_base : presheafValue C.base ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s))
    (_e_cover : ∀ D ∈ C.covers, presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (_compat_base : ∀ a : A, e_base (C.base.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_compat_cover : ∀ (D : RationalLocData A) (hD : D ∈ C.covers) (a : A),
      (_e_cover D hD) (D.canonicalMap a) =
        (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (a : A)
    (hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C (C.base.canonicalMap a) D hD = 0) :
    e_base (C.base.canonicalMap a) = 0 := by
  have hzero : C.base.canonicalMap a = 0 :=
    rationalCovering_hasSeparation P C (C.base.canonicalMap a) 0 (fun D hD => by
      show restrictionMap C.base D (C.hsubset D hD) (C.base.canonicalMap a) =
        restrictionMap C.base D (C.hsubset D hD) 0
      rw [show restrictionMap C.base D (C.hsubset D hD) 0 =
        (0 : presheafValue D) from map_zero (restrictionMapHom C.base D (C.hsubset D hD))]
      exact hker D hD)
  rw [hzero, map_zero]

/-- The product restriction, transferred to Tate algebra quotients via the isomorphism,
has trivial kernel (Theorem 8.28 of Wedhorn).

The proof uses `rationalCovering_hasSeparation` from the Laurent refinement route:
the product restriction being zero on all covering pieces implies the element is zero
in `presheafValue C.base`, hence its image under `e_base` is zero. -/
theorem tateQuotientProductRestriction_injective
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (_e_base : presheafValue C.base ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s))
    (_e_cover : ∀ D ∈ C.covers, presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (_compat_base : ∀ a : A, _e_base (C.base.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_compat_cover : ∀ (D : RationalLocData A) (hD : D ∈ C.covers) (a : A),
      (_e_cover D hD) (D.canonicalMap a) =
        (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (z : presheafValue C.base)
    (hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C z D hD = 0) :
    _e_base z = 0 := by
  have hzero : z = 0 :=
    rationalCovering_hasSeparation P C z 0 (fun D hD => by
      show restrictionMap C.base D (C.hsubset D hD) z =
        restrictionMap C.base D (C.hsubset D hD) 0
      rw [show restrictionMap C.base D (C.hsubset D hD) 0 =
        (0 : presheafValue D) from map_zero (restrictionMapHom C.base D (C.hsubset D hD))]
      exact hker D hD)
  rw [hzero, map_zero]

/-- The product restriction is injective for strongly noetherian Tate rings
(Theorem 8.28 of Wedhorn, separation component via TopologyComparison). -/
theorem separation_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    (hb_base : TopologicalRing.IsPowerBounded (invS C.base))
    (hcs_base : @CompleteSpace _ (quotientTUniformSpace C.base.s))
    (ht0_base : @T0Space _ (quotientTTopology C.base.s))
    (hcont_base : @Continuous _ _
      (quotientTTopology C.base.s)
      (inferInstance : TopologicalSpace (presheafValue C.base))
      (tateQuotientToPresheafHom C.base hb_base))
    (hdense_base : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s)
      (quotientTTopology C.base.s) (Localization.Away C.base.s)
      (locToQuotientOneSubfX_gen C.base.s))
    (hb_all : ∀ D : RationalLocData A, TopologicalRing.IsPowerBounded (invS D))
    (hcs_cover : ∀ D ∈ C.covers, @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0_cover : ∀ D ∈ C.covers, @T0Space _ (quotientTTopology D.s))
    (hcont_cover : ∀ D ∈ C.covers, @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D (hb_all D)))
    (hdense_cover : ∀ D ∈ C.covers, @DenseRange
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    Function.Injective (productRestriction A C) := by
  let e_base := presheafValueTateQuotientEquiv C.base hb_base hcs_base ht0_base
    hcont_base hdense_base
  intro x y hxy
  suffices h : x - y = 0 from sub_eq_zero.mp h
  have hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C (x - y) D hD = 0 := by
    intro D hD
    rw [productRestriction_map_sub, sub_eq_zero]
    exact congr_fun (congr_fun hxy D) hD
  set z := x - y
  set q := e_base z
  suffices hq : q = 0 by
    have : e_base z = 0 := hq
    exact e_base.injective (this.trans (map_zero e_base.toRingHom).symm)
  exact tateQuotientProductRestriction_injective (A := A) P C e_base
    (fun D hD => presheafValueTateQuotientEquiv D (hb_all D)
      (hcs_cover D hD) (ht0_cover D hD) (hcont_cover D hD) (hdense_cover D hD))
    (fun a => presheafValueTateQuotientEquiv_canonicalMap C.base
      hb_base hcs_base ht0_base hcont_base hdense_base a)
    (fun D hD a => presheafValueTateQuotientEquiv_canonicalMap D
      (hb_all D) (hcs_cover D hD) (ht0_cover D hD) (hcont_cover D hD)
      (hdense_cover D hD) a)
    hSpa z hker

/-! ### Flatness of presheafValue (Wedhorn Proposition 8.30, via TopologyComparison) -/

/-- `presheafValue D` is flat over `A` (Wedhorn Proposition 8.30), assuming
the TopologyComparison isomorphism hypotheses are satisfied. -/
theorem presheafValue_flat_of_tateQuotient
    [T2Space A] [NonarchimedeanRing A] [IsNoetherianRing A]
    [FirstCountableTopology A] [IsTateRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s)) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    TateAlgebra.flat_quotient_oneSubfX_general P D.s
  let e := presheafValueTateQuotientEquiv D hb hcs ht0 hcont hdense
  change @Module.Flat A (presheafValue D) _ _
    (RingHom.toModule (RationalLocData.canonicalMap D))
  letI : Module A (presheafValue D) := RingHom.toModule (RationalLocData.canonicalMap D)
  have he_smul : ∀ (a : A) (x : presheafValue D), e (a • x) = a • e x := by
    intro a x
    change e (RationalLocData.canonicalMap D a * x) = algebraMap A _ a * e x
    rw [e.map_mul]; congr 1
    exact presheafValueTateQuotientEquiv_canonicalMap D hb hcs ht0 hcont hdense a
  exact @Module.Flat.of_linearEquiv A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) (presheafValue D)
    inferInstance inferInstance inferInstance inferInstance this hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-! ### Proof via Laurent cover refinement (Wedhorn Lemma 8.34) -/

/-- The product restriction is injective for every rational covering, via Laurent
refinement (Lemma 8.34 of Wedhorn). -/
theorem productRestriction_injective_of_laurentRefinement
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    Function.Injective (productRestriction A C) := by
  intro x y hxy
  exact rationalCovering_hasSeparation P C x y
    (fun D hD => congr_fun (congr_fun hxy D) hD)

/-- The product restriction is topologically inducing for nonempty coverings.
Each restriction map to a covering piece is inducing (Prop 8.15, via
`restrictionMapHom_isInducing`); the product of inducing maps is inducing. -/
theorem productRestrictionSub_isInducing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (C : RationalCovering A) (D₀ : RationalLocData A) (hD₀ : D₀ ∈ C.covers) :
    Topology.IsInducing (productRestrictionSub A C) := by
  haveI : Nonempty (↥C.covers) := ⟨⟨D₀, hD₀⟩⟩
  -- The topology on presheafValue C.base = iInf of induced topologies from each
  -- restriction (because each restriction is inducing).
  -- The product map is inducing iff the source topology = induced from the product,
  -- which = iInf of induced topologies from projections (by induced_to_pi).
  constructor
  conv_rhs => rw [induced_to_pi]
  -- Goal: actual_topo = iInf (fun D => induced (component D) (topo D))
  -- Each induced (component D) (topo D) = actual_topo (restrictionMapHom is inducing)
  -- Show each induced topology equals the actual one, then use iInf_const
  suffices h : ∀ D : ↥C.covers,
      TopologicalSpace.induced (fun x => productRestrictionSub A C x D) inferInstance =
      instTopologicalSpacePresheafValue C.base by
    simp_rw [h, iInf_const]
  intro ⟨D, hD⟩
  exact (restrictionMapHom_isInducing C.base D (C.hsubset D hD)).eq_induced.symm

/-- Strongly noetherian Tate rings are sheafy (Theorem 8.28 of Wedhorn),
via Laurent cover refinement (Lemma 8.34). -/
theorem isSheafy_ofStronglyNoetherianTate_flat
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A where
  isEmbedding_productRestriction C := by
    constructor
    · -- Goal: IsInducing (productRestrictionSub A C)
      -- Strategy: Each restriction map to a covering piece is topologically
      -- inducing (Prop 8.15, via restrictionMapHom_isInducing). By
      -- IsInducing.of_comp, if g . f is inducing and both are continuous,
      -- then f is inducing. We take g = projection to any covering piece.
      by_cases hne : C.covers.Nonempty
      · -- Nonempty covering: use productRestrictionSub_isInducing
        obtain ⟨D₀, hD₀⟩ := hne
        exact productRestrictionSub_isInducing (A := A) C D₀ hD₀
      · -- Empty covering: presheafValue C.base is a subsingleton.
        -- When C.covers is empty, rationalCovering_hasSeparation gives
        -- x = y for all x y (the hypothesis is vacuously true).
        haveI : Subsingleton (presheafValue C.base) :=
          ⟨fun x y => rationalCovering_hasSeparation P C x y
            (fun D hD => absurd ⟨D, hD⟩ hne)⟩
        exact IsInducing.of_subsingleton _
    · intro x y hxy
      exact rationalCovering_hasSeparation P C x y (fun D hD => congr_fun hxy ⟨D, hD⟩)
  gluing C f hcompat :=
    rationalCovering_hasGluing P C f hcompat

-- REMOVED (T6): isSheafy_ofStronglyNoetherianTate (TopologyComparison route)
-- had 2 sorries, superseded by isSheafy_ofStronglyNoetherianTate_flat above.

/-! ### Factoring the product restriction through the canonical map -/

/-- The product restriction composed with the canonical map to the base
equals the product of canonical maps to the covering pieces. That is,
the following diagram commutes:
```
          canonicalMap C.base
      A ──────────────────────→ presheafValue C.base
      │                                  │
      │ ∏ D.canonicalMap                 │ productRestriction C
      ↓                                  ↓
  ∏ presheafValue D  ═════════  ∏ presheafValue D
```
-/
theorem productRestriction_comp_canonicalMap
    (C : RationalCovering A)
    (a : A) (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (C.base.canonicalMap a) D hD = D.canonicalMap a := by
  change restrictionMap C.base D (C.hsubset D hD) (C.base.canonicalMap a) = D.canonicalMap a
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe (restrictionMapAlg C.base D (C.hsubset D hD))
    (restrictionMapAlg_continuous C.base D (C.hsubset D hD))]
  simp only [restrictionMapAlg, IsLocalization.Away.lift_eq]

/-! ### Adic spaces as objects of 𝒱 (Definitions 8.21, 8.22 of Wedhorn) -/

end ValuationSpectrum
