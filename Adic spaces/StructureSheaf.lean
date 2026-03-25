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

We define the structure sheaf `𝒪_X` on `X = Spa(A, A⁺)` following §8.1 of Wedhorn.

## Main definitions

* `SpaTop A` : The adic spectrum as an object of `TopCat`.
* `structureSheaf A` : The structure sheaf valued in `CommRingCat`.
* `VPreObj` / `VObj` : Categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7, Remark 8.20).
* `IsSheafyTopRing` : Full sheaf condition for topological ring presheaves.

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

/-- The structure sheaf of `Spa(A, A⁺)`, valued in `Type`. -/
def structureSheafInType : Sheaf (Type u) (SpaTop A) :=
  subsheafToTypes isLocallyFraction

instance structureSheafInType.commRing (U : (Opens (SpaTop A))ᵒᵖ) :
    CommRing ((structureSheafInType A).obj.obj U) :=
  inferInstanceAs (CommRing (sectionsSubring U.unop))

/-- The structure presheaf of `Spa(A, A⁺)`, valued in `CommRingCat`. -/
def structurePresheaf : Presheaf CommRingCat (SpaTop A) where
  obj U := .of ((structureSheafInType A).obj.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType A).obj.map i
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-! ### Lifting to `CommRingCat` -/

/-- `structurePresheaf A ⋙ forget ≅ structureSheafInType A`. -/
def structurePresheafCompForget :
    structurePresheaf A ⋙ forget CommRingCat ≅ (structureSheafInType A).obj :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- The structure sheaf of `Spa(A, A⁺)`, valued in `CommRingCat`. -/
def structureSheaf : Sheaf CommRingCat (SpaTop A) :=
  ⟨structurePresheaf A,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) _).mpr
      (TopCat.Presheaf.isSheaf_of_iso (structurePresheafCompForget A).symm
        (structureSheafInType A).property)⟩

/-! ### Sheafy affinoid rings (Definition 8.26 of Wedhorn) -/

variable [IsTopologicalRing A] [HasRestrictionMaps A]

/-- The product restriction map for a rational covering. -/
noncomputable def productRestriction (C : RationalCovering A) :
    presheafValue C.base → ∀ D ∈ C.covers, presheafValue D :=
  fun x D hD ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- An affinoid ring is *sheafy* if the product restriction map is
injective for every rational covering (Definition 8.26). -/
class IsSheafy [IsTopologicalRing A] [HasRestrictionMaps A] : Prop where
  /-- For every rational covering, the product restriction map is injective
  (separation / uniqueness of gluing). -/
  separation : ∀ (C : RationalCovering A),
    Function.Injective (productRestriction A C)

/-- **Theorem 8.28(c)** of Wedhorn: discrete rings are sheafy. -/
instance IsSheafy.discrete [DiscreteTopology A] [IsTopologicalRing A] :
    IsSheafy A :=
  ⟨fun C ↦ by
    intro x y hxy; exact productRestriction_injective_discrete C
      (funext fun ⟨D, hD⟩ ↦ congr_fun (congr_fun hxy D) hD)⟩

/-! ### Affinoid adic spaces (Definition 8.21 of Wedhorn) -/

/-- An *affinoid adic space* (Definition 8.21 of Wedhorn). -/
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

/-! ### Sheafy affinoid rings, revisited (Definition 8.26 / Remark 8.20 of Wedhorn) -/

/-- The product restriction map using a subtype-indexed product. -/
noncomputable def productRestrictionSub (C : RationalCovering A) :
    presheafValue C.base → ∀ (D : ↥C.covers), presheafValue D.1 :=
  fun x ⟨D, hD⟩ ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- The full sheafiness condition (Definition 8.26 of Wedhorn). -/
class IsSheafyTopRing (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [inst₁ : PlusSubring A] [inst₂ : HasRestrictionMaps A] :
    Prop where
  /-- The product restriction map is a topological embedding
  (Remark 8.20, condition (2) of Wedhorn). -/
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
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D

/-- `IsSheafyTopRing` implies `IsSheafy`. -/
instance (priority := 100) IsSheafyTopRing.toIsSheafy (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [HasRestrictionMaps A]
    [IsSheafyTopRing A] : IsSheafy A where
  separation C := by
    intro x y hxy
    exact (IsSheafyTopRing.isEmbedding_productRestriction C).injective
      (funext fun ⟨D, hD⟩ ↦ congr_fun (congr_fun hxy D) hD)

/-! ### Sheafiness of strongly noetherian Tate rings (Theorem 8.28 of Wedhorn)

Wedhorn's Theorem 8.28 states that strongly noetherian Tate rings are sheafy.
The proof goes through **Tate acyclicity**: every rational covering of
`Spa(A, A⁺)` yields an exact Čech complex.

The **separation** (= injectivity of the product restriction) requires showing
that the canonical map

  `presheafValue C.base → ∏_{D ∈ C.covers} presheafValue D`

is injective. Since `presheafValue D` is the *completion* of
`Localization.Away D.s` with respect to the localization topology,
this is strictly stronger than injectivity at the algebraic (localization)
level.

**Proof outline (Wedhorn pp. 82-85):**
1. Laurent cover exactness gives separation for 2-element covers
   (Lemma 8.33).
2. Every standard rational covering refines a product of Laurent covers
   (Lemma 7.54).
3. Refinement preserves separation (Proposition A.3).

**Current status:**
- Steps 1 and 3 are proved in `TateAcyclicity.lean` (sorry-free).
- Step 2 requires the decomposition of rational subsets into basic pieces
  and the categorical connection between `RationalCovering` and the
  `FiniteCover`/`AbPresheaf` framework. These are documented as
  Components B and C in `TateAcyclicity.lean`.
- The algebraic injectivity argument from the discrete case
  (`Presheaf.lean`, `productRestriction_injective_discrete`) relies on
  constructing Spa points at every prime ideal (via
  `exists_mem_spa_supp_eq_of_prime`), which uses `DiscreteTopology` to
  ensure all valuations are continuous. For general Tate rings, this
  requires Lemma 7.45 of Wedhorn (analytic point construction at
  arbitrary primes), which gives `supp ⊇ 𝔭` (not `= 𝔭`).

**Factorization of the product restriction:**
The product restriction `productRestriction A C` on the completion
factors through the algebraic product restriction on the dense subring
`Localization.Away C.base.s` (see `productRestriction_coe_eq` below).
The algebraic product restriction into the product of `presheafValue D`
is the composition of the localization-level maps (injective by the
Spa-point argument from the discrete case) with the completion
embeddings (injective by T0Space). The full proof requires showing
that this factorization lifts from the dense subring to the completion.
-/

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
  change restrictionMap C.base D (C.hsubset D hD)
    (C.base.coeRingHom z) = _
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg C.base D (C.hsubset D hD))
    (HasRestrictionMaps.restrictionMapAlg_continuous
      C.base D (C.hsubset D hD))]

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

/-- The product restriction on the dense embedding is injective: if
an element of `Localization.Away C.base.s` maps to zero in every
covering piece (via the algebraic restriction), then it was zero.

This follows from the factorization
`restrictionMapAlg = D.coeRingHom ∘ algebraicLift` where
`algebraicLift : Localization.Away C.base.s → Localization.Away D.s`
is the localization-level map. Since `D.coeRingHom` is injective
(T0Space on the completion), `algebraicLift(z) = 0` for all D.
Then the algebraic product restriction on the localization is
injective (by the Spa-point radical argument from
`productRestriction_injective_discrete`), so `z = 0`.

For discrete rings, this is immediate since `coeRingHom` is
bijective. For general rings, the factorization requires
`IsUnit (algebraMap A (Localization.Away D.s) C.base.s)`, which
is the algebraic content of `isUnit_canonicalMap_s` lifted through
the bijective `coeRingHom` of the discrete case. -/
theorem productRestriction_coe_injective
    (C : RationalCovering A) (z : Localization.Away C.base.s)
    (hz : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C (C.base.coeRingHom z) D hD = 0) :
    C.base.coeRingHom z = 0 := by
  have hz_alg : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) z = 0 := by
    intro D hD
    rw [← productRestriction_coe_eq (A := A) C z D hD]
    exact hz D hD
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  suffices h : z = 0 by rw [h, map_zero]
  -- Each `restrictionMapAlg C.base D h` sends `z` to `0` in
  -- `presheafValue D`. The `restrictionMapAlg` is defined as
  -- `IsLocalization.Away.lift D.s hu` where `hu` witnesses that
  -- `D.s` maps to a unit in `presheafValue D`. This map factors
  -- as `D.coeRingHom ∘ locLift` where `locLift` is the localization-
  -- level map, provided `D.s` maps to a unit in `Localization.Away D.s`
  -- (not just in `presheafValue D`). For discrete rings, this follows
  -- from `coeRingHom_bijective_of_discrete`. For general rings, this
  -- factorization requires the presheaf identification
  -- (`presheafValue D ≅ AdicCompletion I (Localization.Away D.s)`).
  sorry

/-- **Theorem 8.28 of Wedhorn** (separation component): for a strongly
noetherian Tate ring, every rational covering has injective product
restriction.

This is the key step toward `IsSheafy`. The proof reduces injectivity
of `productRestriction` to:
1. `productRestriction_coe_eq`: the product restriction extends the
   algebraic restriction from the dense subring.
2. `productRestriction_coe_injective`: the product restriction is
   injective on the dense subring.

The remaining gap (`productRestriction_coe_injective`) requires the
connection between the completion-valued product restriction and the
algebraic product restriction on the localization. The precise
obstacle is that `coeRingHom` is injective but not surjective for
non-discrete topologies, so we cannot lift elements from the
completion back to the localization.

Possible proof routes for the gap:
- *Faithful flatness (Corollary 8.32)*: show the product of
  presheaf values is faithfully flat over `A`, hence the canonical
  map is injective. Requires presheaf identification.
- *Laurent cover refinement*: show every rational cover refines a
  product of Laurent covers (Lemma 7.54), use refinement transfer
  (Proposition A.3), and Laurent cover separation (Lemma 8.33).
  Requires categorical wrapping.
- *Adic completion*: identify `presheafValue D` with
  `AdicCompletion I (Localization.Away D.s)` and use
  `AdicCompletion.map_injective` from Mathlib.

The algebraic foundations (Laurent cover exactness, flatness,
refinement transfer) are proved in `TateAcyclicity.lean`.

The discrete case is fully proved by
`productRestriction_injective_discrete` in `Presheaf.lean` and
`IsSheafy.discrete` in this file. -/
theorem separation_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    Function.Injective (productRestriction A C) := by
  intro x y hxy
  rw [← sub_eq_zero]
  set z := x - y with hz_def
  suffices hz : z = 0 by exact hz
  have hz_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C z D hD = 0 := by
    intro D hD
    rw [hz_def, productRestriction_map_sub, sub_eq_zero]
    exact congr_fun (congr_fun hxy D) hD
  -- Each component of productRestriction is a continuous ring hom
  -- built via `extensionHom` of the algebraic restriction. On the
  -- dense subring `coeRingHom(Localization.Away C.base.s)`, the
  -- product restriction reduces to the algebraic product restriction
  -- (`productRestriction_coe_eq`). Injectivity on the dense subring
  -- is `productRestriction_coe_injective` (which itself requires the
  -- presheaf identification). Lifting from the dense subring to the
  -- full completion requires one of:
  -- (a) the product restriction being a topological embedding
  --     (`IsSheafyTopRing`), or
  -- (b) identifying `presheafValue` with `AdicCompletion` and using
  --     `AdicCompletion.map_injective`, or
  -- (c) the Laurent cover refinement + Cech cohomology route.
  sorry

/-- **Theorem 8.28 of Wedhorn**: strongly noetherian Tate rings
are sheafy.

Uses `separation_ofStronglyNoetherianTate` for the separation axiom.
See that theorem's docstring for the proof roadmap and remaining
gaps. -/
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A where
  separation C := separation_ofStronglyNoetherianTate A P C

/-! ### Factoring the product restriction through the canonical map

The product of canonical maps `A → ∏ presheafValue D` factors through
the canonical map to the base `A → presheafValue C.base` followed by
the product restriction. This is a key structural property used in the
faithful flatness route to sheafiness. -/

/-- The product restriction composed with the canonical map to the base
equals the product of canonical maps to the covering pieces. That is,
the following diagram commutes:
```
            canonicalMap C.base
        A ─────────────────────────→ presheafValue C.base
        │                                    │
        │ ∏ D.canonicalMap                   │ productRestriction C
        ↓                                    ↓
  ∏ presheafValue D  ═══════════  ∏ presheafValue D
```
-/
theorem productRestriction_comp_canonicalMap
    (C : RationalCovering A)
    (a : A) (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (C.base.canonicalMap a) D hD =
      D.canonicalMap a := by
  -- productRestriction C (canonicalMap a) D hD
  -- = restrictionMap C.base D h (canonicalMap a)
  -- = restrictionMapHom(coeRingHom(algebraMap a))
  -- = extensionHom(restrictionMapAlg)(coeRingHom(algebraMap a))
  -- = restrictionMapAlg(algebraMap a)              [by extensionHom_coe]
  -- = IsLocalization.Away.lift(algebraMap a)        [by defn of restrictionMapAlg]
  -- = D.canonicalMap a                              [by lift_eq]
  change restrictionMap C.base D (C.hsubset D hD) (C.base.canonicalMap a) =
    D.canonicalMap a
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg C.base D (C.hsubset D hD))
    (HasRestrictionMaps.restrictionMapAlg_continuous
      C.base D (C.hsubset D hD))]
  simp only [restrictionMapAlg, IsLocalization.Away.lift_eq]

/-! ### Adic spaces as objects of 𝒱 (Definitions 8.21, 8.22 of Wedhorn) -/

end ValuationSpectrum
