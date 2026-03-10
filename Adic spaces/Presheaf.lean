/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RationalSubsets
import «Adic spaces».LocalizationTopology
import «Adic spaces».CompleteTopCommRingCat
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# The Presheaf on the Adic Spectrum

We define the presheaf `𝒪_X` on the adic spectrum `X = Spa(A, A⁺)`,
following Section 8.1 of [Wedhorn, *Adic Spaces*].

The presheaf is defined on rational subsets by equation (8.1.1) of Wedhorn:

  `𝒪_X(R(T/s)) := A⟨T/s⟩`

where `A⟨T/s⟩` is the completion of the localization `Aₛ` equipped with the
localization topology from `LocalizationTopology.lean`.

## Main definitions

* `rationalOpens T s` : Rational subsets as elements of `Opens ↥(Spa A A⁺)`.
* `adicCompletion A` : The completion `Â` as an object of `TopCommRingCat`.
* `presheafValue P T s` : The presheaf value `𝒪_X(R(T/s)) = A⟨T/s⟩`, the
  completion of `Localization.Away s` with the localization topology.

## Main results

* `rationalOpen_singleton_one` : `R({1}/1) = Spa(A, A⁺)` (Remark 8.3, first part).
* `rationalOpens_singleton_one` : `R({1}/1) = ⊤` as an element of `Opens`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Section 8.1, Remark 8.3
-/

open Spv

namespace Spv

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### Step 0: Rational subsets as `Opens` -/

/-- A rational subset `R(T/s)` viewed as an open subset of `↥(Spa A A⁺)`. -/
def rationalOpens [DecidableEq A] (T : Finset A) (s : A) :
    TopologicalSpace.Opens ↥(Spa A A⁺) :=
  ⟨Subtype.val ⁻¹' rationalOpen T s, rationalOpen_isOpen T s⟩

/-! ### Step 1: The trivial rational subset is the whole space -/

/-- `R({1}/1) = Spa(A, A⁺)`. This is the first part of Remark 8.3 of Wedhorn:
the whole adic spectrum is itself a rational subset. -/
theorem rationalOpen_singleton_one :
    rationalOpen ({1} : Finset A) (1 : A) = Spa A A⁺ := by
  ext v
  simp only [rationalOpen, Spa, Set.mem_setOf_eq, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, -, -⟩; exact hv
  · intro hv
    exact ⟨hv, fun t ht ↦ by subst ht; exact (v.vle_total 1 1).elim id id,
      v.not_vle_one_zero⟩

/-- The rational subset `R({1}/1)` corresponds to `⊤` in `Opens ↥(Spa A A⁺)`. -/
theorem rationalOpens_singleton_one [DecidableEq A] :
    rationalOpens ({1} : Finset A) (1 : A) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  simp only [rationalOpens, TopologicalSpace.Opens.coe_mk, TopologicalSpace.Opens.coe_top]
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, Set.mem_univ, iff_true]
  rw [rationalOpen_singleton_one]
  exact hv

/-! ### The adic completion -/

/-- The *adic completion* `Â` of a topological ring `A`, as an object of `TopCommRingCat`.
This is `UniformSpace.Completion A` equipped with its ring and topological ring structure. -/
noncomputable def adicCompletion (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] : TopCommRingCat :=
  TopCommRingCat.of (UniformSpace.Completion A)

/-! ### Remark 8.3 of Wedhorn

The presheaf `𝒪_X` on the adic spectrum `X = Spa(A, A⁺)` is defined on rational
subsets by `𝒪_X(R(T/s)) := A⟨T/s⟩`, the completion of the localization `A(T/s)`.

**Remark 8.3** states: since `X = R({1}/1)` (by `rationalOpen_singleton_one`),
the presheaf value on the whole space is `𝒪_X(X) = A⟨{1}/1⟩ = Â`.

This follows because the localization `A({1}/1)` is canonically isomorphic to `A`
as a topological ring (localizing at `1` does nothing), so its completion is `Â`.
-/

section Remark83

/-! ### Remark 8.3: `𝒪_X(X) = Â`

The proof has three ingredients:
1. `X = R({1}/1)` as sets (proved above as `rationalOpen_singleton_one`).
2. Localizing at `1` is trivial: `Localization.Away 1 ≃ₐ[A] A`.
3. The localization topology on `A({1}/1)` has the same neighborhood basis
   as the original topology on `A`, mapped through `algebraMap`
   (by `locSubring_singleton_one`, `locNhd_singleton_one_eq`, and
   `locTopology_hasBasis_singleton_one` from `LocalizationTopology.lean`).

Together: `𝒪_X(X) = A⟨{1}/1⟩ = Completion(A) = Â`.
-/

variable (A : Type*) [CommRing A]

/-- Localizing at `1` gives back the original ring: `Localization.Away 1 ≃ₐ[A] A`
(ingredient 2 of Remark 8.3). -/
noncomputable def localizationAwayOneEquiv :
    Localization.Away (1 : A) ≃ₐ[A] A :=
  (IsLocalization.atOne A (Localization.Away (1 : A))).symm

/-- The underlying `RingEquiv` of `localizationAwayOneEquiv`. -/
noncomputable def localizationAwayOneRingEquiv :
    Localization.Away (1 : A) ≃+* A :=
  (localizationAwayOneEquiv A).toRingEquiv

end Remark83

/-! ### The presheaf value `𝒪_X(R(T/s))` (equation 8.1.1 of Wedhorn) -/

/-! ### Rational localization data -/

/-- A *rational localization datum* for a Huber ring `A` packages together the data
needed to define the localization topology on `Aₛ = Localization.Away s` and its
completion `A⟨T/s⟩`: a pair of definition `(A₀, I)`, a finite set `T`, an element
`s`, and the condition that high powers of `I` map into the ring of definition `D`
under division by `s`.

This condition (`hopen`) captures the topological requirement from Wedhorn §8.1:
it ensures that multiplication by `1/s` is continuous in the localization topology.
For rational subsets where `T` generates an open ideal, this should hold
automatically (but the proof requires non-trivial algebra relating the openness
of `T · A` to the pair of definition). -/
structure RationalLocData (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] where
  /-- A pair of definition for `A`. -/
  P : PairOfDefinition A
  /-- The finite set `T ⊂ A`. -/
  T : Finset A
  /-- The element `s ∈ A`. -/
  s : A
  /-- High powers of `I` map into the ring of definition `D` under division by `s`. -/
  hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
    divByS (↑b : A) s ∈ locSubring P T s

section PresheafValue

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The localization topology on `Aₛ` determined by a rational localization datum. -/
noncomputable def RationalLocData.topology (D : RationalLocData A) :
    TopologicalSpace (Localization.Away D.s) :=
  locTopology D.P D.T D.s D.hopen

/-- The `IsTopologicalRing` instance on `Localization.Away D.s` with the localization topology. -/
noncomputable def RationalLocData.isTopologicalRing (D : RationalLocData A) :
    @IsTopologicalRing (Localization.Away D.s) D.topology _ :=
  (locBasis D.P D.T D.s D.hopen).toRingFilterBasis.isTopologicalRing

/-- The `IsTopologicalAddGroup` instance on `Localization.Away D.s`
from the localization topology. -/
noncomputable def RationalLocData.isTopologicalAddGroup (D : RationalLocData A) :
    @IsTopologicalAddGroup (Localization.Away D.s) D.topology _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _ D.topology D.isTopologicalRing

/-- The `UniformSpace` on `Localization.Away D.s` induced by the localization topology. -/
noncomputable def RationalLocData.uniformSpace (D : RationalLocData A) :
    UniformSpace (Localization.Away D.s) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _ D.topology D.isTopologicalAddGroup

/-- The `IsUniformAddGroup` instance on `Localization.Away D.s` with `D.uniformSpace`. -/
noncomputable def RationalLocData.isUniformAddGroup (D : RationalLocData A) :
    @IsUniformAddGroup (Localization.Away D.s) D.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup _ _ D.topology D.isTopologicalAddGroup

/-- The presheaf value `𝒪_X(R(T/s)) := A⟨T/s⟩`, defined as the completion of the
localization `Aₛ` with respect to the localization topology (§8.1, eq. 8.1.1 of Wedhorn).

This is the completion of `Localization.Away s` equipped with the topology
`locTopology P T s`, where `P` is a pair of definition for `A`. The topology
makes `D = A₀[t₁/s, …, tₙ/s]` into an open subring with the `(I · D)`-adic
subspace topology. -/
noncomputable def presheafValue (D : RationalLocData A) : Type _ :=
  @UniformSpace.Completion (Localization.Away D.s) D.uniformSpace

noncomputable instance (D : RationalLocData A) :
    CommRing (presheafValue D) :=
  @UniformSpace.Completion.commRing _ _ D.uniformSpace D.isUniformAddGroup
    D.isTopologicalRing

noncomputable instance (D : RationalLocData A) :
    TopologicalSpace (presheafValue D) :=
  @UniformSpace.toTopologicalSpace _ (@UniformSpace.Completion.uniformSpace
    (Localization.Away D.s) D.uniformSpace)

noncomputable instance (D : RationalLocData A) :
    UniformSpace (presheafValue D) :=
  @UniformSpace.Completion.uniformSpace (Localization.Away D.s) D.uniformSpace

noncomputable instance (D : RationalLocData A) :
    IsTopologicalRing (presheafValue D) :=
  @UniformSpace.Completion.topologicalRing _ _ D.uniformSpace
    D.isTopologicalRing D.isUniformAddGroup

noncomputable instance (D : RationalLocData A) :
    IsUniformAddGroup (presheafValue D) :=
  @UniformSpace.Completion.isUniformAddGroup _ D.uniformSpace _ D.isUniformAddGroup

instance (D : RationalLocData A) :
    CompleteSpace (presheafValue D) :=
  @UniformSpace.Completion.completeSpace _ D.uniformSpace

instance (D : RationalLocData A) :
    T0Space (presheafValue D) :=
  @UniformSpace.Completion.t0Space _ D.uniformSpace

/-- The dense embedding `Localization.Away D.s → presheafValue D`
(the completion map). -/
noncomputable def RationalLocData.coeRingHom (D : RationalLocData A) :
    Localization.Away D.s →+* presheafValue D :=
  @UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
    D.isTopologicalRing D.isUniformAddGroup

/-- The canonical ring homomorphism `ρ : A →+* A⟨T/s⟩`, the composition of
`algebraMap A (Localization.Away s)` with the completion embedding. -/
noncomputable def RationalLocData.canonicalMap (D : RationalLocData A) :
    A →+* presheafValue D :=
  D.coeRingHom.comp (algebraMap A (Localization.Away D.s))

/-! ### Presheaf values as objects of `CompleteTopCommRingCat` -/

/-- The presheaf value `A⟨T/s⟩` as an object of `CompleteTopCommRingCat`.
This bundles the completion of the localization with all its instances. -/
noncomputable def presheafValueObj (D : RationalLocData A) :
    CompleteTopCommRingCat.{_} :=
  CompleteTopCommRingCat.of (presheafValue D)

end PresheafValue

/-! ### Remark 8.3: `𝒪_X(X)` as a concrete type

Remark 8.3 of Wedhorn: since `X = R({1}/1)`, the global sections are
`𝒪_X(X) = presheafValue (globalLocData P)`.

This is the completion of `Localization.Away 1` with the localization topology.
Since `Localization.Away 1 ≃ₐ[A] A` (by `localizationAwayOneEquiv`), this
completion is abstractly isomorphic to `Â`. -/

section GlobalSections

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The rational localization datum for the global sections `R({1}/1)`. -/
def globalLocData (P : PairOfDefinition A) : RationalLocData A where
  P := P
  T := {1}
  s := 1
  hopen := hopen_away_one P {1}

/-- The presheaf value on the whole space `𝒪_X(X)`, where `X = Spa(A, A⁺)`.
By Remark 8.3 of Wedhorn, `X = R({1}/1)`, so this is the completion of
`Localization.Away 1` with the localization topology. -/
noncomputable def presheafGlobal (P : PairOfDefinition A) : Type _ :=
  presheafValue (globalLocData P)

end GlobalSections

/-! ### Restriction maps data

A Huber pair `(A, A⁺)` *has restriction maps* if for every inclusion of rational subsets
`R(T'/s') ⊆ R(T/s)`, the element `s` maps to a unit in `A⟨T'/s'⟩` and the induced
algebraic restriction map is continuous. These are the key inputs for Proposition 8.2
of Wedhorn (existence and uniqueness of restriction maps).

For discrete rings, these conditions are easy to verify (`HasRestrictionMaps.discrete`).
For general Huber rings, they require the full affinoid ring structure on `A⟨T/s⟩`
and Proposition 7.52. -/

/-- A Huber pair `(A, A⁺)` *has restriction maps* if for every inclusion of rational
subsets `R(T'/s') ⊆ R(T/s)`, the canonical map sends `s` to a unit in `A⟨T'/s'⟩`
and the induced algebraic lift is continuous (Lemma 8.1 / Proposition 8.2 of Wedhorn). -/
class HasRestrictionMaps (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] : Prop where
  /-- The image of `s` under the canonical map `A → A⟨T'/s'⟩` is a unit
  when `R(T'/s') ⊆ R(T/s)` (key ingredient of Lemma 8.1 / Prop 8.2). -/
  isUnit_canonicalMap_s : ∀ (D D' : RationalLocData A),
    rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s → IsUnit (D'.canonicalMap D.s)
  /-- The algebraic restriction map is continuous with the localization topology
  on the source and the completion topology on the target. -/
  restrictionMapAlg_continuous : ∀ (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s),
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s D D' h))

/-! ### Restriction maps (Proposition 8.2 of Wedhorn)

For an inclusion `R(T'/s') ⊆ R(T/s)` of rational subsets, there exists a unique
continuous ring homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩` such that `σ ∘ ρ = ρ'`, where
`ρ : A → A⟨T/s⟩` and `ρ' : A → A⟨T'/s'⟩` are the canonical maps (Lemma 8.1).

These restriction maps make the assignment `R(T/s) ↦ A⟨T/s⟩` into a presheaf
on the basis of rational subsets (Proposition 8.2 of Wedhorn). -/

section RestrictionMaps

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [HasRestrictionMaps A]

/-- The image of `s` under the canonical map `A → A⟨T'/s'⟩` is a unit
when `R(T'/s') ⊆ R(T/s)` (key ingredient of Lemma 8.1 / Prop 8.2). -/
theorem isUnit_canonicalMap_s (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) :=
  HasRestrictionMaps.isUnit_canonicalMap_s D D' h

/-- The algebraic part of the restriction map: a ring homomorphism
`Localization.Away D.s →+* presheafValue D'` extending `D'.canonicalMap`,
using `IsLocalization.Away.lift`. -/
noncomputable def restrictionMapAlg (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  IsLocalization.Away.lift D.s (isUnit_canonicalMap_s D D' h)

/-- The algebraic restriction map is continuous with the localization topology
on the source and the completion topology on the target. -/
theorem restrictionMapAlg_continuous (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (restrictionMapAlg D D' h) :=
  HasRestrictionMaps.restrictionMapAlg_continuous D D' h

/-- The restriction map `σ : A⟨T/s⟩ →+* A⟨T'/s'⟩` for `R(T'/s') ⊆ R(T/s)`,
constructed as the completion-extension of the algebraic lift
(Proposition 8.2(1) of Wedhorn). -/
noncomputable def restrictionMapHom (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D →+* presheafValue D' := by
  -- Source instances: Localization.Away D.s with D's localization topology
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  -- Target instances: presheafValue D' = Completion of (Localization.Away D'.s)
  -- These are automatically derived from D'.uniformSpace via Completion instances,
  -- but we need to put them in scope explicitly.
  letI us' : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (restrictionMapAlg D D' h) (restrictionMapAlg_continuous D D' h)

/-- The *restriction map* `σ : A⟨T/s⟩ → A⟨T'/s'⟩` for an inclusion of rational
subsets `R(T'/s') ⊆ R(T/s)` (Proposition 8.2(1) of Wedhorn).

This is the unique continuous ring homomorphism compatible with the canonical
maps from `A`, given by the universal property of `A⟨T/s⟩` (Lemma 8.1). -/
noncomputable def restrictionMap (D D' : RationalLocData A)
    (_ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D → presheafValue D' :=
  restrictionMapHom D D' ‹_›

/-- The restriction map applied to an element in the dense image of the completion embedding
equals the algebraic restriction map. -/
private theorem restrictionMapHom_coe (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (a : Localization.Away D.s) :
    restrictionMapHom D D' h
      (@UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
        D.isTopologicalRing D.isUniformAddGroup a) =
      restrictionMapAlg D D' h a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg D D' h) (restrictionMapAlg_continuous D D' h) a

/-- Restriction maps compose (functoriality of the presheaf on rational subsets). -/
theorem restrictionMap_comp (D D' D'' : RationalLocData A)
    (h₁ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (h₂ : rationalOpen D''.T D''.s ⊆ rationalOpen D'.T D'.s) :
    restrictionMap D' D'' h₂ ∘ restrictionMap D D' h₁ =
      restrictionMap D D'' (h₂.trans h₁) := by
  -- Set up instances
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  letI : UniformSpace (Localization.Away D''.s) := D''.uniformSpace
  letI : IsTopologicalRing (Localization.Away D''.s) := D''.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D''.s) := D''.isUniformAddGroup
  -- Step 1: The composition (restrictionMapHom D' D'').comp(restrictionMapAlg D D')
  --       = restrictionMapAlg D D'' as ring homs Localization.Away D.s →+* presheafValue D''
  have alg_comp_eq :
      (restrictionMapHom D' D'' h₂).comp (restrictionMapAlg D D' h₁) =
      restrictionMapAlg D D'' (h₂.trans h₁) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    ext r
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq]
    -- Goal: restrictionMapHom D' D'' h₂ (D'.canonicalMap r) = D''.canonicalMap r
    change restrictionMapHom D' D'' h₂ (D'.coeRingHom (algebraMap A _ r)) = D''.canonicalMap r
    -- D'.coeRingHom = Completion.coeRingHom with D' instances
    change restrictionMapHom D' D'' h₂
      (@UniformSpace.Completion.coeRingHom _ _ D'.uniformSpace
        D'.isTopologicalRing D'.isUniformAddGroup (algebraMap A _ r)) = _
    rw [restrictionMapHom_coe, restrictionMapAlg, IsLocalization.Away.lift_eq]
  -- Step 2: Use Completion.ext' to show the composed extension maps are equal
  ext x
  change (restrictionMapHom D' D'' h₂) ((restrictionMapHom D D' h₁) x) =
    (restrictionMapHom D D'' (h₂.trans h₁)) x
  refine @UniformSpace.Completion.ext' _ D.uniformSpace (presheafValue D'') _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    UniformSpace.Completion.continuous_extension ?_ x
  -- They agree on coe a
  intro a
  -- The LHS is (extension(f) ∘ extension(g)) ↑a, the RHS is extension(h) ↑a
  simp only [Function.comp]
  erw [UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (restrictionMapAlg_continuous D D' h₁)),
    UniformSpace.Completion.extension_coe
      (uniformContinuous_addMonoidHom_of_continuous
        (restrictionMapAlg_continuous D D'' (h₂.trans h₁)))]
  exact congr_fun (congrArg DFunLike.coe alg_comp_eq) a

/-- The restriction map for the identity inclusion is the identity. -/
theorem restrictionMap_id (D : RationalLocData A) :
    restrictionMap D D (le_refl _) = id := by
  -- Set up instances for the localization topology
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  -- restrictionMapAlg D D _ = D.coeRingHom by uniqueness of the localization lift
  have alg_eq : restrictionMapAlg D D (le_refl _) = D.coeRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    ext r
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
      RationalLocData.coeRingHom, RationalLocData.canonicalMap]
  -- Use Completion.ext: two continuous maps from Completion to a T2 space agreeing on
  -- the dense image are equal.
  ext x
  change restrictionMapHom D D (le_refl _) x = x
  refine @UniformSpace.Completion.ext' _ D.uniformSpace (presheafValue D) _ _ _ _
    UniformSpace.Completion.continuous_extension continuous_id ?_ x
  intro a
  -- Goal: Completion.extension (restrictionMapAlg D D _) (↑a) = id (↑a)
  simp only [id]
  erw [UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (restrictionMapAlg_continuous D D (le_refl _)))]
  exact congr_fun (congrArg DFunLike.coe alg_eq) a

/-- The restriction map is continuous between the presheaf value topologies
(Proposition 8.2 of Wedhorn). -/
theorem restrictionMapHom_continuous (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Continuous (restrictionMapHom D D' h) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.continuous_extension

/-- The restriction map as a morphism in `CompleteTopCommRingCat`
(Proposition 8.2 of Wedhorn). -/
noncomputable def restrictionMapMor (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValueObj D ⟶ presheafValueObj D' :=
  ⟨restrictionMapHom D D' h, restrictionMapHom_continuous D D' h⟩

/-- A *rational covering* of a rational subset `R(T/s)` is a finite collection of
rational subsets `R(Tᵢ/sᵢ)` that cover `R(T/s)` and are contained in it
(Wedhorn, §8.1, before Definition 8.5). -/
structure RationalCovering (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] where
  /-- The base rational localization datum. -/
  base : RationalLocData A
  /-- The covering rational localization data. -/
  covers : Finset (RationalLocData A)
  /-- Each covering piece is contained in the base. -/
  hsubset : ∀ D ∈ covers, rationalOpen D.T D.s ⊆ rationalOpen base.T base.s
  /-- The covering pieces cover the base. -/
  hcover : ∀ v ∈ rationalOpen base.T base.s,
    ∃ D ∈ covers, v ∈ rationalOpen D.T D.s

/-- In a discrete topological ring, topologically nilpotent elements are nilpotent:
`a^n → 0` in the discrete topology means `a^N = 0` for some `N`. -/
private theorem isNilpotent_of_isTopologicallyNilpotent_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsNilpotent a := by
  have h0 : ({0} : Set A) ∈ nhds (0 : A) := isOpen_discrete {0} |>.mem_nhds rfl
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha h0)
  exact ⟨N, Set.mem_singleton_iff.mp (hN N le_rfl)⟩

/-- For a discrete ring `A`, the localization topology on `Localization.Away s` is
discrete (`⊥`): since the ideal of definition `I` has nilpotent generators (elements
of `I` are topologically nilpotent, and in discrete topology this means nilpotent),
the ideal `J = I · D` is nilpotent, so `locNhd P T s M = {0}` for large `M`. -/
private theorem locTopology_eq_bot_of_discrete {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] (D : RationalLocData A) :
    D.topology = ⊥ := by
  -- Step 1: Elements of I are nilpotent in A₀
  have hI_le : D.P.I ≤ nilradical D.P.A₀ := by
    intro ⟨a, ha⟩ haI
    obtain ⟨n, hn⟩ := isNilpotent_of_isTopologicallyNilpotent_discrete
      (D.P.isTopologicallyNilpotent_of_mem haI)
    exact ⟨n, Subtype.val_injective (by simp [hn])⟩
  -- Step 2: I is nilpotent (finitely generated ideal contained in nilradical)
  obtain ⟨M, hM⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical D.P.fg).mpr hI_le
  -- hM : D.P.I ^ M = 0 (as ideal, 0 = ⊥)
  -- Step 3: J^M = ⊥
  have hJ : locIdeal D.P D.T D.s ^ M = ⊥ := by
    rw [show locIdeal D.P D.T D.s = Ideal.map (algebraMapD D.P D.T D.s) D.P.I from rfl,
      ← Ideal.map_pow]
    simp [hM]
  -- Step 4: locNhd P T s M = {0}
  have hNhd : ∀ x ∈ locNhd D.P D.T D.s M, x = (0 : Localization.Away D.s) := by
    rintro _ ⟨d, hd, rfl⟩
    have hd' : d ∈ (locIdeal D.P D.T D.s) ^ M := hd
    rw [hJ] at hd'
    simp [show d = 0 from hd']
  -- Step 5: D.topology = ⊥
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI := D.isTopologicalRing
  have hbasis := locBasis D.P D.T D.s D.hopen
  -- locNhd M is open in D.topology (it's a basis element)
  have hopen_nhd : @IsOpen _ D.topology
      ((locNhd D.P D.T D.s M : AddSubgroup (Localization.Away D.s)) : Set _) :=
    (hbasis.openAddSubgroup M).isOpen
  -- locNhd M = {0} by step 4
  have hNhd_eq : ((locNhd D.P D.T D.s M : AddSubgroup _) : Set (Localization.Away D.s)) =
      {0} := by
    ext y; exact ⟨fun hy => Set.mem_singleton_iff.mpr (hNhd y hy),
      fun hy => Set.mem_singleton_iff.mp hy ▸ zero_mem_locNhd D.P D.T D.s M⟩
  -- {0} is open
  have hopen_zero : @IsOpen _ D.topology ({0} : Set (Localization.Away D.s)) :=
    hNhd_eq ▸ hopen_nhd
  apply eq_bot_of_singletons_open
  intro x
  rw [show ({x} : Set (Localization.Away D.s)) = (x + ·) '' {0} from by simp]
  exact (isOpenMap_add_left x) _ hopen_zero

instance HasRestrictionMaps.discrete {A : Type*} [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] [PlusSubring A] :
    HasRestrictionMaps A where
  isUnit_canonicalMap_s := fun D D' h => by
    -- It suffices to show algebraMap A (Localization.Away D'.s) D.s is a unit,
    -- then push through D'.coeRingHom
    suffices hu : IsUnit (algebraMap A (Localization.Away D'.s) D.s) by
      change IsUnit (D'.coeRingHom (algebraMap A (Localization.Away D'.s) D.s))
      exact hu.map D'.coeRingHom
    -- Step 1: D'.s ∈ √(span {D.s}) via prime ideal argument
    have hrad : D'.s ∈ Ideal.radical (Ideal.span {D.s}) := by
      classical
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro p ⟨hsp, hp⟩
      -- p is a prime ideal containing span {D.s}, so D.s ∈ p
      have hDs : D.s ∈ p := hsp (Ideal.subset_span (Set.mem_singleton D.s))
      -- By contradiction, assume D'.s ∉ p
      by_contra hD's
      haveI := hp
      -- Construct the trivial valuation at p directly
      haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
      let φ : A →+* FractionRing (A ⧸ p) :=
        (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
      let w : Valuation A (WithZero (Multiplicative ℤ)) :=
        (1 : Valuation (FractionRing (A ⧸ p)) _).comap φ
      let v := ofValuation w
      -- v ∈ Spa A A⁺
      have hv_spa : v ∈ Spa A A⁺ := by
        refine ⟨?_, ?_⟩
        · apply isContinuous_ofValuation_of; intro γ; exact isOpen_discrete _
        · intro f hf; change w f ≤ w 1
          simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
      -- v.supp = p
      have hv_supp : v.supp = p := by
        rw [supp_ofValuation]; ext a
        simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply, φ, RingHom.comp_apply,
          Valuation.one_apply_eq_zero_iff]
        exact ⟨fun h => Ideal.Quotient.eq_zero_iff_mem.mp
          ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
            (by rwa [map_zero])),
          fun ha => by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]; rfl⟩
      -- Key: w t' ≤ w D'.s for all t' (because D'.s ∉ p means w D'.s = 1)
      have hw_Ds : w D'.s = 1 := by
        simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
        apply Valuation.one_apply_of_ne_zero
        intro heq
        apply hD's
        exact Ideal.Quotient.eq_zero_iff_mem.mp
          ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
            (by rwa [map_zero]))
      -- v ∈ rationalOpen D'.T D'.s
      have hv_rat : v ∈ rationalOpen D'.T D'.s := by
        refine ⟨hv_spa, ?_, ?_⟩
        · intro t' _
          -- v.vle t' D'.s means w t' ≤ w D'.s = 1
          change w t' ≤ w D'.s
          rw [hw_Ds]
          simp only [w, Valuation.comap_apply]
          exact Valuation.one_apply_le_one _
        · -- ¬ v.vle D'.s 0 means w D'.s > 0 = w D'.s ≠ 0
          change ¬ (w D'.s ≤ w 0)
          simp [hw_Ds, w, map_zero]
      -- By h, v ∈ rationalOpen D.T D.s
      have hv_rat2 := h hv_rat
      -- So ¬ v.vle D.s 0, i.e., D.s ∉ supp(v) = p
      exact (hv_rat2.2.2) ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs))
    -- Step 2: Extract n with D'.s^n ∈ span {D.s}, i.e., a * D.s = D'.s^n
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
    -- Step 3: In Localization.Away D'.s, algebraMap(D'.s)^n is a unit
    have hunit_pow : IsUnit (algebraMap A (Localization.Away D'.s) D'.s ^ n) := by
      exact (IsLocalization.map_units (Localization.Away D'.s)
        (⟨D'.s, ⟨1, pow_one D'.s⟩⟩ : Submonoid.powers D'.s)).pow n
    -- algebraMap(a) * algebraMap(D.s) = algebraMap(D'.s)^n
    have heq : algebraMap A (Localization.Away D'.s) a *
        algebraMap A (Localization.Away D'.s) D.s =
        algebraMap A (Localization.Away D'.s) D'.s ^ n := by
      rw [← map_mul, ← map_pow, ha]
    -- Therefore algebraMap(D.s) is a unit
    rw [← heq] at hunit_pow
    exact isUnit_of_mul_isUnit_right hunit_pow
  restrictionMapAlg_continuous := fun D D' h => by
    have hbot : D.topology = ⊥ := locTopology_eq_bot_of_discrete D
    rw [hbot]
    exact continuous_bot

/-- For a discrete ring `A`, the `coeRingHom` embedding into the completion is bijective.
This follows because the uniform space is discrete (⊥), so the source is complete and T0,
making `coe : α → Completion α` an isomorphism (surjective via closed + dense range,
injective via T0). -/
private theorem coeRingHom_bijective_of_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    (D : RationalLocData A) :
    Function.Bijective D.coeRingHom := by
  have htop : D.topology = ⊥ := locTopology_eq_bot_of_discrete D
  -- Step 1: Show D.uniformSpace = ⊥
  -- D.uniformSpace = rightUniformSpace with D.topology
  -- rightUniformSpace.uniformity = comap (fun p => p.2 - p.1) (nhds 0)
  -- Since D.topology = ⊥ (discrete), nhds 0 = pure 0
  -- So uniformity = comap (sub) (pure 0) = principal {(a,b) | a = b}
  -- = (⊥ : UniformSpace).uniformity
  have hbot : D.uniformSpace = ⊥ := by
    -- D.uniformSpace = rightUniformSpace with D.topology
    -- uniformity = comap (fun p => p.2 - p.1) (nhds 0)
    -- D.topology = ⊥ (discrete), so nhds 0 = pure 0
    -- comap sub (pure 0) = principal {(a,b) | b-a = 0}
    -- = principal {(a,b) | a = b} = principal SetRel.id = (⊥ : UniformSpace).uniformity
    suffices h : D.uniformSpace.uniformity = Filter.principal SetRel.id by
      exact UniformSpace.ext (h.trans bot_uniformity.symm)
    -- Unfold D.uniformSpace
    change Filter.comap (fun p : Localization.Away D.s × Localization.Away D.s =>
      p.2 - p.1) (@nhds (Localization.Away D.s) D.topology 0) = Filter.principal SetRel.id
    -- D.topology = ⊥, so nhds 0 = pure 0
    have hpure : @nhds (Localization.Away D.s) D.topology 0 = pure 0 := by
      rw [htop]
      -- Now goal: @nhds _ (⊥ : TopologicalSpace _) 0 = pure 0
      letI : TopologicalSpace (Localization.Away D.s) := ⊥
      haveI : DiscreteTopology (Localization.Away D.s) := ⟨rfl⟩
      exact congr_fun (nhds_discrete _) 0
    rw [hpure, Filter.comap_pure]
    ext s
    simp only [Filter.mem_principal]
    constructor
    · intro h ⟨a, b⟩ (hab : a = b); exact h (show b - a = 0 by rw [hab, sub_self])
    · intro h ⟨a, b⟩ (hab : b - a = 0); exact h (sub_eq_zero.mp hab).symm
  -- Step 2: Put D.uniformSpace into the typeclass system
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  -- Step 3: Derive DiscreteUniformity, CompleteSpace, T0Space
  haveI : DiscreteUniformity (Localization.Away D.s) := ⟨hbot⟩
  -- DiscreteUniformity → DiscreteTopology → T1Space → T0Space (all automatic)
  -- DiscreteUniformity → CompleteSpace (automatic)
  constructor
  · -- Injective: coe is injective for T0 spaces
    exact UniformSpace.Completion.coe_injective _
  · -- Surjective: uniform embedding of complete space has closed range, + dense = surjective
    have hclosed := (UniformSpace.Completion.isUniformEmbedding_coe
      (Localization.Away D.s)).isClosedEmbedding.isClosed_range
    have hdense := UniformSpace.Completion.denseRange_coe (α := Localization.Away D.s)
    intro x
    have : x ∈ Set.range ((↑) : Localization.Away D.s →
        UniformSpace.Completion (Localization.Away D.s)) := by
      rw [← hclosed.closure_eq]
      exact hdense.closure_range ▸ Set.mem_univ x
    exact this

/-- For a discrete ring and a rational covering, the product restriction map is injective.
This is the key algebraic content of Theorem 8.28(c) of Wedhorn.

The proof proceeds as follows:
1. Since `A` has discrete topology, all localization topologies are discrete.
2. The completion maps `coe : Localization.Away s → presheafValue D` are bijective.
3. Reduce to showing: if `z ∈ Localization.Away C.base.s` maps to `0` under each
   localization map to `Localization.Away D.s` (for D in the covering), then `z = 0`.
4. Write `z = a / C.base.s^n`. The map to `Localization.Away D.s` sends `z` to
   `algebraMap(a) / algebraMap(C.base.s)^n`. For this to be `0`, we need
   `algebraMap(a) = 0` in `Localization.Away D.s`, i.e., `∃ k, D.s^k * a = 0`.
5. By the covering condition (using trivial valuations at primes), every prime `p`
   with `C.base.s ∉ p` contains some `D.s^k`. So `C.base.s ∈ √(Ann(a))`, giving
   `C.base.s^m * a = 0` for some `m`, i.e., `z = 0` in `Localization.Away C.base.s`. -/
theorem productRestriction_injective_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    (C : RationalCovering A) :
    Function.Injective (fun x : presheafValue C.base =>
      fun (D : C.covers) => restrictionMap C.base D (C.hsubset D D.prop) x) := by
  -- Step 1: coe is bijective for all involved localization data
  have hbij_base := coeRingHom_bijective_of_discrete C.base
  intro x y hxy
  -- Step 2: Since coe is surjective, find preimages
  obtain ⟨x', rfl⟩ := hbij_base.2 x
  obtain ⟨y', rfl⟩ := hbij_base.2 y
  -- Step 3: It suffices to show x' = y'
  suffices h : x' = y' by rw [h]
  -- Step 4: From hxy, restrictionMapAlg sends x' and y' to the same value for each D
  have hmap_eq : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) x' =
      restrictionMapAlg C.base D (C.hsubset D hD) y' := by
    intro D hD
    have h := congr_fun hxy ⟨D, hD⟩
    -- Beta-reduce: h becomes restrictionMap ... (coe x') = restrictionMap ... (coe y')
    simp only at h
    -- Convert using restrictionMapHom_coe
    have hx := restrictionMapHom_coe C.base D (C.hsubset D hD) x'
    have hy := restrictionMapHom_coe C.base D (C.hsubset D hD) y'
    rwa [hx.symm, hy.symm]
  -- Step 5: It suffices to show x' - y' = 0
  rw [show (x' = y') ↔ (x' - y' = 0) from sub_eq_zero.symm]
  set z := x' - y'
  -- Step 6: For each D, restrictionMapAlg sends z to 0 in presheafValue D
  have hz_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) z = 0 := by
    intro D hD
    have := hmap_eq D hD
    simp only [z, map_sub, sub_eq_zero] at this ⊢
    exact this
  -- Step 7: For each D, there is an algebraic lift g_D and restrictionMapAlg factors through coe
  -- First, show algebraMap(C.base.s) is a unit in each Localization.Away D.s
  have hs_unit : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      IsUnit (algebraMap A (Localization.Away D.s) C.base.s) := by
    intro D hD
    have hu := isUnit_canonicalMap_s C.base D (C.hsubset D hD)
    change IsUnit (D.coeRingHom (algebraMap A _ C.base.s)) at hu
    let e := RingEquiv.ofBijective D.coeRingHom (coeRingHom_bijective_of_discrete D)
    exact (MulEquiv.isUnit_map (f := e.toMulEquiv) (x := algebraMap A _ C.base.s)).mp hu
  -- Step 8: The algebraic lift g_D sends z to 0 in Localization.Away D.s
  have hz_alg_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      (IsLocalization.Away.lift C.base.s (hs_unit D hD) :
        Localization.Away C.base.s →+* Localization.Away D.s) z = 0 := by
    intro D hD
    -- restrictionMapAlg = D.coeRingHom ∘ algebraic_lift (by localization uniqueness)
    have lift_eq : restrictionMapAlg C.base D (C.hsubset D hD) =
        D.coeRingHom.comp (IsLocalization.Away.lift C.base.s (hs_unit D hD)) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers C.base.s)
      ext r
      simp only [RingHom.comp_apply, restrictionMapAlg,
        IsLocalization.Away.lift_eq, RationalLocData.canonicalMap,
        RationalLocData.coeRingHom]
    have h0 := hz_zero D hD
    rw [lift_eq, RingHom.comp_apply] at h0
    exact (coeRingHom_bijective_of_discrete D).1
      (h0.trans (map_zero D.coeRingHom).symm)
  -- Step 9: z = 0 in Localization.Away C.base.s
  -- This follows from: z maps to 0 in each Localization.Away D.s, and
  -- by the covering condition, the elements D.s generate the unit ideal in
  -- Localization.Away C.base.s (modulo radicals).
  -- Write z = mk'(a, s₀^m) for some a ∈ A
  obtain ⟨a, ⟨_, ⟨m, rfl⟩⟩, hz_eq⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers C.base.s) z
  -- Step 10: algebraMap(a) = 0 in each Localization.Away D.s
  have ha_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      algebraMap A (Localization.Away D.s) a = 0 := by
    intro D hD
    have h := hz_alg_zero D hD
    -- h : g_D(z) = 0 where z = mk'(a, s₀^m)
    -- By mk'_spec: mk'(a, s₀^m) * algebraMap(s₀^m) = algebraMap(a)
    -- Since z = mk'(a, s₀^m), we get z * algebraMap(s₀^m) = algebraMap(a)
    -- Applying g_D and using g_D(z) = 0: algebraMap(a) = 0
    -- z * algebraMap(s₀^m) = algebraMap(a)
    have hza : z * algebraMap A (Localization.Away C.base.s) (C.base.s ^ m) =
        algebraMap A (Localization.Away C.base.s) a := by
      rw [← hz_eq]; exact IsLocalization.mk'_spec _ _ _
    -- Apply g_D to both sides
    have hga := congr_arg (IsLocalization.Away.lift (S := Localization.Away C.base.s)
      C.base.s (hs_unit D hD)) hza
    simp only [map_mul, IsLocalization.Away.lift_eq] at hga
    rw [h, zero_mul] at hga
    exact hga.symm
  -- Step 11: ∃ k_D, D.s^k_D * a = 0
  have ha_ann : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      ∃ k : ℕ, D.s ^ k * a = 0 := by
    intro D hD
    have h := ha_zero D hD
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers D.s)] at h
    obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := h
    exact ⟨k, hk⟩
  -- Step 12: C.base.s ∈ √(Ann(a)) via covering + trivial valuations at primes
  -- Ann(a) = {b : A | b * a = 0} is an ideal
  -- For every prime p ⊇ Ann(a) with C.base.s ∉ p, the covering gives D with D.s ∉ p
  -- D.s^k ∈ Ann(a) ⊆ p and D.s ∉ p contradicts p being prime
  -- Hence C.base.s ∈ every prime ⊇ Ann(a), so C.base.s ∈ √Ann(a)
  -- Therefore ∃ M, C.base.s^M * a = 0, giving z = 0
  suffices hs_rad : C.base.s ∈
      (Ideal.span ({b : A | b * a = 0} : Set A)).radical by
    obtain ⟨M, hM⟩ := Ideal.mem_radical_iff.mp hs_rad
    -- C.base.s^M ∈ Ideal.span {b | b * a = 0}
    -- Need: C.base.s^M * a = 0
    -- Since hM : C.base.s^M ∈ Ideal.span {b | b * a = 0},
    -- and Ideal.span S is the smallest ideal containing S,
    -- elements of Ideal.span S are A-linear combinations of elements of S
    -- For b ∈ S, b * a = 0. So (∑ cᵢ * bᵢ) * a = ∑ cᵢ * (bᵢ * a) = 0
    have : C.base.s ^ M * a = 0 := by
      -- Every element of Ideal.span S satisfies: x * a = 0 when S = {b | b * a = 0}
      suffices ∀ (x : A) (_ : x ∈ Ideal.span ({b : A | b * a = 0} : Set A)),
          x * a = 0 by
        exact this _ hM
      intro x hx
      induction hx using Submodule.span_induction with
      | mem b hb => exact hb
      | zero => exact zero_mul a
      | add x y _ _ hxa hya => rw [add_mul, hxa, hya, add_zero]
      | smul c x _ hxa => rw [smul_eq_mul, mul_assoc, hxa, mul_zero]
    -- z = mk'(a, s₀^m) and C.base.s^M * a = 0
    rw [← hz_eq, IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨C.base.s ^ M, ⟨M, rfl⟩⟩, this⟩
  -- Prove hs_rad
  classical
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro p ⟨hp_ann, hp_prime⟩
  haveI := hp_prime
  by_contra hs_notin
  -- Trivial valuation at p
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) _).comap φ
  let v := ofValuation w
  have hv_spa : v ∈ Spa A A⁺ := by
    refine ⟨?_, ?_⟩
    · apply isContinuous_ofValuation_of; intro γ; exact isOpen_discrete _
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_supp : v.supp = p := by
    rw [supp_ofValuation]; ext b
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply, φ,
      RingHom.comp_apply, Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h => Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun hb => by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]; rfl⟩
  have hw_s : w C.base.s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero; intro heq; apply hs_notin
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hv_rat : v ∈ rationalOpen C.base.T C.base.s :=
    ⟨hv_spa,
      fun t _ => by
        change w t ≤ w C.base.s; rw [hw_s]
        simp only [w, Valuation.comap_apply]
        exact Valuation.one_apply_le_one _,
      by change ¬ (w C.base.s ≤ w 0); simp [hw_s, w, map_zero]⟩
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  have hDs_notin : D.s ∉ p := fun hDs =>
    hv_D.2.2 ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs))
  obtain ⟨k, hk⟩ := ha_ann D hD
  exact hDs_notin (Ideal.IsPrime.mem_of_pow_mem hp_prime k
    (hp_ann (Ideal.subset_span (show D.s ^ k * a = 0 from hk))))

end RestrictionMaps

end Spv
