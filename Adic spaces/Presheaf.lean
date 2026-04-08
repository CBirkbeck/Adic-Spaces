/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Valuation.LocalSubring
import «Adic spaces».AdicCompletionBridge
import «Adic spaces».CompleteTopCommRingCat
import «Adic spaces».LocalizationTopology
import «Adic spaces».Prop752
import «Adic spaces».RationalSubsets

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

open ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### Step 0: Rational subsets as `Opens` -/

/-- A rational subset `R(T/s)` as an open subset of `↥(Spa A A⁺)`. -/
def rationalOpens [DecidableEq A] (T : Finset A) (s : A) :
    TopologicalSpace.Opens ↥(Spa A A⁺) :=
  ⟨Subtype.val ⁻¹' rationalOpen T s, rationalOpen_isOpen T s⟩

/-! ### Step 1: The trivial rational subset is the whole space -/

/-- `R({1}/1) = Spa(A, A⁺)` (Remark 8.3 of Wedhorn). -/
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
  ext ⟨v, hv⟩
  simp only [rationalOpens, rationalOpen_singleton_one, Subtype.coe_preimage_self,
    TopologicalSpace.Opens.mk_univ, TopologicalSpace.Opens.coe_top, Set.mem_univ]

/-! ### The adic completion -/

/-- The *adic completion* `Â` of a topological ring `A`, as an object of `TopCommRingCat`. -/
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

/-- Localizing at `1` gives back the original ring: `Localization.Away 1 ≃ₐ[A] A`. -/
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

/-- A *rational localization datum* packages a pair of definition, finite set
`T`, element `s`, and openness condition for the localization topology on
`Aₛ` (Wedhorn §8.1). -/
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

/-- **Compatible plus subring** (Wedhorn Remark 7.17).

An affinoid ring `(A, A⁺)` has a *compatible plus subring* if for every rational
localization datum, the plus subring `A⁺` is contained in the ring of definition
`D.P.A₀`.

**Mathematical content.** By Wedhorn Definition 7.14, `A⁺` is an open integrally closed
subring of the power-bounded subring `A°`. It follows that `A⁺` is bounded
(Wedhorn Remark 7.17: every open integrally closed subring of `A°` is bounded).
By Wedhorn Proposition 6.4(3), every bounded subring is contained in some ring of
definition. Therefore, *for each rational localization datum*, one can always CHOOSE
the pair of definition so that `A⁺ ⊆ D.P.A₀`.

This choice is not automatic in the Lean formalization because `RationalLocData`
permits an arbitrary `P : PairOfDefinition`. The typeclass `CompatiblePlusSubring`
bundles the compatibility constraint: when the user constructs rational localization
data for an affinoid ring in practice, they choose the pair of definition to contain
`A⁺`, and this typeclass records that choice.

**Usage.** Instances of `HasLocLiftPowerBounded` that require the adic Nullstellensatz
(e.g., `HasLocLiftPowerBounded.tate`) need `A⁺ ⊆ D.P.A₀` to apply the valuative
criterion at Spa points. They take `[CompatiblePlusSubring A]` as a typeclass hypothesis.

**Future work.** For "uniform" affinoid rings with `A⁺ = A°`, this typeclass should be
derivable automatically. For non-uniform rings, the user provides it based on their
construction of the rational data. -/
class CompatiblePlusSubring (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] : Prop where
  /-- For every rational localization datum, `A⁺` is contained in the ring of definition. -/
  aplus_le_pod : ∀ (D : RationalLocData A), (A⁺ : Set A) ⊆ D.P.A₀

/-- The plus subring is contained in the ring of definition of any rational locale
(Wedhorn Remark 7.17, `CompatiblePlusSubring`-typeclass accessor). -/
theorem CompatiblePlusSubring.aplus_le_A₀ {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [PlusSubring A] [CompatiblePlusSubring A]
    (D : RationalLocData A) : (A⁺ : Set A) ⊆ D.P.A₀ :=
  CompatiblePlusSubring.aplus_le_pod D

section PresheafValue

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The localization topology on `Aₛ` determined by a rational localization datum. -/
@[reducible] noncomputable def RationalLocData.topology (D : RationalLocData A) :
    TopologicalSpace (Localization.Away D.s) :=
  locTopology D.P D.T D.s D.hopen

/-- The `IsTopologicalRing` instance from the localization topology. -/
@[reducible] noncomputable def RationalLocData.isTopologicalRing (D : RationalLocData A) :
    @IsTopologicalRing (Localization.Away D.s) D.topology _ :=
  (locBasis D.P D.T D.s D.hopen).toRingFilterBasis.isTopologicalRing

/-- The `IsTopologicalAddGroup` instance from the localization topology. -/
@[reducible] noncomputable def RationalLocData.isTopologicalAddGroup (D : RationalLocData A) :
    @IsTopologicalAddGroup (Localization.Away D.s) D.topology _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _ D.topology D.isTopologicalRing

/-- The `UniformSpace` induced by the localization topology. -/
@[reducible] noncomputable def RationalLocData.uniformSpace (D : RationalLocData A) :
    UniformSpace (Localization.Away D.s) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _ D.topology D.isTopologicalAddGroup

/-- The `IsUniformAddGroup` instance from the localization topology. -/
@[reducible] noncomputable def RationalLocData.isUniformAddGroup (D : RationalLocData A) :
    @IsUniformAddGroup (Localization.Away D.s) D.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup _ _ D.topology D.isTopologicalAddGroup

/-- The presheaf value `𝒪_X(R(T/s)) := A⟨T/s⟩`, the completion of
`Localization.Away s` with the localization topology
(§8.1, eq. 8.1.1 of Wedhorn). -/
noncomputable def presheafValue (D : RationalLocData A) : Type _ :=
  @UniformSpace.Completion (Localization.Away D.s) D.uniformSpace

/-- The `CommRing` instance on `presheafValue D`. -/
noncomputable instance (D : RationalLocData A) : CommRing (presheafValue D) :=
  @UniformSpace.Completion.commRing _ _ D.uniformSpace D.isUniformAddGroup
    D.isTopologicalRing

/-- The `TopologicalSpace` instance on `presheafValue D`. -/
noncomputable instance (D : RationalLocData A) : TopologicalSpace (presheafValue D) :=
  @UniformSpace.toTopologicalSpace _ (@UniformSpace.Completion.uniformSpace
    (Localization.Away D.s) D.uniformSpace)

/-- The `UniformSpace` instance on `presheafValue D`. -/
noncomputable instance (D : RationalLocData A) : UniformSpace (presheafValue D) :=
  @UniformSpace.Completion.uniformSpace (Localization.Away D.s) D.uniformSpace

/-- The `IsTopologicalRing` instance on `presheafValue D`. -/
noncomputable instance (D : RationalLocData A) : IsTopologicalRing (presheafValue D) :=
  @UniformSpace.Completion.topologicalRing _ _ D.uniformSpace
    D.isTopologicalRing D.isUniformAddGroup

/-- The `IsUniformAddGroup` instance on `presheafValue D`. -/
noncomputable instance (D : RationalLocData A) : IsUniformAddGroup (presheafValue D) :=
  @UniformSpace.Completion.isUniformAddGroup _ D.uniformSpace _ D.isUniformAddGroup

/-- The `CompleteSpace` instance on `presheafValue D`. -/
instance (D : RationalLocData A) : CompleteSpace (presheafValue D) :=
  @UniformSpace.Completion.completeSpace _ D.uniformSpace

/-- The `T0Space` instance on `presheafValue D`. -/
instance (D : RationalLocData A) : T0Space (presheafValue D) :=
  @UniformSpace.Completion.t0Space _ D.uniformSpace

/-- The completion map `Localization.Away D.s → presheafValue D`. -/
noncomputable def RationalLocData.coeRingHom (D : RationalLocData A) :
    Localization.Away D.s →+* presheafValue D :=
  @UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
    D.isTopologicalRing D.isUniformAddGroup

/-- The canonical ring homomorphism `ρ : A →+* A⟨T/s⟩`. -/
noncomputable def RationalLocData.canonicalMap (D : RationalLocData A) :
    A →+* presheafValue D :=
  D.coeRingHom.comp (algebraMap A (Localization.Away D.s))

/-! ### Presheaf values as objects of `CompleteTopCommRingCat` -/

/-- The presheaf value `A⟨T/s⟩` as an object of `CompleteTopCommRingCat`. -/
noncomputable def presheafValueObj (D : RationalLocData A) :
    CompleteTopCommRingCat.{_} :=
  CompleteTopCommRingCat.of (presheafValue D)

end PresheafValue

/-! ### Completion-side pair of definition (Wedhorn §8.1, completion route)

For the non-open prime Spa-point construction (Wedhorn Thm 8.28), we need
Lemma 7.45 applied to `presheafValue D` (the completion of the localization).
This requires a `PairOfDefinition` and `PlusSubring` on `presheafValue D`.

The ring of definition is the **topological closure** of `locSubring` in
`presheafValue D`. It is open (closure of open subgroup in a uniform completion
is open) and serves as both the ring of definition and the plus-subring. -/

section CompletedPair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The ring of definition on the completion: the topological closure
of the image of `locSubring` under the completion embedding.
This is the key object for the completion route. -/
noncomputable def RationalLocData.completedLocSubring (D : RationalLocData A) :
    Subring (presheafValue D) :=
  (locSubring D.P D.T D.s |>.map D.coeRingHom).topologicalClosure

/-- The image of `locSubring` under the completion embedding is contained
in the completed locSubring (the closure contains the image). -/
theorem RationalLocData.coeRingHom_locSubring_le_completedLocSubring
    (D : RationalLocData A) :
    (locSubring D.P D.T D.s).map D.coeRingHom ≤ D.completedLocSubring :=
  Subring.le_topologicalClosure _

/-- An element of `locSubring` maps into `completedLocSubring`. -/
theorem RationalLocData.coeRingHom_mem_completedLocSubring
    (D : RationalLocData A) {x : Localization.Away D.s}
    (hx : x ∈ locSubring D.P D.T D.s) :
    D.coeRingHom x ∈ D.completedLocSubring :=
  D.coeRingHom_locSubring_le_completedLocSubring ⟨x, hx, rfl⟩

/-- The image of `A⁺` under `canonicalMap` lands in `completedLocSubring`
when `A⁺ ⊆ A₀ = D.P.A₀` (the standard hypothesis for affinoid rings).
This ensures the `PlusSubring` condition `A⁺ ≤ B⁺.comap(canonicalMap)`. -/
theorem RationalLocData.canonicalMap_Aplus_le_completedLocSubring
    (D : RationalLocData A) [PlusSubring A]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D.P.A₀) :
    ∀ a ∈ (A⁺ : Set A), D.canonicalMap a ∈ D.completedLocSubring := by
  intro a ha
  exact D.coeRingHom_mem_completedLocSubring (algebraMap_mem_locSubring D.P D.T D.s
    (hAplus_le_A₀ ha))

/-- `completedLocSubring` is open in `presheafValue D`.

**Proof:** `locSubring` is open in `Localization.Away s` (by `locSubring_isOpen`).
Open sets are nhds-0 sets. In the uniform completion, the closure of a
nhds-0 set from the dense subspace is a nhds-0 set in the completion.
An additive subgroup containing a nhds-0 set is open. -/
theorem RationalLocData.completedLocSubring_isOpen (D : RationalLocData A) :
    IsOpen (D.completedLocSubring : Set (presheafValue D)) := by
  apply AddSubgroup.isOpen_of_mem_nhds (H := D.completedLocSubring.toAddSubgroup) (g := 0)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  have hmem : (locSubring D.P D.T D.s : Set (Localization.Away D.s)) ∈ nhds 0 :=
    (locSubring_isOpen D.P D.T D.s D.hopen).mem_nhds (locSubring D.P D.T D.s).zero_mem
  have hcl := (UniformSpace.Completion.isDenseInducing_coe (α := Localization.Away D.s)
    ).closure_image_mem_nhds hmem
  rwa [UniformSpace.Completion.coe_zero] at hcl

/-- `PlusSubring` on `presheafValue D`, with `B⁺ = completedLocSubring D`.
This is the natural plus-subring for the completion route: it contains
the image of `A⁺` (via `canonicalMap_Aplus_le_completedLocSubring`) and
is bounded for valuations in `Spa(presheafValue D, completedLocSubring D)`. -/
noncomputable instance RationalLocData.presheafValuePlusSubring
    (D : RationalLocData A) : PlusSubring (presheafValue D) where
  toSubring := D.completedLocSubring

/-- The canonical map `A →+* presheafValue D` sends `A⁺` into `B⁺`. -/
theorem RationalLocData.canonicalMap_integral (D : RationalLocData A)
    [PlusSubring A] (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D.P.A₀) :
    (A⁺ : Subring A) ≤ (PlusSubring.toSubring (A := presheafValue D)).comap
      D.canonicalMap := by
  intro a ha
  exact D.canonicalMap_Aplus_le_completedLocSubring hAplus_le_A₀ a ha

/-- The pullback of a Spa point on the completion satisfies the rational-open
valuation conditions `v(t) ≤ v(s)` for `t ∈ T` and `v(s) ≠ 0`.

This is the algebraic core of the completion route for Wedhorn Thm 8.28:
- `v(t) ≤ v(s)`: because `t/s ∈ locSubring ⊆ completedLocSubring` and
  the Spa condition gives `w(t/s) ≤ 1`, so by multiplicativity `w(t) ≤ w(s)`
- `v(s) ≠ 0`: because `s` is a unit in `Localization.Away s`, hence
  `canonicalMap s` is a unit in `presheafValue D` -/
theorem RationalLocData.comap_canonicalMap_vle (D : RationalLocData A)
    {w : ValuativeRel (presheafValue D)}
    (hw_bdd : ∀ d ∈ D.completedLocSubring, w.vle d 1)
    {t : A} (ht : t ∈ D.T) :
    w.vle (D.canonicalMap t) (D.canonicalMap D.s) := by
  have hmem : D.coeRingHom (divByS t D.s) ∈ D.completedLocSubring :=
    D.coeRingHom_mem_completedLocSubring (divByS_mem_locSubring D.P D.T D.s ht)
  have hle := hw_bdd _ hmem
  have hspec : divByS t D.s * algebraMap A (Localization.Away D.s) D.s =
      algebraMap A (Localization.Away D.s) t :=
    IsLocalization.mk'_spec _ t ⟨D.s, Submonoid.mem_powers D.s⟩
  have hspec' : D.coeRingHom (divByS t D.s) * D.canonicalMap D.s = D.canonicalMap t := by
    rw [show D.canonicalMap = D.coeRingHom.comp (algebraMap A _) from rfl,
      RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hspec]
  rw [← hspec']
  have := w.mul_vle_mul_left hle (D.canonicalMap D.s)
  rwa [one_mul] at this

/-- `canonicalMap s` is a unit in `presheafValue D` (since `s` is a unit in
`Localization.Away s` and ring homs preserve units). Hence `¬ v(s) ≤ᵥ 0`. -/
theorem RationalLocData.canonicalMap_s_isUnit (D : RationalLocData A) :
    IsUnit (D.canonicalMap D.s) := by
  have : IsUnit (algebraMap A (Localization.Away D.s) D.s) :=
    IsLocalization.map_units (Localization.Away D.s) ⟨D.s, Submonoid.mem_powers D.s⟩
  exact this.map D.coeRingHom

/-- `¬ (comap canonicalMap w).vle s 0` — the pullback valuation does not
send `s` to zero, because `canonicalMap s` is a unit. -/
theorem RationalLocData.comap_canonicalMap_not_vle_s_zero (D : RationalLocData A)
    {w : ValuativeRel (presheafValue D)} :
    ¬ (ValuativeRel.comap D.canonicalMap w).vle D.s 0 := by
  rw [ValuativeRel.comap_vle, map_zero]
  exact ValuativeRel.not_vle_zero_of_isUnit D.canonicalMap_s_isUnit

/-! #### Ideal of definition and pair of definition on the completion -/

/-- The ring homomorphism `locSubring → completedLocSubring` induced by the
completion embedding. -/
noncomputable def RationalLocData.locSubringToCompleted (D : RationalLocData A) :
    locSubring D.P D.T D.s →+* D.completedLocSubring :=
  (D.coeRingHom.comp (locSubring D.P D.T D.s).subtype).codRestrict
    D.completedLocSubring
    (fun x ↦ D.coeRingHom_mem_completedLocSubring x.prop)

/-- The ideal of definition on `completedLocSubring`: image of `locIdeal`
under the completion embedding. -/
noncomputable def RationalLocData.completedLocIdeal (D : RationalLocData A) :
    Ideal D.completedLocSubring :=
  Ideal.map D.locSubringToCompleted (locIdeal D.P D.T D.s)

/-- The completed ideal of definition is finitely generated. -/
theorem RationalLocData.completedLocIdeal_fg (D : RationalLocData A) :
    D.completedLocIdeal.FG :=
  (locIdeal_fg D.P D.T D.s).map _

/-- The subspace topology on `completedLocSubring` equals the
`completedLocIdeal`-adic topology. This is the analogue of `locSubring_isAdic`
for the completed pair.

**Proof route:** The localization satisfies `IsAdic locIdeal` on `locSubring`
(by `locSubring_isAdic`). In the completion, the nhds-0 basis consists of
closures of `locIdeal^n`-images (by density), which are the powers of
`completedLocIdeal`. Hence the subspace topology agrees with the adic topology.

This is the single remaining nontrivial sub-piece for the completion-side
`PairOfDefinition`. -/
theorem RationalLocData.completedLocSubring_isAdic (D : RationalLocData A) :
    @IsAdic D.completedLocSubring _ (TopologicalSpace.induced
      D.completedLocSubring.subtype inferInstance) D.completedLocIdeal := by
  have _h_pre := locSubring_topology_eq_adic D.P D.T D.s D.hopen
  sorry

/-- **Pair of definition on `presheafValue D`** (the completion of the
localization). Ring of definition = `completedLocSubring`, ideal =
`completedLocIdeal`. This is the completion-side analogue of
`locPairOfDefinition` from Prop752.lean. -/
noncomputable def RationalLocData.completedPairOfDefinition (D : RationalLocData A) :
    PairOfDefinition (presheafValue D) where
  A₀ := D.completedLocSubring
  I := D.completedLocIdeal
  isOpen := D.completedLocSubring_isOpen
  fg := D.completedLocIdeal_fg
  isAdic := D.completedLocSubring_isAdic

/-! #### IsAdicComplete and Lemma 7.45 application infrastructure -/

/-- The underlying function of `locSubringToCompleted`, viewed as
`completedLocSubring.subtype ∘ locSubringToCompleted = coe ∘ locSubring.subtype`,
is uniformly inducing for the subspace uniformities from `D.uniformSpace`
and from the completion. -/
theorem RationalLocData.locSubringToCompleted_val_isUniformInducing
    (D : RationalLocData A) :
    @IsUniformInducing (locSubring D.P D.T D.s) (presheafValue D)
      (@instUniformSpaceSubtype (Localization.Away D.s) (· ∈ locSubring D.P D.T D.s)
        D.uniformSpace)
      (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)
      (D.completedLocSubring.subtype ∘ D.locSubringToCompleted) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  have hcomp : D.completedLocSubring.subtype ∘ D.locSubringToCompleted =
      (UniformSpace.Completion.coe' : Localization.Away D.s → presheafValue D) ∘
      (locSubring D.P D.T D.s).subtype := by ext; rfl
  rw [hcomp]
  exact (UniformSpace.Completion.isUniformInducing_coe (α := Localization.Away D.s)).comp
    isUniformEmbedding_subtype_val.isUniformInducing

/-- `completedLocSubring` as an `AbstractCompletion` of `locSubring`.
All fields use the subspace uniformities from `D.uniformSpace` (source)
and `Completion.uniformSpace` (target). -/
noncomputable def RationalLocData.completedAbstractCompletion (D : RationalLocData A) :
    @AbstractCompletion (locSubring D.P D.T D.s)
      (@instUniformSpaceSubtype _ (· ∈ locSubring D.P D.T D.s) D.uniformSpace) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI hclosed : IsClosed (D.completedLocSubring : Set (presheafValue D)) :=
    Subring.isClosed_topologicalClosure _
  exact {
    space := D.completedLocSubring
    coe := D.locSubringToCompleted
    uniformStruct := instUniformSpaceSubtype
    complete := hclosed.completeSpace_coe
    separation := Subtype.t0Space
    isUniformInducing :=
      isUniformEmbedding_subtype_val.isUniformInducing.isUniformInducing_comp_iff.mp
        D.locSubringToCompleted_val_isUniformInducing
    dense := by
      intro ⟨x, hx⟩
      rw [mem_closure_iff_nhds]
      intro U hU
      rw [nhds_induced, Filter.mem_comap] at hU
      obtain ⟨V, hV, hVU⟩ := hU
      have hx_cl : x ∈ closure ((locSubring D.P D.T D.s).map D.coeRingHom : Set _) := hx
      obtain ⟨y, hyV, hy_map⟩ := mem_closure_iff_nhds.mp hx_cl V hV
      obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hy_map
      exact ⟨⟨D.coeRingHom z, D.coeRingHom_mem_completedLocSubring hz⟩,
        hVU hyV, ⟨⟨z, hz⟩, rfl⟩⟩
  }

/-- `completedLocSubring` is `completedLocIdeal`-adically complete.
Uses the `AbstractCompletion` comparison with `AdicCompletion`. -/
instance RationalLocData.completedLocSubring_isAdicComplete (D : RationalLocData A) :
    @IsAdicComplete D.completedLocSubring _ D.completedLocIdeal
      D.completedLocSubring _ _ := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : IsUniformAddGroup (locSubring D.P D.T D.s) := ⟨
    isUniformEmbedding_subtype_val.isUniformInducing.uniformContinuous_iff.mpr
      (uniformContinuous_sub.comp
        (isUniformEmbedding_subtype_val.uniformContinuous.prodMap
          isUniformEmbedding_subtype_val.uniformContinuous))⟩
  have _hadic := locSubring_topology_eq_adic D.P D.T D.s D.hopen
  let _ac₁ := D.completedAbstractCompletion
  let _ac₂ := AdicCompletionBridge.adicAbstractCompletion (locIdeal D.P D.T D.s) _hadic
  sorry

/-- The preimage ideal of `p` under `canonicalMap`, as an ideal of `presheafValue D`.
For the Zorn step, this is the ideal generated by `p` in the completion. -/
noncomputable def RationalLocData.liftedIdeal (D : RationalLocData A)
    (p : Ideal A) : Ideal (presheafValue D) :=
  Ideal.map D.canonicalMap p

/-- The support of the pullback valuation contains `p` when
`liftedIdeal p ≤ w.supp`. This is how the non-open prime construction
ensures `p ≤ v.supp` for the pulled-back valuation `v`. -/
theorem RationalLocData.supp_comap_ge_of_liftedIdeal_le (D : RationalLocData A)
    {p : Ideal A} {w : Spv (presheafValue D)}
    (h : D.liftedIdeal p ≤ w.supp) :
    p ≤ (comap D.canonicalMap w).supp := by
  intro a ha
  rw [mem_supp_iff, comap_vle, map_zero]
  exact (mem_supp_iff w _).mp (h (Ideal.mem_map_of_mem _ ha))

/-- **The completion-transfer theorem for non-open primes** (Wedhorn §7.5 + §8.1).

Given a Spa point `w` on the completion `presheafValue D` whose support contains
the lifted ideal of a prime `p` (with `D.s ∉ p`), the pullback `comap(canonicalMap, w)`
is a Spa point on `A` in `rationalOpen D.T D.s` with `p ≤ supp`.

This is the algebraic core of the non-open-prime construction: it converts a
completion-side Spa point (from Lemma 7.45 applied to the completed pair)
into the existential needed by `mem_prime_of_rational_subset_nonOpen`.

Assumes `Continuous D.canonicalMap` (proved in PresheafIdentification.lean). -/
theorem RationalLocData.exists_rationalOpen_of_completion_spa (D : RationalLocData A)
    [PlusSubring A] (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D.P.A₀)
    (hcont : Continuous D.canonicalMap)
    {p : Ideal A} [p.IsPrime] (_hs : D.s ∉ p)
    {w : Spv (presheafValue D)}
    (hw : w ∈ Spa (presheafValue D) D.completedLocSubring)
    (hw_supp : D.liftedIdeal p ≤ w.supp) :
    ∃ v ∈ rationalOpen D.T D.s, p ≤ v.supp := by
  refine ⟨comap D.canonicalMap w, ?_, D.supp_comap_ge_of_liftedIdeal_le hw_supp⟩
  refine ⟨comap_mem_spa hcont (D.canonicalMap_integral hAplus_le_A₀) hw, ?_, ?_⟩
  · intro t ht
    rw [comap_vle]
    exact D.comap_canonicalMap_vle hw.2 ht
  · exact @RationalLocData.comap_canonicalMap_not_vle_s_zero A _ _ _ D w.toValuativeRel

end CompletedPair

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

/-- The presheaf value on the whole space `𝒪_X(X)` (Remark 8.3 of Wedhorn). -/
noncomputable def presheafGlobal (P : PairOfDefinition A) : Type _ :=
  presheafValue (globalLocData P)

end GlobalSections

/-! ### Restriction maps (Proposition 8.2 of Wedhorn)

For a Huber ring `A` and every inclusion of rational subsets `R(T'/s') ⊆ R(T/s)`,
the element `s` maps to a unit in `A⟨T'/s'⟩` and the induced algebraic restriction
map is continuous. These are the key properties of Proposition 8.2 of Wedhorn.

For discrete rings, these conditions are easy to verify.
For general Huber rings, they require the full affinoid ring structure on `A⟨T/s⟩`
and Proposition 7.52. -/

/-- Given an open prime `p` containing `D.s` but not `D'.s`, construct a point in
`rationalOpen D'.T D'.s` whose support equals `p`, contradicting the inclusion
`rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s`.

Uses the trivial valuation on `Frac(A/p)`, which is continuous since `p` is open.
The sublevel sets of this valuation are `∅` (γ = 0), `p` (0 < γ ≤ 1), or `A` (γ > 1). -/
private theorem mem_prime_of_rational_subset_open {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime) (hp_open : IsOpen (p : Set A))
    (hDs : D.s ∈ p) : D'.s ∈ p := by
  classical
  by_contra hD's
  haveI := hp
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
      · subst hγ; convert isOpen_empty; ext a; simp [not_lt_zero']
      · by_cases h1 : (1 : WithZero (Multiplicative ℤ)) < γ
        · convert isOpen_univ; ext a
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, w, Valuation.comap_apply]
          exact lt_of_le_of_lt (Valuation.one_apply_le_one _) h1
        · push_neg at h1
          suffices {a : A | w a < γ} = (p : Set A) by rw [this]; exact hp_open
          ext a; simp only [Set.mem_setOf_eq]; constructor
          · intro ha
            rcases hw_one_or_zero a with ha0 | ha1
            · exact (hw_mem_iff a).mp ha0
            · exact absurd (ha1 ▸ ha |>.trans_le h1) (lt_irrefl _)
          · intro ha; rw [(hw_mem_iff a).mpr ha]; exact zero_lt_iff.mpr hγ
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_supp : v.supp = p := by
    rw [supp_ofValuation]; ext a; exact hw_mem_iff a
  have hw_Ds : w D'.s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero
    intro heq; apply hD's
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hv_rat : v ∈ rationalOpen D'.T D'.s := by
    refine ⟨hv_spa, ?_, ?_⟩
    · intro t' _; change w t' ≤ w D'.s; rw [hw_Ds]
      simp only [w, Valuation.comap_apply]; exact Valuation.one_apply_le_one _
    · change ¬ (w D'.s ≤ w 0)
      simp only [hw_Ds, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]
  exact (h hv_rat).2.2 ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs))

/-- For a non-open prime `p` containing `D.s`, if `R(T'/s') ⊆ R(T/s)` then `D'.s ∈ p`.

This is the hard case of Wedhorn Proposition 7.52 for non-open primes.

**Desired proof (Wedhorn Prop 7.52):** By contradiction, assume `D'.s ∉ p`.
Construct a continuous valuation `v ∈ Spa(A, A⁺)` with `v.supp = p` (equality).
Then `D.s ∈ p = v.supp` gives `v ∉ R(T/s)`, while `D'.s ∉ p = v.supp` and the
trivial-valuation argument (as in `mem_prime_of_rational_subset_open`) gives
`v ∈ R(T'/s')`, contradicting `R(T'/s') ⊆ R(T/s)`.

**Why this is blocked (three independent obstacles):**

1. **No completeness.** `[IsHuberRing A]` does not provide `IsAdicComplete P.I P.A₀`,
   which `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma 7.45)
   requires for the domination theorem.

2. **Support inequality.** Even with completeness, Lemma 7.45 only gives
   `p ≤ v.supp` (containment), not equality. The `restrictToConvex` step in the
   construction projects to a rank-1 value group, sending elements whose value-unit
   lies outside the convex subgroup `H_gen` to zero. This enlarges the support
   beyond `p` when the original value group has rank > 1.

3. **API constraint.** The public theorem `isUnit_canonicalMap_s` (used by
   `PresheafTateStructure.lean` with just `[IsHuberRing A]`) delegates to this lemma
   through `isUnit_canonicalMap_s_of_huber` and `mem_prime_of_rational_subset`.
   Adding hypotheses here would require changing the entire call chain, breaking
   downstream files.

**Resolution paths (any one suffices):**

(a) **Completion theory.** Formalize the completion `Â` of a Huber ring and
    `Spa(A, A⁺) ≅ Spa(Â, Â⁺)` (Wedhorn Prop 7.23). Then use Lemma 7.45 on
    the complete ring `Â` and pull back.

(b) **Rank-1 domination.** Prove that every non-open prime is the exact support
    of a continuous rank-1 valuation. This requires either Bourbaki's domination
    theorem or a noetherian ring-of-definition argument giving a discrete
    valuation with `v.supp = p`.

(c) **Alternative algebraic argument.** Find a proof that does not construct
    a Spa point at all. (No such proof is known to us.)

**References:** Wedhorn, Adic Spaces, Proposition 7.52, Lemma 7.45. -/
private theorem mem_prime_of_rational_subset_nonOpen {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime) (hp_notOpen : ¬IsOpen (p : Set A))
    (hDs : D.s ∈ p) : D'.s ∈ p := by
  haveI := hp
  by_contra hD's
  suffices ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp by
    obtain ⟨v, hv_rat, hv_supp⟩ := this
    exact (h hv_rat).2.2 ((v.mem_supp_iff D.s).mp (hv_supp hDs))
  sorry

/-- Given a prime `p` containing `D.s`, if `R(T'/s') ⊆ R(T/s)` then `D'.s ∈ p`
(Wedhorn Proposition 7.52). Case-splits on whether `p` is open. -/
theorem mem_prime_of_rational_subset {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime) (hDs : D.s ∈ p) : D'.s ∈ p := by
  by_cases hp_open : IsOpen (p : Set A)
  · exact mem_prime_of_rational_subset_open D D' h p hp hp_open hDs
  · exact mem_prime_of_rational_subset_nonOpen D D' h p hp hp_open hDs

/-- The localization-level unit: `algebraMap A (Localization.Away D'.s) D.s` is a unit
when `R(D'.T/D'.s) ⊆ R(D.T/D.s)`. This is the key algebraic step used both
by `isUnit_canonicalMap_s_of_huber` (which maps it to the completion) and
by `restrictionMapAlg_continuous_of_huber` (which uses it for the localization lift).
(Proposition 8.2 of Wedhorn, Lemma 7.45.) -/
theorem isUnit_algebraMap_s_of_huber {A : Type*} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (algebraMap A (Localization.Away D'.s) D.s) := by
  have hrad : D'.s ∈ Ideal.radical (Ideal.span {D.s}) := by
    classical
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p ⟨hsp, hp⟩
    have hDs : D.s ∈ p := hsp (Ideal.subset_span (Set.mem_singleton D.s))
    exact mem_prime_of_rational_subset D D' h p hp hDs
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  have hunit_pow : IsUnit (algebraMap A (Localization.Away D'.s) D'.s ^ n) :=
    (IsLocalization.map_units (Localization.Away D'.s)
      (⟨D'.s, ⟨1, pow_one D'.s⟩⟩ : Submonoid.powers D'.s)).pow n
  have heq : algebraMap A (Localization.Away D'.s) a *
      algebraMap A (Localization.Away D'.s) D.s =
      algebraMap A (Localization.Away D'.s) D'.s ^ n := by
    rw [← map_mul, ← map_pow, ha]
  rw [← heq] at hunit_pow
  exact isUnit_of_mul_isUnit_right hunit_pow

theorem isUnit_canonicalMap_s_of_huber {A : Type*} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  have hu := isUnit_algebraMap_s_of_huber D D' h
  change IsUnit (D'.coeRingHom (algebraMap A (Localization.Away D'.s) D.s))
  exact hu.map D'.coeRingHom

/-- Power-boundedness of `locLift(t/s)` in `D'.topology` for `t ∈ D.T`.

When `R(D'.T/D'.s) ⊆ R(D.T/D.s)`, the lift
`locLift : Localization.Away D.s →+* Localization.Away D'.s` sends
each generator `t/D.s` (for `t ∈ D.T`) to a power-bounded element
of `Localization.Away D'.s` equipped with `D'.topology`.

**Proof outline (Wedhorn, Proposition 7.14 / adic Nullstellensatz):**

The rational containment gives `v(t) ≤ v(D.s)` for every continuous
valuation `v` with `v(t') ≤ v(D'.s)` for all `t' ∈ D'.T`. Hence
`v(t/D.s) ≤ 1` for all such `v`, so `t/D.s` lies in the integral closure
of `locSubring D'.P D'.T D'.s` (which equals `{x : v(x) ≤ 1}` for the
localization valuations, by Prop 7.14). Since `locSubring` is bounded
(`locSubring_isBounded`), integrality over a bounded subring gives
power-boundedness (`IsBounded.isPowerBounded_of_isIntegral`).

**Status:** Requires formalizing the adic Nullstellensatz (Prop 7.14).
See `docs/TICKETS-axiom-clean.md`, ticket R4. -/
-- Adic Nullstellensatz (Wedhorn Prop 5.30(4) + 7.14, specialized):
-- Elements with v(x) ≤ 1 at all Spa points are integral over locSubring.
-- Route: rational containment → v(t/D.s) ≤ 1 → integral → isPowerBounded.
-- See docs/TICKETS-axiom-clean.md R4.
private theorem locLift_divByS_isPowerBounded {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (_h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hu_loc : IsUnit (algebraMap A (Localization.Away D'.s) D.s))
    {t : A} (ht : t ∈ D.T)
    (hpb : ∀ t' ∈ D.T, @TopologicalRing.IsPowerBounded (Localization.Away D'.s) _ D'.topology
      (IsLocalization.Away.lift D.s hu_loc (divByS t' D.s))) :
    @TopologicalRing.IsPowerBounded (Localization.Away D'.s) _ D'.topology
      (IsLocalization.Away.lift D.s hu_loc (divByS t D.s)) :=
  hpb t ht

/-- The algebraic restriction map is continuous for Huber rings
(Proposition 8.2 of Wedhorn).

**Proof structure:** The lift factors as `D'.coeRingHom ∘ locLift` where
`locLift : Localization.Away D.s →+* Localization.Away D'.s` uses the unit witness
`IsUnit (algebraMap A (Localization.Away D'.s) D.s)`. Since `D'.coeRingHom`
(the completion embedding) is continuous, it suffices to show `locLift` is continuous
from `D.topology` to `D'.topology`.

By the universal property of the localization topology
(`locTopology_continuous_lift`), this reduces to two conditions:
1. `locLift ∘ algebraMap : A → Loc.Away D'.s` is continuous (proved via the
   pair-of-definition neighborhood basis).
2. Each generator `locLift(t/D.s)` for `t ∈ D.T` is power-bounded in
   `D'.topology` (from `locLift_divByS_isPowerBounded`, which needs the
   adic Nullstellensatz — Wedhorn Prop 7.14, ticket R4). -/
theorem restrictionMapAlg_continuous_of_huber {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpb : ∀ t ∈ D.T, @TopologicalRing.IsPowerBounded (Localization.Away D'.s) _ D'.topology
      (IsLocalization.Away.lift D.s (isUnit_algebraMap_s_of_huber D D' h) (divByS t D.s))) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_of_huber D D' h)) := by
  have hu_loc := isUnit_algebraMap_s_of_huber D D' h
  let locLift : Localization.Away D.s →+* Localization.Away D'.s :=
    IsLocalization.Away.lift D.s hu_loc
  have hfactor : IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_of_huber D D' h) =
      D'.coeRingHom.comp locLift := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    ext a
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, RationalLocData.coeRingHom,
      RationalLocData.canonicalMap, locLift]
  rw [hfactor]
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  have hcoe : @Continuous _ _ D'.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      D'.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D'.uniformSpace
  suffices hlift : @Continuous _ _ D.topology D'.topology locLift from hcoe.comp hlift
  haveI : @NonarchimedeanRing _ _ D'.topology :=
    (locBasis D'.P D'.T D'.s D'.hopen).nonarchimedean
  have hf_alg : @Continuous _ _ _ D'.topology
      (locLift.comp (algebraMap A (Localization.Away D.s))) := by
    have h_eq : locLift.comp (algebraMap A (Localization.Away D.s)) =
        algebraMap A (Localization.Away D'.s) := by
      ext a; simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, locLift]
    rw [show (⇑(locLift.comp (algebraMap A (Localization.Away D.s))) : A → _) =
      ⇑(algebraMap A (Localization.Away D'.s)) from congr_arg _ h_eq]
    apply continuous_of_continuousAt_zero
      (algebraMap A (Localization.Away D'.s)).toAddMonoidHom
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro S hS
    obtain ⟨n, -, hn⟩ :=
      (locBasis D'.P D'.T D'.s D'.hopen).hasBasis_nhds_zero.mem_iff.mp hS
    apply Filter.mem_of_superset (D'.P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial)
    intro a ha
    obtain ⟨⟨b, hb⟩, hbn, hab⟩ := ha
    rw [← hab]
    exact hn ⟨algebraMapD D'.P D'.T D'.s ⟨b, hb⟩,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hbn, rfl⟩
  apply locTopology_continuous_lift D.P D.T D.s D.hopen locLift hf_alg
  intro t ht
  exact locLift_divByS_isPowerBounded D D' h hu_loc ht hpb

/-! ### Restriction maps (Proposition 8.2 of Wedhorn)

For an inclusion `R(T'/s') ⊆ R(T/s)` of rational subsets, there exists a unique
continuous ring homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩` such that `σ ∘ ρ = ρ'`, where
`ρ : A → A⟨T/s⟩` and `ρ' : A → A⟨T'/s'⟩` are the canonical maps (Lemma 8.1).

These restriction maps make the assignment `R(T/s) ↦ A⟨T/s⟩` into a presheaf
on the basis of rational subsets (Proposition 8.2 of Wedhorn). -/

/-- The adic Nullstellensatz hypothesis for the presheaf restriction maps: for any
rational containment `R(D'.T/D'.s) ⊆ R(D.T/D.s)`, each generator `t/D.s`
(for `t ∈ D.T`) maps to a power-bounded element in the D'-localization topology
under the canonical lift `Localization.Away D.s →+* Localization.Away D'.s`.

This is a consequence of Wedhorn Prop 5.30(4) + 7.14 (adic Nullstellensatz):
the rational containment gives `v(t) ≤ v(D.s)` for all relevant continuous
valuations, hence `t/D.s` is integral over the ring of definition, hence
power-bounded.

**Status:** Will be proved as an instance for Tate rings (where the Nullstellensatz
is available). For now, carried as an explicit hypothesis via this class. -/
class HasLocLiftPowerBounded (A : Type*) [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsHuberRing A] : Prop where
  locLift_divByS_isPowerBounded : ∀ (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) (t : A), t ∈ D.T →
    @TopologicalRing.IsPowerBounded (Localization.Away D'.s) _ D'.topology
      (IsLocalization.Away.lift D.s (isUnit_algebraMap_s_of_huber D D' h) (divByS t D.s))

section RestrictionMaps

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- The image of `s` under `A → A⟨T'/s'⟩` is a unit when `R(T'/s') ⊆ R(T/s)`
(Proposition 8.2 of Wedhorn). -/
theorem isUnit_canonicalMap_s (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) :=
  isUnit_canonicalMap_s_of_huber D D' h

/-- The algebraic part of the restriction map via `IsLocalization.Away.lift`. -/
noncomputable def restrictionMapAlg (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  IsLocalization.Away.lift D.s (isUnit_canonicalMap_s D D' h)

/-- The algebraic restriction map is continuous (Proposition 8.2 of Wedhorn).
Requires `[HasLocLiftPowerBounded A]` (the adic Nullstellensatz for power-boundedness
of localization generators). -/
theorem restrictionMapAlg_continuous [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (restrictionMapAlg D D' h) :=
  restrictionMapAlg_continuous_of_huber D D' h
    (fun t ht => HasLocLiftPowerBounded.locLift_divByS_isPowerBounded D D' h t ht)

/-- The restriction map `σ : A⟨T/s⟩ →+* A⟨T'/s'⟩` (Proposition 8.2(1) of Wedhorn). -/
noncomputable def restrictionMapHom [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D →+* presheafValue D' := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI us' : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (restrictionMapAlg D D' h) (restrictionMapAlg_continuous D D' h)

/-- The restriction map `σ : A⟨T/s⟩ → A⟨T'/s'⟩` (Proposition 8.2(1)). -/
noncomputable def restrictionMap [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (_ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D → presheafValue D' :=
  restrictionMapHom D D' ‹_›

/-- The restriction map on the dense image equals the algebraic map. -/
private theorem restrictionMapHom_coe [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
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

/-- Restriction maps compose (presheaf functoriality). -/
theorem restrictionMap_comp [HasLocLiftPowerBounded A] (D D' D'' : RationalLocData A)
    (h₁ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (h₂ : rationalOpen D''.T D''.s ⊆ rationalOpen D'.T D'.s) :
    restrictionMap D' D'' h₂ ∘ restrictionMap D D' h₁ =
      restrictionMap D D'' (h₂.trans h₁) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  letI : UniformSpace (Localization.Away D''.s) := D''.uniformSpace
  letI : IsTopologicalRing (Localization.Away D''.s) := D''.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D''.s) := D''.isUniformAddGroup
  have alg_comp_eq :
      (restrictionMapHom D' D'' h₂).comp (restrictionMapAlg D D' h₁) =
      restrictionMapAlg D D'' (h₂.trans h₁) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    ext r
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq]
    change restrictionMapHom D' D'' h₂ (D'.coeRingHom (algebraMap A _ r)) = D''.canonicalMap r
    change restrictionMapHom D' D'' h₂
      (@UniformSpace.Completion.coeRingHom _ _ D'.uniformSpace
        D'.isTopologicalRing D'.isUniformAddGroup (algebraMap A _ r)) = _
    rw [restrictionMapHom_coe, restrictionMapAlg, IsLocalization.Away.lift_eq]
  ext x
  change (restrictionMapHom D' D'' h₂) ((restrictionMapHom D D' h₁) x) =
    (restrictionMapHom D D'' (h₂.trans h₁)) x
  refine @UniformSpace.Completion.ext' _ D.uniformSpace (presheafValue D'') _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    UniformSpace.Completion.continuous_extension ?_ x
  intro a
  simp only [Function.comp]
  erw [UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (restrictionMapAlg_continuous D D' h₁)),
    UniformSpace.Completion.extension_coe
      (uniformContinuous_addMonoidHom_of_continuous
        (restrictionMapAlg_continuous D D'' (h₂.trans h₁)))]
  exact congr_fun (congrArg DFunLike.coe alg_comp_eq) a

/-- The restriction map for the identity inclusion is the identity. -/
theorem restrictionMap_id [HasLocLiftPowerBounded A] (D : RationalLocData A) :
    restrictionMap D D (le_refl _) = id := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have alg_eq : restrictionMapAlg D D (le_refl _) = D.coeRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    ext r
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
      RationalLocData.coeRingHom, RationalLocData.canonicalMap]
  ext x
  change restrictionMapHom D D (le_refl _) x = x
  refine @UniformSpace.Completion.ext' _ D.uniformSpace (presheafValue D) _ _ _ _
    UniformSpace.Completion.continuous_extension continuous_id ?_ x
  intro a
  simp only [id]
  erw [UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (restrictionMapAlg_continuous D D (le_refl _)))]
  exact congr_fun (congrArg DFunLike.coe alg_eq) a

/-- The restriction map is continuous (Proposition 8.2 of Wedhorn). -/
theorem restrictionMapHom_continuous [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Continuous (restrictionMapHom D D' h) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The restriction map as a `CompleteTopCommRingCat` morphism. -/
noncomputable def restrictionMapMor [HasLocLiftPowerBounded A] (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValueObj D ⟶ presheafValueObj D' :=
  ⟨restrictionMapHom D D' h, restrictionMapHom_continuous D D' h⟩

/-- A *rational covering* of `R(T/s)` (Wedhorn §8.1). -/
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

/-- Topologically nilpotent elements are nilpotent in discrete rings. -/
private theorem isNilpotent_of_isTopologicallyNilpotent_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsNilpotent a := by
  have h0 : ({0} : Set A) ∈ nhds (0 : A) := isOpen_discrete {0} |>.mem_nhds rfl
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha h0)
  exact ⟨N, Set.mem_singleton_iff.mp (hN N le_rfl)⟩

/-- The localization topology is discrete when the base ring is. -/
theorem locTopology_eq_bot_of_discrete {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] (D : RationalLocData A) :
    D.topology = ⊥ := by
  have hI_le : D.P.I ≤ nilradical D.P.A₀ := by
    intro ⟨a, ha⟩ haI
    obtain ⟨n, hn⟩ := isNilpotent_of_isTopologicallyNilpotent_discrete
      (D.P.isTopologicallyNilpotent_of_mem haI)
    exact ⟨n, Subtype.val_injective (by simp only [SubmonoidClass.mk_pow, hn,
      ZeroMemClass.coe_zero])⟩
  obtain ⟨M, hM⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical D.P.fg).mpr hI_le
  have hJ : locIdeal D.P D.T D.s ^ M = ⊥ := by
    rw [locIdeal, ← Ideal.map_pow]
    simp only [hM, Submodule.zero_eq_bot, Ideal.map_bot]
  have hNhd : ∀ x ∈ locNhd D.P D.T D.s M, x = (0 : Localization.Away D.s) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hJ] at hd
    simp only [RingHom.toAddMonoidHom_eq_coe, show d = 0 from hd,
      AddMonoidHom.coe_coe, Subring.subtype_apply, ZeroMemClass.coe_zero]
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI := D.isTopologicalRing
  have hbasis := locBasis D.P D.T D.s D.hopen
  have hopen_nhd : @IsOpen _ D.topology
      ((locNhd D.P D.T D.s M : AddSubgroup (Localization.Away D.s)) : Set _) :=
    (hbasis.openAddSubgroup M).isOpen
  have hNhd_eq : ((locNhd D.P D.T D.s M : AddSubgroup _) : Set (Localization.Away D.s)) =
      {0} := Set.eq_singleton_iff_unique_mem.mpr ⟨zero_mem_locNhd D.P D.T D.s M, hNhd⟩
  apply eq_bot_of_singletons_open
  intro x
  rw [show ({x} : Set (Localization.Away D.s)) = (x + ·) '' {0} from by
    simp only [Set.image_singleton, add_zero]]
  exact (isOpenMap_add_left x) _ (hNhd_eq ▸ hopen_nhd)

/-- For discrete rings, the adic Nullstellensatz hypothesis holds trivially because
the localization topology is `⊥` (discrete), making every element power-bounded. -/
instance HasLocLiftPowerBounded.discrete {A : Type*} [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [PlusSubring A] [IsHuberRing A] : HasLocLiftPowerBounded A where
  locLift_divByS_isPowerBounded D D' _h _t _ht := by
    have hbot : D'.topology = ⊥ := locTopology_eq_bot_of_discrete D'
    show @TopologicalRing.IsBounded _ _ D'.topology
      (Set.range (fun n => (IsLocalization.Away.lift D.s _ (divByS _t D.s)) ^ n))
    rw [hbot]
    intro U hU
    letI : TopologicalSpace (Localization.Away D'.s) := ⊥
    haveI : DiscreteTopology (Localization.Away D'.s) := ⟨rfl⟩
    rw [nhds_discrete, Filter.mem_pure] at hU
    refine ⟨{0}, ?_, ?_⟩
    · rw [nhds_discrete, Filter.mem_pure]; exact rfl
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
      rw [Set.mem_singleton_iff.mp hb, mul_zero]; exact hU

/-! ### Adic Nullstellensatz (Wedhorn Remark 7.24 + Prop 7.18)

The valuative criterion for integrality: if `v(x) ≤ 1` for every continuous
valuation `v` with `v ≤ 1` on a subring `B`, then `x` is integral over `B`.

Equivalently: the integral closure of an open subring `B` equals
`{x : v(x) ≤ 1 for all v ∈ σ(B)}` where `σ(B) = {v ∈ Cont(A) : v ≤ 1 on B}`. -/

/-- **Valuative criterion for integrality** (hard direction of Wedhorn Remark 7.24).
If `x` satisfies `v(x) ≤ 1` for every continuous valuation `v` that is `≤ 1` on
the subring `B`, then `x` is integral over `B`.

The proof constructs a valuation dominating the localization `B[x]_m` where `m`
is chosen to avoid powers of `x`. See [Hu2] Lemma 3.3.

This is the deepest ingredient of the adic Nullstellensatz. -/
theorem isIntegral_of_forall_valuation_le_one
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsDomain R]
    {B : Subring R} (hB_open : IsOpen (B : Set R))
    (x : R)
    (hvle : ∀ (v : ValuativeRel R), (∀ b ∈ B, v.vle b 1) → v.vle x 1) :
    IsIntegral B x := by
  -- Proof by contraposition using the field-level Mathlib API
  -- (Wedhorn Prop 7.18 / [Hu2] Lemma 3.3).
  by_contra hni
  -- Pass to fraction field; ι = algebraMap R (FractionRing R)
  let ι := algebraMap R (FractionRing R)
  have hι_inj : Function.Injective ι := IsFractionRing.injective R (FractionRing R)
  -- Step 1: ι x is not integral over B in FractionRing R
  have hni_K : ¬ IsIntegral B (ι x) :=
    mt (isIntegral_algebraMap_iff hι_inj).mp hni
  -- Step 2: ι x ∉ (integralClosure B (FractionRing R)).toSubring
  have hx_notin : ι x ∉ (integralClosure B (FractionRing R)).toSubring := by
    rwa [Subalgebra.mem_toSubring, mem_integralClosure_iff]
  -- Step 3: ∃ V with integralClosure ≤ V and ι x ∉ V (Stacks 090P(1))
  obtain ⟨V, hV_le, hx_notV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx_notin
  -- Step 4: Construct ValuativeRel on R by pulling V.valuation back along ι
  let w := ValuativeRel.ofValuation (V.valuation.comap ι)
  -- Step 5: w.vle b 1 for all b ∈ B (elements of B land in integralClosure ≤ V)
  have hw_B : ∀ b ∈ B, w.vle b 1 := by
    intro b hb
    show V.valuation (ι b) ≤ V.valuation (ι 1)
    simp only [map_one, ValuationSubring.valuation_le_one_iff]
    exact hV_le (Subalgebra.algebraMap_mem (integralClosure B (FractionRing R)) ⟨b, hb⟩)
  -- Step 6: hvle gives w.vle x 1, i.e. V.valuation (ι x) ≤ V.valuation (ι 1) = 1
  have hw_x : w.vle x 1 := hvle w hw_B
  -- Step 7: So ι x ∈ V, contradicting hx_notV
  apply hx_notV; rw [← V.valuation_le_one_iff]
  have : V.valuation (ι x) ≤ V.valuation (ι 1) := hw_x
  simpa only [map_one] using this

/-- **Topology-aware valuative criterion for integrality (Wedhorn Proposition 7.18).**
Let `R` be a topological integral domain with a pair of definition `P` and `B` a
subring of `R` containing the ring of definition `P.A₀`. If `v(x) ≤ 1` for every
**continuous** valuation `v` on `R` with `v(b) ≤ 1` for all `b ∈ B`, then `x` is
integral over `B`.

This strengthens `isIntegral_of_forall_valuation_le_one` by restricting the hypothesis
to *continuous* valuations only. See Wedhorn Prop 7.18 / [Hu2, Lemma 3.3].

**Proof outline (following Wedhorn):**
1. Contrapositive: assume `x` is not integral over `B`.
2. Apply the field-level `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`
   (Stacks 090P) to get a valuation subring `V ⊆ Frac(R)` with `B ⊆ V` (image) and
   `ι x ∉ V`.
3. Construct `w := ValuativeRel.ofValuation (V.valuation.comap ι)` on `R`.
4. Verify `w(b) ≤ 1` for `b ∈ B` (trivial from `B ⊆ V`).
5. **Key step (Wedhorn 7.22):** Show `w` is continuous on `R`. For this, we use
   `Valuation.isContinuous_of_le_one_and_pow_cofinal` with `P.A₀` as the ring of
   definition. We need:
   (a) `V.valuation.comap ι ≤ 1` on `P.A₀` — holds since `P.A₀ ⊆ B ⊆ V` (image).
   (b) Some generator `g < 1` bounds `V.valuation` on `P.I`.
   (c) `g^n` is cofinal in `V.ValueGroup`.
   Conditions (b), (c) require the valuation subring `V` to be chosen carefully so
   that its maximal ideal contains the image of `P.I`. This is the content of
   Wedhorn Lemma 7.22.
6. Apply the hypothesis `hvle` to get `w.vle x 1`.
7. Contradict `ι x ∉ V`.

**Status:** The continuity step (5) requires Wedhorn Lemma 7.22 / [Hu2] Lemma 3.3,
which is the deepest ingredient of the adic Nullstellensatz. The rest of the proof
is straightforward. The single remaining sorry is isolated to the continuity step.

See `docs/plans/2026-04-08-wedhorn-7-10-plan.md` for the detailed plan. -/
theorem isIntegral_of_forall_continuous_valuation_le_one
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsDomain R]
    (P : PairOfDefinition R)
    {B : Subring R} (_hB_open : IsOpen (B : Set R))
    (hA₀B : (P.A₀ : Set R) ⊆ B)
    (x : R)
    (hvle : ∀ (v : ValuativeRel R),
      (⟨v⟩ : Spv R).IsContinuous →
      (∀ b ∈ B, v.vle b 1) → v.vle x 1) :
    IsIntegral B x := by
  -- Proof by contraposition.
  by_contra hni
  -- Pass to fraction field.
  let ι := algebraMap R (FractionRing R)
  have hι_inj : Function.Injective ι := IsFractionRing.injective R (FractionRing R)
  -- Step 1: ι x is not integral over B in Frac(R).
  have hni_K : ¬ IsIntegral B (ι x) :=
    mt (isIntegral_algebraMap_iff hι_inj).mp hni
  have hx_notin : ι x ∉ (integralClosure B (FractionRing R)).toSubring := by
    rwa [Subalgebra.mem_toSubring, mem_integralClosure_iff]
  -- Step 2: Stacks 090P gives V ⊇ integralClosure(B), x ∉ V.
  obtain ⟨V, hV_le, hx_notV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx_notin
  -- Step 3: Construct the comap valuation w on R.
  let wVal : Valuation R V.ValueGroup := V.valuation.comap ι
  let w : ValuativeRel R := ValuativeRel.ofValuation wVal
  -- Step 4: w ≤ 1 on B (elements of B land in V via integralClosure).
  have hw_B : ∀ b ∈ B, w.vle b 1 := by
    intro b hb
    show V.valuation (ι b) ≤ V.valuation (ι 1)
    simp only [map_one, ValuationSubring.valuation_le_one_iff]
    exact hV_le (Subalgebra.algebraMap_mem (integralClosure B (FractionRing R)) ⟨b, hb⟩)
  -- Derived facts for continuity:
  -- wVal ≤ 1 on P.A₀ (since P.A₀ ⊆ B ⊆ V image).
  have hwVal_le_A₀ : ∀ (a : P.A₀), wVal (P.A₀.subtype a) ≤ 1 := by
    intro a
    show V.valuation (ι ((a : R))) ≤ 1
    rw [ValuationSubring.valuation_le_one_iff]
    exact hV_le (Subalgebra.algebraMap_mem (integralClosure B (FractionRing R))
      ⟨(a : R), hA₀B a.property⟩)
  -- Step 5: **KEY GAP (Wedhorn 7.22).**
  -- We need wVal (= V.valuation.comap ι) to be continuous on R.
  -- By `Valuation.isContinuous_of_le_one_and_pow_cofinal`, it suffices to find
  -- `g < 1` in `V.ValueGroup` with `wVal ≤ g` on `P.I` and `g^n` cofinal.
  -- Finding such `g` requires refining V so that its maximal ideal contains
  -- the image of P.I — this is Wedhorn Lemma 7.22.
  have hwVal_cont : wVal.IsContinuous := by
    sorry -- Wedhorn 7.22 / [Hu2] Lemma 3.3: requires V refined with I ⊆ maxIdeal(V)
  have hw_cont : (⟨w⟩ : Spv R).IsContinuous :=
    isContinuous_ofValuation_of wVal hwVal_cont
  -- Step 6: Apply the topology-aware hypothesis.
  have hw_x : w.vle x 1 := hvle w hw_cont hw_B
  -- Step 7: Derive contradiction with x ∉ V.
  apply hx_notV
  rw [← V.valuation_le_one_iff]
  have : V.valuation (ι x) ≤ V.valuation (ι 1) := hw_x
  simpa only [map_one] using this

/-- A `ValuativeRel` that is `≤ 1` on an open subring of `Localization.Away s` yields
a `Spv` point for which `algebraMap t ≤ᵥ algebraMap s` for `t ∈ T`, by the
pattern of `vle_of_locSubring_bounded` adapted to `ValuativeRel`. -/
private theorem comap_algebraMap_vle_of_locSubring {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (_hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (v : ValuativeRel (Localization.Away s))
    (hv_sub : ∀ b ∈ locSubring P T s, v.vle b 1)
    {t : A} (ht : t ∈ T) :
    v.vle (algebraMap A (Localization.Away s) t)
      (algebraMap A (Localization.Away s) s) := by
  -- divByS t s ∈ locSubring, so v(divByS t s) ≤ 1
  have hle : v.vle (divByS t s) 1 := hv_sub _ (divByS_mem_locSubring P T s ht)
  -- divByS t s * algebraMap s = algebraMap t
  have hspec : divByS t s * algebraMap A (Localization.Away s) s =
      algebraMap A (Localization.Away s) t :=
    IsLocalization.mk'_spec _ t ⟨s, Submonoid.mem_powers s⟩
  -- v(divByS t s * algebraMap s) ≤ v(1 * algebraMap s) = v(algebraMap s)
  have hmul := v.mul_vle_mul_left hle (algebraMap A (Localization.Away s) s)
  rwa [one_mul, hspec] at hmul

/-- **Rational containment at Spa points (Wedhorn §8.1).**

Given rational data `D, D'` with `R(D'.T/D'.s) ⊆ R(D.T/D.s)`, a valuation `v` on
`Localization.Away D'.s` that is `≤ 1` on `locSubring`, and a hypothesis that the
comap valuation `w := v.comap (algebraMap A _)` on `A` is continuous, we conclude
`v(lift(t/D.s)) ≤ 1` for `t ∈ D.T`.

The continuity hypothesis on `w` (rather than a universal statement about `v ≤ 1
on A₀ → continuous`) is the key correction for non-discrete rings: the false
universal statement fails for the trivial valuation, but the specific comap `w`
appearing in our application can be made continuous via `comap_isContinuous`
when `v` itself is continuous on the localization.

**Proof strategy.** Since `w` is continuous and `w ≤ 1` on `A⁺` (by `hAplus_le_A₀`
and `hv_sub`), we have `⟨w⟩ ∈ Spa A A⁺`. Combined with the rational-open conditions
derived from `hv_sub`, we get `⟨w⟩ ∈ rationalOpen D'.T D'.s`. Rational containment
`h` lifts this to `⟨w⟩ ∈ rationalOpen D.T D.s`, giving `w(t) ≤ w(D.s)` for
`t ∈ D.T`. Unfolding `w` and cancelling the unit `algebraMap(D.s)` yields the
conclusion. -/
theorem locLift_vle_one_at_spa {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D'.P.A₀)
    {t : A} (ht : t ∈ D.T)
    (v : ValuativeRel (Localization.Away D'.s))
    (hv_sub : ∀ b ∈ locSubring D'.P D'.T D'.s, v.vle b 1)
    (hw_cont : (⟨ValuativeRel.comap
      (algebraMap A (Localization.Away D'.s)) v⟩ : Spv A).IsContinuous) :
    v.vle (IsLocalization.Away.lift D.s (isUnit_algebraMap_s_of_huber D D' h)
      (divByS t D.s)) 1 := by
  -- Step 1: Key identity — lift(divByS t D.s) * algebraMap(D.s) = algebraMap(t)
  -- in Localization.Away D'.s.
  have hu := isUnit_algebraMap_s_of_huber D D' h
  let locLift : Localization.Away D.s →+* Localization.Away D'.s :=
    IsLocalization.Away.lift D.s hu
  -- Key identity: locLift(divByS t D.s) * algebraMap(D.s) = algebraMap(t)
  have hspec : locLift (divByS t D.s) * algebraMap A (Localization.Away D'.s) D.s =
      algebraMap A (Localization.Away D'.s) t := by
    -- divByS t D.s * algebraMap(D.s) = algebraMap(t) in Localization.Away D.s
    have h_src : divByS t D.s * algebraMap A (Localization.Away D.s) D.s =
        algebraMap A (Localization.Away D.s) t :=
      IsLocalization.mk'_spec _ t ⟨D.s, Submonoid.mem_powers D.s⟩
    -- Apply locLift (a ring hom) to both sides
    have h2 := congr_arg locLift h_src
    rw [map_mul] at h2
    -- h2 : locLift(divByS t D.s) * locLift(algebraMap D.s) = locLift(algebraMap t)
    -- Use lift_eq: locLift(algebraMap a) = algebraMap a
    have h_eq_s : locLift (algebraMap A (Localization.Away D.s) D.s) =
        algebraMap A (Localization.Away D'.s) D.s :=
      IsLocalization.Away.lift_eq D.s hu D.s
    have h_eq_t : locLift (algebraMap A (Localization.Away D.s) t) =
        algebraMap A (Localization.Away D'.s) t :=
      IsLocalization.Away.lift_eq D.s hu t
    rw [h_eq_s, h_eq_t] at h2
    exact h2
  -- Step 2: Construct the pullback valuation w on A
  set w : ValuativeRel A :=
    ValuativeRel.comap (algebraMap A (Localization.Away D'.s)) v
  -- Step 3: Show w satisfies rational-open conditions for D'.T/D'.s
  -- w.vle t' D'.s for t' ∈ D'.T
  have hw_rat : ∀ t' ∈ D'.T, w.vle t' D'.s := by
    intro t' ht'
    show v.vle (algebraMap A _ t') (algebraMap A _ D'.s)
    exact comap_algebraMap_vle_of_locSubring D'.P D'.T D'.s D'.hopen v hv_sub ht'
  -- ¬ w.vle D'.s 0
  have hw_nz : ¬ w.vle D'.s 0 := by
    show ¬ v.vle (algebraMap A _ D'.s) (algebraMap A _ 0)
    rw [map_zero]
    exact ValuativeRel.not_vle_zero_of_isUnit
      (IsLocalization.map_units (Localization.Away D'.s)
        ⟨D'.s, Submonoid.mem_powers D'.s⟩)
  -- w.vle a 1 for a ∈ A₀ (and hence for a ∈ A⁺ since A⁺ ⊆ A₀ for affinoid)
  have hw_A₀ : ∀ a ∈ D'.P.A₀, w.vle a 1 := by
    intro a ha
    show v.vle (algebraMap A _ a) (algebraMap A _ 1)
    rw [map_one]
    exact hv_sub _ (algebraMap_mem_locSubring D'.P D'.T D'.s ha)
  -- Step 4: Show ⟨w⟩ ∈ rationalOpen D'.T D'.s (needs Spa membership, i.e. continuity)
  -- Construct Spv point
  let wSpv : Spv A := ⟨w⟩
  -- Step 4a: Show wSpv ∈ Spa A A⁺ — this requires w.IsContinuous and w ≤ 1 on A⁺
  -- We use: v ≤ 1 on locSubring (an open subring), so pulled-back v is continuous
  -- by Wedhorn Lemma 7.22.
  -- For now, we establish the key conclusion directly:
  -- Step 5: Use rational containment to get w.vle t D.s
  -- From h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s
  -- and wSpv ∈ rationalOpen D'.T D'.s, we get wSpv ∈ rationalOpen D.T D.s
  -- i.e., w.vle t D.s.
  -- Step 5': w.vle t D.s means v.vle (algebraMap t) (algebraMap D.s)
  suffices hkey : v.vle (algebraMap A (Localization.Away D'.s) t)
      (algebraMap A (Localization.Away D'.s) D.s) by
    -- Step 6: Cancel the unit algebraMap(D.s) using vle_mul_cancel
    -- From hspec: f(divByS t D.s) * algebraMap(D.s) = algebraMap(t)
    -- So v.vle (f(divByS t D.s) * algebraMap D.s) (1 * algebraMap D.s)
    -- By vle_mul_cancel (with ¬ v.vle (algebraMap D.s) 0): v.vle (f(divByS t D.s)) 1
    have hDsUnit : ¬ v.vle (algebraMap A (Localization.Away D'.s) D.s) 0 :=
      ValuativeRel.not_vle_zero_of_isUnit hu
    apply v.vle_mul_cancel hDsUnit
    rw [hspec, one_mul]
    exact hkey
  -- Step 5: Prove v.vle (algebraMap t) (algebraMap D.s) via Spv pullback.
  -- Show wSpv ∈ rationalOpen D'.T D'.s
  have hw_mem_rat : wSpv ∈ rationalOpen D'.T D'.s := by
    refine ⟨⟨?_, fun f hf ↦ ?_⟩, hw_rat, hw_nz⟩
    · -- wSpv.IsContinuous: from hw_cont hypothesis.
      exact hw_cont
    · -- w.vle f 1 for f ∈ A⁺: from hAplus_le_A₀ + hw_A₀.
      exact hw_A₀ f (hAplus_le_A₀ hf)
  -- Use rational containment: wSpv ∈ rationalOpen D.T D.s
  have hw_mem_D := h hw_mem_rat
  -- Extract w.vle t D.s from hw_mem_D
  exact hw_mem_D.2.1 t ht

-- The HasLocLiftPowerBounded.tate instance is in PresheafIdentification.lean
-- (needs locSubring_isBounded which is defined there).
-- It combines isIntegral_of_forall_valuation_le_one + locLift_vle_one_at_spa
-- + isPowerBounded_of_isIntegral + locSubring_isBounded.

/-- Given a prime `p` containing `D.s` but not `D'.s`, construct a point in `rationalOpen D'.T D'.s`
whose support is `p`, contradicting `rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s`. -/
private theorem mem_prime_of_rational_subset_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime)
    (hDs : D.s ∈ p) : D'.s ∈ p := by
  classical
  by_contra hD's
  haveI := hp
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) (WithZero (Multiplicative ℤ))).comap φ
  let v := ofValuation w
  have hv_spa : v ∈ Spa A A⁺ := by
    refine ⟨?_, ?_⟩
    · apply isContinuous_ofValuation_of; intro γ; exact isOpen_discrete _
    · intro f hf; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_supp : v.supp = p := by
    rw [supp_ofValuation]; ext a
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply, φ, RingHom.comp_apply,
      Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun ha ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]; rfl⟩
  have hw_Ds : w D'.s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero
    intro heq
    apply hD's
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hv_rat : v ∈ rationalOpen D'.T D'.s := by
    refine ⟨hv_spa, ?_, ?_⟩
    · intro t' _
      change w t' ≤ w D'.s
      rw [hw_Ds]
      simp only [w, Valuation.comap_apply]
      exact Valuation.one_apply_le_one _
    · change ¬ (w D'.s ≤ w 0)
      simp only [hw_Ds, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]
  exact (h hv_rat).2.2 ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs))

/-- The image of `s` under `A → A⟨T'/s'⟩` is a unit when `R(T'/s') ⊆ R(T/s)`
(Proposition 8.2 of Wedhorn, discrete case). -/
theorem isUnit_canonicalMap_s_of_discrete {A : Type*} [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] [PlusSubring A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  suffices hu : IsUnit (algebraMap A (Localization.Away D'.s) D.s) by
    change IsUnit (D'.coeRingHom (algebraMap A (Localization.Away D'.s) D.s))
    exact hu.map D'.coeRingHom
  have hrad : D'.s ∈ Ideal.radical (Ideal.span {D.s}) := by
    classical
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p ⟨hsp, hp⟩
    have hDs : D.s ∈ p := hsp (Ideal.subset_span (Set.mem_singleton D.s))
    exact mem_prime_of_rational_subset_discrete D D' h p hp hDs
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  have hunit_pow : IsUnit (algebraMap A (Localization.Away D'.s) D'.s ^ n) :=
    (IsLocalization.map_units (Localization.Away D'.s)
      (⟨D'.s, ⟨1, pow_one D'.s⟩⟩ : Submonoid.powers D'.s)).pow n
  have heq : algebraMap A (Localization.Away D'.s) a *
      algebraMap A (Localization.Away D'.s) D.s =
      algebraMap A (Localization.Away D'.s) D'.s ^ n := by
    rw [← map_mul, ← map_pow, ha]
  rw [← heq] at hunit_pow
  exact isUnit_of_mul_isUnit_right hunit_pow

/-- The algebraic restriction map is continuous for discrete rings
(Proposition 8.2 of Wedhorn, discrete case). -/
theorem restrictionMapAlg_continuous_of_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] [PlusSubring A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_of_discrete D D' h)) :=
  locTopology_eq_bot_of_discrete D ▸ continuous_bot

/-- The completion embedding is bijective for discrete rings. -/
theorem coeRingHom_bijective_of_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    (D : RationalLocData A) :
    Function.Bijective D.coeRingHom := by
  have htop : D.topology = ⊥ := locTopology_eq_bot_of_discrete D
  have hbot : D.uniformSpace = ⊥ := by
    suffices h : D.uniformSpace.uniformity = Filter.principal SetRel.id by
      exact UniformSpace.ext (h.trans bot_uniformity.symm)
    change Filter.comap (fun p : Localization.Away D.s × Localization.Away D.s ↦
      p.2 - p.1) (@nhds (Localization.Away D.s) D.topology 0) = Filter.principal SetRel.id
    have hpure : @nhds (Localization.Away D.s) D.topology 0 = pure 0 := by
      rw [htop]
      letI : TopologicalSpace (Localization.Away D.s) := ⊥
      haveI : DiscreteTopology (Localization.Away D.s) := ⟨rfl⟩
      exact congr_fun (nhds_discrete _) 0
    rw [hpure, Filter.comap_pure]
    ext s
    simp only [Filter.mem_principal]
    constructor
    · intro h ⟨a, b⟩ (hab : a = b); exact h (show b - a = 0 by rw [hab, sub_self])
    · intro h ⟨a, b⟩ (hab : b - a = 0); exact h (sub_eq_zero.mp hab).symm
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : DiscreteUniformity (Localization.Away D.s) := ⟨hbot⟩
  constructor
  · exact UniformSpace.Completion.coe_injective _
  · have hclosed := (UniformSpace.Completion.isUniformEmbedding_coe
      (Localization.Away D.s)).isClosedEmbedding.isClosed_range
    have hdense := UniformSpace.Completion.denseRange_coe (α := Localization.Away D.s)
    intro x
    have : x ∈ Set.range ((↑) : Localization.Away D.s →
        UniformSpace.Completion (Localization.Away D.s)) := by
      rw [← hclosed.closure_eq]
      exact hdense.closure_range ▸ Set.mem_univ x
    exact this

/-- The algebraMap image of `z` in each cover piece is zero, lifted through the
localization map (helper for `productRestriction_injective_discrete`). -/
private theorem lift_map_zero_of_restrictionAlg_zero {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A]
    (C : RationalCovering A) (z : Localization.Away C.base.s)
    (hz_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) z = 0)
    (hs_unit : ∀ (D' : RationalLocData A), D' ∈ C.covers →
      IsUnit (algebraMap A (Localization.Away D'.s) C.base.s))
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    (IsLocalization.Away.lift C.base.s (hs_unit D hD) :
      Localization.Away C.base.s →+* Localization.Away D.s) z = 0 := by
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

/-- If the lift of `z` to each cover piece is zero, then the numerator `a` of `z = a / s^m`
maps to zero in each cover piece (helper for `productRestriction_injective_discrete`). -/
private theorem algebraMap_numerator_zero {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    (C : RationalCovering A) (z : Localization.Away C.base.s) (a : A) (m : ℕ)
    (hs_unit : ∀ (D' : RationalLocData A), D' ∈ C.covers →
      IsUnit (algebraMap A (Localization.Away D'.s) C.base.s))
    (hz_eq : z = IsLocalization.mk' (Localization.Away C.base.s) a
      (⟨C.base.s ^ m, m, rfl⟩ : Submonoid.powers C.base.s))
    (hz_alg_zero : ∀ (D' : RationalLocData A) (hD' : D' ∈ C.covers),
      (IsLocalization.Away.lift C.base.s (hs_unit D' hD') :
        Localization.Away C.base.s →+* Localization.Away D'.s) z = 0)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    algebraMap A (Localization.Away D.s) a = 0 := by
  have h := hz_alg_zero D hD
  have hza : z * algebraMap A (Localization.Away C.base.s) (C.base.s ^ m) =
      algebraMap A (Localization.Away C.base.s) a := by
    rw [hz_eq]; exact IsLocalization.mk'_spec _ _ _
  have hga := congr_arg (IsLocalization.Away.lift (S := Localization.Away C.base.s)
    C.base.s (hs_unit D hD)) hza
  simp only [map_mul, IsLocalization.Away.lift_eq] at hga
  rw [h, zero_mul] at hga
  exact hga.symm

/-- An element annihilated in every cover piece lies in the radical of the annihilator,
using a trivial valuation argument (helper for `productRestriction_injective_discrete`). -/
private theorem base_s_mem_annihilator_radical {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    (C : RationalCovering A) (a : A)
    (ha_ann : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∃ k : ℕ, D.s ^ k * a = 0) :
    C.base.s ∈ (Ideal.span ({b : A | b * a = 0} : Set A)).radical := by
  classical
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro p ⟨hp_ann, hp_prime⟩
  haveI := hp_prime
  by_contra hs_notin
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
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun hb ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]; rfl⟩
  have hw_s : w C.base.s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero; intro heq; apply hs_notin
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hv_rat : v ∈ rationalOpen C.base.T C.base.s :=
    ⟨hv_spa,
      fun t _ ↦ by
        change w t ≤ w C.base.s; rw [hw_s]
        simp only [w, Valuation.comap_apply]
        exact Valuation.one_apply_le_one _,
      by change ¬ (w C.base.s ≤ w 0)
         simp only [hw_s, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]⟩
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  have hDs_notin : D.s ∉ p := fun hDs ↦
    hv_D.2.2 ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs))
  obtain ⟨k, hk⟩ := ha_ann D hD
  exact hDs_notin (Ideal.IsPrime.mem_of_pow_mem hp_prime k
    (hp_ann (Ideal.subset_span hk)))

/-- Product restriction is injective for discrete rings (Theorem 8.28(c)). -/
theorem productRestriction_injective_discrete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A]
    (C : RationalCovering A) :
    Function.Injective (fun x : presheafValue C.base ↦
      fun (D : C.covers) ↦ restrictionMap C.base D (C.hsubset D D.prop) x) := by
  have hbij_base := coeRingHom_bijective_of_discrete C.base
  intro x y hxy
  obtain ⟨x', rfl⟩ := hbij_base.2 x
  obtain ⟨y', rfl⟩ := hbij_base.2 y
  suffices h : x' = y' by rw [h]
  have hmap_eq : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) x' =
      restrictionMapAlg C.base D (C.hsubset D hD) y' := by
    intro D hD
    have h := congr_fun hxy ⟨D, hD⟩
    simp only at h
    have hx := restrictionMapHom_coe C.base D (C.hsubset D hD) x'
    have hy := restrictionMapHom_coe C.base D (C.hsubset D hD) y'
    rwa [hx.symm, hy.symm]
  rw [← sub_eq_zero]
  set z := x' - y'
  have hz_zero : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) z = 0 := by
    intro D hD
    have := hmap_eq D hD
    simp only [z, map_sub, sub_eq_zero] at this ⊢
    exact this
  have hs_unit : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      IsUnit (algebraMap A (Localization.Away D.s) C.base.s) := by
    intro D hD
    have hu := isUnit_canonicalMap_s C.base D (C.hsubset D hD)
    change IsUnit (D.coeRingHom (algebraMap A _ C.base.s)) at hu
    let e := RingEquiv.ofBijective D.coeRingHom (coeRingHom_bijective_of_discrete D)
    exact (MulEquiv.isUnit_map (f := e.toMulEquiv) (x := algebraMap A _ C.base.s)).mp hu
  have hz_alg_zero := lift_map_zero_of_restrictionAlg_zero C z hz_zero hs_unit
  obtain ⟨a, ⟨_, ⟨m, rfl⟩⟩, hz_eq⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers C.base.s) z
  have ha_zero := algebraMap_numerator_zero C z a m hs_unit hz_eq.symm hz_alg_zero
  have ha_ann : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      ∃ k : ℕ, D.s ^ k * a = 0 := by
    intro D hD
    have h := ha_zero D hD
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers D.s)] at h
    obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := h
    exact ⟨k, hk⟩
  suffices hs_rad : C.base.s ∈
      (Ideal.span ({b : A | b * a = 0} : Set A)).radical by
    obtain ⟨M, hM⟩ := Ideal.mem_radical_iff.mp hs_rad
    have : C.base.s ^ M * a = 0 := by
      suffices ∀ (x : A) (_ : x ∈ Ideal.span ({b : A | b * a = 0} : Set A)),
          x * a = 0 by
        exact this _ hM
      intro x hx
      induction hx using Submodule.span_induction with
      | mem b hb => exact hb
      | zero => exact zero_mul a
      | add x y _ _ hxa hya => rw [add_mul, hxa, hya, add_zero]
      | smul c x _ hxa => rw [smul_eq_mul, mul_assoc, hxa, mul_zero]
    rw [← hz_eq, IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨C.base.s ^ M, ⟨M, rfl⟩⟩, this⟩
  exact base_s_mem_annihilator_radical C a ha_ann

end RestrictionMaps

end ValuationSpectrum
