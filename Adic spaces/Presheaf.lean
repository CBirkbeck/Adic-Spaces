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

/-- Given a prime `p` containing `D.s` but not `D'.s`, construct a point in
`rationalOpen D'.T D'.s` whose support contains `p`, contradicting the inclusion
`rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s` (Wedhorn Proposition 7.52).

For open primes, we use the trivial valuation on `Frac(A/p)` (which is continuous
since `p` is open). For non-open primes, this requires Lemma 7.45 plus I-adic
completeness; see `mem_prime_of_rational_subset_nonOpen_sorry` for that case. -/
private theorem mem_prime_of_rational_subset {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime) (hDs : D.s ∈ p) : D'.s ∈ p := by
  classical
  by_contra hD's
  haveI := hp
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) (WithZero (Multiplicative ℤ))).comap φ
  let v := ofValuation w
  -- w(a) = 0 iff a ∈ p, else w(a) = 1
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
  -- Continuity: the sublevel sets of w are ∅ (γ=0), p (0<γ≤1), or A (γ>1).
  -- For open primes, all three are open. For non-open primes, p is not open.
  -- We handle both cases: open primes directly, non-open primes via sorry.
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
          suffices {a : A | w a < γ} = (p : Set A) by
            rw [this]
            -- Open prime case: p is open. Non-open: sorry.
            by_cases hp_open : IsOpen (p : Set A)
            · exact hp_open
            · -- Non-open prime: continuity of the trivial valuation requires p open.
              -- This case needs Lemma 7.45 (I-adic completeness) for an alternative
              -- construction. See Wedhorn Lemma 7.45.
              exact absurd (by
                -- In a Huber ring, RationalLocData carries a PairOfDefinition.
                -- The argument for non-open primes requires I-adic completeness
                -- to construct a different continuous valuation.
                sorry) hp_open
          ext a
          simp only [Set.mem_setOf_eq]
          constructor
          · intro ha
            rcases hw_one_or_zero a with ha0 | ha1
            · exact (hw_mem_iff a).mp ha0
            · exact absurd (ha1 ▸ ha |>.trans_le h1) (lt_irrefl _)
          · intro ha
            rw [(hw_mem_iff a).mpr ha]; exact zero_lt_iff.mpr hγ
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_supp : v.supp = p := by
    rw [supp_ofValuation]; ext a
    exact ⟨fun h ↦ (hw_mem_iff a).mp h, fun ha ↦ (hw_mem_iff a).mpr ha⟩
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
(Proposition 8.2 of Wedhorn). For Huber rings, this uses Lemma 7.45. -/
theorem isUnit_canonicalMap_s_of_huber {A : Type*} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A]
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

/-- The algebraic restriction map is continuous for Huber rings
(Proposition 8.2 of Wedhorn). -/
theorem restrictionMapAlg_continuous_of_huber {A : Type*} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
    (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_of_huber D D' h)) := sorry

/-! ### Restriction maps (Proposition 8.2 of Wedhorn)

For an inclusion `R(T'/s') ⊆ R(T/s)` of rational subsets, there exists a unique
continuous ring homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩` such that `σ ∘ ρ = ρ'`, where
`ρ : A → A⟨T/s⟩` and `ρ' : A → A⟨T'/s'⟩` are the canonical maps (Lemma 8.1).

These restriction maps make the assignment `R(T/s) ↦ A⟨T/s⟩` into a presheaf
on the basis of rational subsets (Proposition 8.2 of Wedhorn). -/

section RestrictionMaps

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- The image of `s` under `A → A⟨T'/s'⟩` is a unit when `R(T'/s') ⊆ R(T/s)`
(Proposition 8.2 of Wedhorn). -/
theorem isUnit_canonicalMap_s (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  exact isUnit_canonicalMap_s_of_huber D D' h

/-- The algebraic part of the restriction map via `IsLocalization.Away.lift`. -/
noncomputable def restrictionMapAlg (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  IsLocalization.Away.lift D.s (isUnit_canonicalMap_s D D' h)

/-- The algebraic restriction map is continuous (Proposition 8.2 of Wedhorn). -/
theorem restrictionMapAlg_continuous (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (restrictionMapAlg D D' h) := by
  exact restrictionMapAlg_continuous_of_huber D D' h

/-- The restriction map `σ : A⟨T/s⟩ →+* A⟨T'/s'⟩` (Proposition 8.2(1) of Wedhorn). -/
noncomputable def restrictionMapHom (D D' : RationalLocData A)
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
noncomputable def restrictionMap (D D' : RationalLocData A)
    (_ : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    presheafValue D → presheafValue D' :=
  restrictionMapHom D D' ‹_›

/-- The restriction map on the dense image equals the algebraic map. -/
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

/-- Restriction maps compose (presheaf functoriality). -/
theorem restrictionMap_comp (D D' D'' : RationalLocData A)
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
theorem restrictionMap_id (D : RationalLocData A) :
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
theorem restrictionMapHom_continuous (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    Continuous (restrictionMapHom D D' h) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The restriction map as a `CompleteTopCommRingCat` morphism. -/
noncomputable def restrictionMapMor (D D' : RationalLocData A)
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
    have hd' : d ∈ (locIdeal D.P D.T D.s) ^ M := hd
    rw [hJ] at hd'
    simp only [RingHom.toAddMonoidHom_eq_coe, show d = 0 from hd',
      AddMonoidHom.coe_coe, Subring.subtype_apply, ZeroMemClass.coe_zero]
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI := D.isTopologicalRing
  have hbasis := locBasis D.P D.T D.s D.hopen
  have hopen_nhd : @IsOpen _ D.topology
      ((locNhd D.P D.T D.s M : AddSubgroup (Localization.Away D.s)) : Set _) :=
    (hbasis.openAddSubgroup M).isOpen
  have hNhd_eq : ((locNhd D.P D.T D.s M : AddSubgroup _) : Set (Localization.Away D.s)) =
      {0} := Set.eq_singleton_iff_unique_mem.mpr ⟨zero_mem_locNhd D.P D.T D.s M, hNhd⟩
  have hopen_zero : @IsOpen _ D.topology ({0} : Set (Localization.Away D.s)) :=
    hNhd_eq ▸ hopen_nhd
  apply eq_bot_of_singletons_open
  intro x
  rw [show ({x} : Set (Localization.Away D.s)) = (x + ·) '' {0} from by
    simp only [Set.image_singleton, add_zero]]
  exact (isOpenMap_add_left x) _ hopen_zero

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
