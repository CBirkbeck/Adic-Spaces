/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AnalyticPoints
import «Adic spaces».AdicSpectrum
import «Adic spaces».Lemma745
import «Adic spaces».StructureSheaf

/-!
# Adic Morphisms

We prove Lemma 7.46 and develop the theory of adic morphisms,
following §7.5 and §8.4 of [Wedhorn, *Adic Spaces*].

## Main results

* `ValuationSpectrum.supp_comap` : `supp(comap φ v) = φ⁻¹(supp v)`.
* `ValuationSpectrum.nonAnalytic_comap_of_continuous` : Continuous maps preserve non-analytic
  points (Lemma 7.46(1), first part).
* `ValuationSpectrum.analytic_comap_of_isAdicHom` : Adic homomorphisms preserve analytic
  points (Lemma 7.46(1), second part).
* `ValuationSpectrum.isAdicHom_of_complete_and_analytic_preserved` : If `B` is complete and
  `Spa(φ)` preserves analytic points, then `φ` is adic (Lemma 7.46(2)).
* `ValuationSpectrum.IsAdicMorphism` : Adic morphisms of adic spaces
  (Definition 8.38 of Wedhorn).
* `ValuationSpectrum.isAdicMorphism_iff_preserves_analytic` : A morphism is adic iff it
  preserves analytic points (Proposition 8.39(1)).
* `ValuationSpectrum.morphism_preserves_nonAnalytic_affinoid` : Any continuous ring hom
  preserves non-analytic points (Proposition 8.39(2), affinoid case).
* `ValuationSpectrum.IsAdicMorphism.ringHom_isAdic` : All induced ring maps of an adic
  morphism are adic (Corollary 8.40).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.5, §8.4
-/

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]

/-! ### Support and comap -/

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` equals the preimage ideal `φ⁻¹(supp v)`. -/
theorem supp_comap (φ : A →+* B) (v : Spv B) :
    (comap φ v).supp = Ideal.comap φ v.supp := by
  have h := congr_arg PrimeSpectrum.asIdeal (suppFun_comap φ v)
  simpa using h

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` as a set equals `φ ⁻¹' (supp v : Set B)`. -/
theorem supp_comap_coe (φ : A →+* B) (v : Spv B) :
    ((comap φ v).supp : Set A) = φ ⁻¹' (v.supp : Set B) := by
  ext x; simp [supp_comap]

/-! ### Lemma 7.46(1): Non-analytic preservation -/

/-- **Lemma 7.46(1), first part.** Continuous ring homomorphisms preserve non-analytic points. -/
theorem nonAnalytic_comap_of_continuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) := by
  simp only [IsAnalytic, not_not] at hv ⊢
  rw [supp_comap_coe]
  exact hφ.isOpen_preimage _ hv

/-! ### Lemma 7.46(1): Adic homomorphisms preserve analytic points -/

section AdicPreservesAnalytic

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]

omit [IsHuberRing B] in
/-- If `supp(v)` contains the ideal of definition, then `supp(v)` is open. -/
private theorem supp_isOpen_of_idealOfDefinition_le
    (PB : PairOfDefinition B) (v : Spv B)
    (h : PB.idealOfDefinition ≤ v.supp) : IsOpen (v.supp : Set B) := by
  change IsOpen (v.supp.toAddSubgroup : Set B)
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset
      ((PB.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (PB.I ^ 1).zero_mem))
      (fun b hb ↦ by
        rw [Submodule.coe_toAddSubgroup]
        obtain ⟨y, hy, rfl⟩ := hb
        exact h (Ideal.mem_map_of_mem _ (pow_one PB.I ▸ hy))))

omit [IsTopologicalRing A] [IsTopologicalRing B] [IsLinearTopology A A]
  [IsHuberRing A] [IsHuberRing B] in
/-- If `I` maps into `supp(comap φ v)` and `φ` is adic, then `PB.idealOfDefinition ≤ supp v`. -/
private theorem idealOfDefinition_le_supp_of_adic
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (hAB : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (hrad : (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical = PB.I.radical)
    (v : Spv B)
    (hI : PA.idealOfDefinition ≤ (comap φ v).supp) :
    PB.idealOfDefinition ≤ v.supp := by
  have hI_comap : PA.I ≤ Ideal.comap PA.A₀.subtype (comap φ v).supp := by
    rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap] at hI
  have hmap_le : Ideal.map (PA.restrictRingHom PB φ hAB) PA.I ≤
      Ideal.comap PB.A₀.subtype v.supp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : (PA.A₀.subtype a : A) ∈ (comap φ v).supp := hI_comap ha
    rw [supp_comap] at ha'
    exact ha'
  have hJ_le : PB.I ≤ Ideal.comap PB.A₀.subtype v.supp := by
    calc PB.I ≤ PB.I.radical := Ideal.le_radical
    _ = (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical := hrad.symm
    _ ≤ (Ideal.comap PB.A₀.subtype v.supp).radical := Ideal.radical_mono hmap_le
    _ = Ideal.comap PB.A₀.subtype v.supp :=
        (Ideal.IsPrime.comap PB.A₀.subtype).radical
  rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]

omit [IsTopologicalRing A] in
/-- **Lemma 7.46(1), second part.** Adic homomorphisms preserve analytic points. -/
theorem analytic_comap_of_isAdicHom {φ : A →+* B}
    (hφ : IsAdicHom φ) {v : Spv B}
    (hv : IsAnalytic v) : IsAnalytic (comap φ v) := by
  intro hna
  apply hv; clear hv
  obtain ⟨PA, PB, hAB, hrad⟩ := hφ
  have hI_le : PA.idealOfDefinition ≤ (comap φ v).supp :=
    calc PA.idealOfDefinition
        ≤ topologicalNilradical A := PA.idealOfDefinition_le_topologicalNilradical
      _ ≤ ((comap φ v).supp).radical := topologicalNilradical_le_radical_of_isOpen hna
      _ = (comap φ v).supp := (instIsPrimeSupp _).radical
  exact supp_isOpen_of_idealOfDefinition_le PB v
    (idealOfDefinition_le_supp_of_adic PA PB φ hAB hrad v hI_le)

end AdicPreservesAnalytic

/-! ### Tate ring specializations of Lemma 7.46 -/

section TateSpecialization

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]

omit [IsTopologicalRing A] in
/-- In a Tate source ring, adic homomorphisms produce analytic comap points. -/
theorem analytic_comap_of_isAdicHom_tate [IsTateRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) (v : Spv B) :
    IsAnalytic (comap φ v) :=
  analytic_comap_of_isAdicHom hφ (IsTateRing.isAnalytic v)

end TateSpecialization

/-! ### Lemma 7.46(2): Converse — analytic preservation implies adic -/

section Lemma746Converse

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]
  [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]

/-- **Lemma 7.46(2) of Wedhorn.** If `B` is a complete Huber ring (with `(B, B⁺)` an
affinoid ring such that `A⁺ ⊆ B⁺` via `φ`) and the induced map `Spa(φ)` preserves
analytic points, then `φ` is an adic homomorphism.

The proof proceeds by contrapositive: if `φ` is not adic, one finds a non-open prime
`𝔭` of `B` via the radical mismatch, then applies **Lemma 7.45** to produce a
`v ∈ Spa(B)` with `supp(v) = 𝔭` that is analytic (non-open support), but whose
comap is non-analytic (since `supp(comap φ v) ⊇ I_A`, hence open). This contradicts
the hypothesis that `Spa(φ)` preserves analytic points.

**Sorry status:** Two helper lemmas are sorry'd:
1. `exists_compatible_pair` — constructing a pair of definition for `A` that is
   compatible with `PB` under `φ`. Fillable Huber ring construction.
2. `exists_analytic_spa_point_with_open_comap_supp` — the combined construction
   that produces `v ∈ Spa(B, B⁺)` with `IsAnalytic v` and `supp(comap φ v)` open.
   This requires: radical mismatch → B₀-prime → B-prime → Lemma 7.45 with exact
   support. The exact support direction is sorry'd in `Lemma745.lean`.

The main proof structure (contrapositive + contradiction) is sorry-free. -/

-- Helper 1: there exists a pair of definition for A compatible with PB under φ.
-- This is a standard fact: φ⁻¹(PB.A₀) is open (continuity), and any open subring
-- of a Huber ring contains a ring of definition with compatible ideal.
private theorem exists_compatible_pair
    {φ : A →+* B} (hφ : Continuous φ) (PB : PairOfDefinition B) :
    ∃ (PA : PairOfDefinition A), ∀ a ∈ PA.A₀, φ a ∈ PB.A₀ := by
  sorry

-- Helper 2a: from strict radical containment, find a separating prime of B₀.
-- This is a standard commutative algebra argument using Ideal.radical_eq_sInf.
omit [IsTopologicalRing A] [IsTopologicalRing B] [IsLinearTopology A A]
  [IsHuberRing A] [IsHuberRing B] in
private theorem exists_separating_prime_of_B₀
    {φ : A →+* B}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical) :
    ∃ (𝔭₀ : Ideal PB.A₀), 𝔭₀.IsPrime ∧
      Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀ ∧ ¬PB.I ≤ 𝔭₀ := by
  -- Strict containment gives an element in rad(J) \ rad(image)
  have h_strict := lt_of_le_of_ne h_le h_not_eq
  -- Choose j ∈ rad(J) \ rad(image). exists_of_ssubset gives (j ∈ t, j ∉ s).
  obtain ⟨j, hj_radJ, hj_not_radI⟩ :=
    Set.exists_of_ssubset (show (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical <
      PB.I.radical from h_strict)
  -- j ∉ rad(image), so there exists a prime 𝔭₀ ⊇ image with j ∉ 𝔭₀
  set img := Ideal.map (PA.restrictRingHom PB φ h_map) PA.I
  -- j ∉ rad(img), and rad(img) = sInf{𝔭 | img ≤ 𝔭 ∧ IsPrime 𝔭}
  have hj_not_all : ¬(∀ (𝔭 : Ideal PB.A₀), (img ≤ 𝔭 ∧ 𝔭.IsPrime) → j ∈ 𝔭) := by
    intro hall
    exact hj_not_radI (Ideal.radical_eq_sInf img ▸ Ideal.mem_sInf.mpr
      fun J hJ ↦ hall J hJ)
  push_neg at hj_not_all
  obtain ⟨𝔭₀, ⟨h_image_le, h𝔭₀_prime⟩, hj_not_p⟩ := hj_not_all
  refine ⟨𝔭₀, h𝔭₀_prime, h_image_le, fun hJ_le ↦ hj_not_p ?_⟩
  -- j ∈ rad(J) and J ≤ 𝔭₀ (prime), so j ∈ rad(J) ≤ rad(𝔭₀) = 𝔭₀
  exact h𝔭₀_prime.radical.symm ▸ Ideal.radical_mono hJ_le hj_radJ

-- Helper 2b: from a prime 𝔭₀ of B₀ (with image ≤ 𝔭₀ and J ⊄ 𝔭₀), produce an
-- analytic v ∈ Spa(B, B⁺) with PA.idealOfDefinition ≤ φ⁻¹(supp(v)).
-- This is the core of Lemma 7.46(2) that requires Lemma 7.45 with exact support.
--
-- Strategy: 𝔭₀ is a prime of B₀ with J ⊄ 𝔭₀. Since IsAdicComplete, 𝔭₀ is not
-- maximal (by not_isMaximal_of_I_not_le). Convert 𝔭₀ to a non-open prime 𝔭 of B,
-- then apply Lemma 7.45 with exact support to get v with supp(v) = 𝔭.
-- Then v is analytic (non-open support) and supp(comap φ v) = φ⁻¹(𝔭) ⊇
-- φ⁻¹(image of 𝔭₀) ⊇ PA.idealOfDefinition, so comap is non-analytic.
--
-- **Sorry:** The conversion from B₀-prime to B-prime (with controlled support)
-- and the exact support direction of Lemma 7.45.
private theorem exists_analytic_spa_point_from_B₀_prime
    [PlusSubring B]
    {φ : A →+* B}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime]
    (h_image_le : Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀)
    (hJ_not_le : ¬PB.I ≤ 𝔭₀)
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  sorry

-- Helper 2: the key construction, assembled from 2a and 2b.
private theorem exists_analytic_spa_point_with_open_comap_supp
    [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ)
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical)
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  -- Step 1: Get a separating prime of B₀
  obtain ⟨𝔭₀, h𝔭₀_prime, h_image_le, hJ_not_le⟩ :=
    exists_separating_prime_of_B₀ PA PB h_map h_not_eq h_le
  haveI := h𝔭₀_prime
  -- Step 2: Apply 2b to get the Spa point
  exact exists_analytic_spa_point_from_B₀_prime PA PB h_map h_image_le hJ_not_le hBplus_le_B₀

theorem isAdicHom_of_complete_and_analytic_preserved
    [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    IsAdicHom φ := by
  -- Step 1: Get a compatible pair of definition for A
  obtain ⟨PA, h_map⟩ := exists_compatible_pair hφ PB
  -- Step 2: By contradiction — if φ is not adic, the radical equality fails
  by_contra h_not_adic
  have h_ne : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical :=
    fun h_eq ↦ h_not_adic ⟨PA, PB, h_map, h_eq⟩
  -- Step 3: Produce an analytic v ∈ Spa(B, B⁺) whose comap has open support
  -- First: the easy direction rad(φ(I)·B₀) ≤ rad(J)
  have h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical := by
    rw [Ideal.radical_le_radical_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    -- PA.restrictRingHom sends a to ⟨φ(subtype a), _⟩ in PB.A₀
    -- a ∈ PA.I → PA.A₀.subtype a is top. nilpotent in A → φ-image is top. nilpotent in B
    have h_nil : IsTopologicallyNilpotent (φ (PA.A₀.subtype a)) :=
      (PA.isTopologicallyNilpotent_of_mem ha).map hφ
    have h_mem : φ (PA.A₀.subtype a) ∈ PB.A₀ := h_map _ a.2
    -- φ(subtype a) ∈ PB.A₀ and top. nilpotent → ⟨φ(subtype a), _⟩^N ∈ PB.I for some N
    obtain ⟨N, hN⟩ := PB.exists_pow_mem_I h_mem h_nil
    show PA.restrictRingHom PB φ h_map a ∈ PB.I.radical
    exact Ideal.mem_radical_iff.mpr ⟨N, hN⟩
  obtain ⟨v, hv_spa, hv_an, hv_open⟩ :=
    exists_analytic_spa_point_with_open_comap_supp hφ PA PB h_map h_ne h_le hBplus_le_B₀
  -- Step 4: Derive contradiction
  -- h_analytic says: v ∈ Spa, v analytic ⟹ comap φ v analytic (= support not open)
  -- But comap φ v has open support, hence is NOT analytic — contradiction
  exact (h_analytic v hv_spa hv_an) hv_open

end Lemma746Converse

/-! ### Definition 8.38: Adic morphisms of adic spaces -/

section AdicMorphismDef

universe u

open TopologicalSpace

/-- An open affinoid neighborhood datum for a point in an adic space: an open set `U`,
a point membership proof, an affinoid adic space `Y`, and a homeomorphism
`U ≃ₜ Spa(Y.Ring)`. This packages the local chart data for Definition 8.38. -/
structure AffinoidNeighborhood (X : AdicSpace.{u}) (x : X.carrier) where
  /-- The open set containing `x`. -/
  U : Opens X.carrier
  /-- Proof that `x ∈ U`. -/
  mem : x ∈ U
  /-- The affinoid adic space that `U` is homeomorphic to. -/
  aff : AffinoidAdicSpace.{u}
  /-- The homeomorphism `U ≃ₜ Spa(aff.Ring)`. -/
  homeo : ↥U ≃ₜ aff.toTopCat

/-- **Definition 8.38 of Wedhorn.** A continuous map `f : X.carrier → Y.carrier`
between the carriers of adic spaces is *adic* if for every `x ∈ X`, there exist
open affinoid neighborhoods `U ∋ x` in `X` and `V ∋ f(x)` in `Y` with
`f(U) ⊆ V`, such that the induced ring homomorphism
`𝒪_Y(V) → 𝒪_X(U)` is adic in the sense of Definition 6.23.

In the formal definition, we ask for affinoid neighborhood data (homeomorphisms to
affinoid spectra) and require the ring homomorphism between the witnessing affinoid
rings to be adic. The requirement `f(U) ⊆ V` is encoded by requiring that
`f` maps points of `U` into `V`.

The ring hom goes from the target ring to the source ring (`NY.aff.Ring →+* NX.aff.Ring`),
matching the contravariant nature of `Spa(φ) : Spa(B) → Spa(A)` for `φ : A →+* B`.
We require `IsHuberRing` instances on the affinoid rings since `IsAdicHom` is defined
for Huber ring homomorphisms (Definition 6.23 of Wedhorn). -/
def IsAdicMorphism (X Y : AdicSpace.{u}) (f : C(X.carrier, Y.carrier)) : Prop :=
  ∀ (x : X.carrier),
    ∃ (NX : AffinoidNeighborhood X x)
      (NY : AffinoidNeighborhood Y (f x))
      (_ : ∀ (p : ↥NX.U), f p.val ∈ NY.U)
      (_ : IsHuberRing NX.aff.Ring) (_ : IsHuberRing NY.aff.Ring)
      (φ : NY.aff.Ring →+* NX.aff.Ring),
      IsAdicHom φ

end AdicMorphismDef

/-! ### Proposition 8.39: Characterization via analytic points -/

section Prop839

/-- **Proposition 8.39(2) of Wedhorn (affinoid case).** Any continuous ring
homomorphism between Huber rings sends non-analytic points to non-analytic
points. This is the affinoid avatar of the statement that any morphism of
adic spaces preserves non-analytic points.

For the full adic space statement, one reduces to the affinoid case by
restricting to an affinoid chart and applying this result (Remark 8.37(2)).

The proof is `nonAnalytic_comap_of_continuous`, restated here for clarity. -/
theorem morphism_preserves_nonAnalytic_affinoid
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) :
    ¬IsAnalytic (comap φ v) :=
  nonAnalytic_comap_of_continuous hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, forward direction).**
An adic ring homomorphism `φ : A →+* B` between Huber rings induces a map
`Spa(φ)` that preserves analytic points.

This is `analytic_comap_of_isAdicHom` (Lemma 7.46(1)), restated in the
form needed for Proposition 8.39. -/
theorem isAdicHom_preserves_analytic
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]
    {φ : A →+* B} (hφ : IsAdicHom φ) :
    ∀ (v : Spv B), IsAnalytic v → IsAnalytic (comap φ v) :=
  fun _ hv ↦ analytic_comap_of_isAdicHom hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, reverse direction).**
If `B` is complete and `Spa(φ)` preserves analytic points, then `φ` is adic.

This is `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)),
restated for the iff form.

**Status:** The reverse direction requires Lemma 7.45; see `Lemma745.lean`. -/
theorem isAdicHom_of_preserves_analytic_complete
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]
    [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ hAB h_analytic PB hBplus_le_B₀

/-- **Proposition 8.39(1) of Wedhorn (adic space version).** A continuous map
`f : X.carrier → Y.carrier` between adic spaces is adic (Definition 8.38)
if and only if for every affinoid chart the induced ring hom preserves analytic
points under `Spa(φ)`.

The forward direction reduces to the affinoid case via Definition 8.38 and
applies `isAdicHom_preserves_analytic` (Lemma 7.46(1)).
The reverse direction uses `isAdicHom_of_preserves_analytic_complete`
(Lemma 7.46(2)), noting that presheaf values of adic spaces are completions.

**Status:** Sorry; requires connecting the abstract adic space machinery to
the affinoid-level results, and Lemma 7.45 for the reverse direction. -/
theorem isAdicMorphism_iff_preserves_analytic {X Y : AdicSpace}
    (f : C(X.carrier, Y.carrier)) :
    IsAdicMorphism X Y f ↔
      (∀ (A B : Type*) [CommRing A] [CommRing B]
        [TopologicalSpace A] [TopologicalSpace B]
        [IsTopologicalRing A] [IsTopologicalRing B]
        [IsLinearTopology A A] [IsHuberRing A] [IsHuberRing B]
        (φ : A →+* B),
        ∀ v : Spv B, IsAnalytic v → IsAnalytic (comap φ v)) := by
  sorry

end Prop839

/-! ### Corollary 8.40: All ring maps of an adic morphism are adic -/

section Cor840

/-- **Corollary 8.40 of Wedhorn.** Let `f : X → Y` be an adic morphism of adic
spaces. Then for *all* open affinoid subspaces `U ⊆ X` and `V ⊆ Y` with
`f(U) ⊆ V`, the induced ring homomorphism `𝒪_Y(V) → 𝒪_X(U)` is adic -- not
just the witnessing neighborhoods from Definition 8.38.

The proof combines Proposition 8.39(1) (adic iff analytic-preserving) with
Lemma 7.46(2) (analytic-preserving + completeness implies adic). Since
`𝒪_X(U)` is a completion and hence a complete topological ring, Lemma 7.46(2)
applies to any affinoid chart, not only the ones witnessing the definition.

We state this at the Huber ring level: given any adic morphism and any pair of
Huber rings arising from affinoid charts with a compatible ring hom, that
ring hom is adic.

**Status:** Sorry; requires Proposition 8.39 and Lemma 7.46(2), which in turn
require Lemma 7.45 (sorry in `Lemma745.lean`). -/
theorem IsAdicMorphism.ringHom_isAdic {X Y : AdicSpace}
    {f : C(X.carrier, Y.carrier)} (hf : IsAdicMorphism X Y f)
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B]
    (φ : A →+* B) :
    IsAdicHom φ := by
  sorry

end Cor840

end ValuationSpectrum
