/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.Module.Pi
import «Adic spaces».StructureSheaf
import «Adic spaces».FlatnessResults

/-!
# Corollary 8.32 of Wedhorn (faithful flatness of product restriction)

**Statement (Wedhorn Cor 8.32, p. 83)**: Let `(A, A⁺)` be a strongly noetherian
Tate affinoid ring, `X = Spa A`, and `(U_i)_{1 ≤ i ≤ n}` a finite covering of
`X` by rational subsets. The homomorphism
`𝒪_X(X) → ∏_i 𝒪_X(U_i)` given by restriction is faithfully flat (in
particular injective).

## Approach

Wedhorn's proof has two ingredients:
1. **Flatness** (Prop 8.30): each restriction map `𝒪_X(X) → 𝒪_X(U_i)` is flat.
2. **Lying over** (lifting of primes): every prime `𝔭` of `𝒪_X(X)` is the image
   (under `comap`) of some prime of the product.

Given that `𝒪_X(U_i) = (𝒪_X(X))_{f_i}`-style localizations (Prop 8.15), the
lying-over follows spectrally.

This file delivers the **abstract Cor 8.32**: given the flatness + joint prime
surjectivity as hypotheses, it produces the faithful flatness and derives
injectivity of the product map.

The key mathlib ingredients are:
* `Module.Flat.pi` — finite products of flat modules are flat (already ported
  in `FlatnessResults.lean`).
* `Module.FaithfullyFlat.of_comap_surjective` — flat + lying-over ⇒ faithfully
  flat.
* `Module.FaithfullyFlat.tensorProduct_mk_injective` — faithfully flat ⇒
  injective on `M → B ⊗[A] M`, specialized to `M = A`, yields injectivity of
  `algebraMap`.

## Signature discipline

`productRestriction_faithfullyFlat_abstract` and `productRestriction_injective`
take explicit flatness + lying-over hypotheses. The unconditional
`restrictionMapHom_injective` in `PresheafTateStructure.lean` is NOT bypassed
here — it has its own (Wedhorn Prop 8.15)-type algebraic gap that requires the
Tate-quotient unit `mk_D₀s_isUnit` step, orthogonal to Cor 8.32.

Importantly, Wedhorn Cor 8.32 delivers **product** injectivity/faithful
flatness, not single-map injectivity. A single projection from
`presheafValue D₀` to one cover piece `presheafValue D` cannot be obtained
from Cor 8.32 alone, because faithful flatness of the product does not imply
faithful flatness of any factor (only the *product* is injective, via the
lying-over / Spec surjection over all factors jointly). This is why
`restrictionMapHom_injective` remains a distinct blocker: it requires the
Prop 8.15 localization identification, not Cor 8.32.

## Axiom status

The **abstract** (ring-theoretic) lemmas `faithfullyFlat_pi_of_prime_surjection`
and `algebraMap_pi_injective_of_prime_surjection` are axiom-clean (only
`propext`, `Classical.choice`, `Quot.sound`).

The **concrete** RationalCovering-level lemmas inherit a pre-existing sorry
from `Adic spaces/Presheaf.lean:720` (`spa_point_nonOpen_of_rational_subset`
— a bypassed helper retired in favor of the standard-cover reduction). This
is NOT introduced by Cor 8.32 work; it lives upstream of everything that uses
`restrictionMapHom`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Corollary 8.32.
* `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — Phase 3 of the Wedhorn plan.
-/

open ValuationSpectrum TensorProduct

namespace ValuationSpectrum

/-! ### Abstract Cor 8.32

Given a commutative ring `R`, a finite family `B : ι → Type*` of `R`-algebras,
each flat and with joint surjection on `Spec`, the product `∏ B i` is
faithfully flat over `R`.
-/

/-- **Product of flat algebras is flat over `R`** — immediate consequence of
`Module.Flat.pi` applied to the `R`-module product structure. -/
theorem Module.Flat.pi_of_algebra {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)] :
    Module.Flat R (∀ i, B i) :=
  _root_.Module.Flat.pi

/-- **Abstract Corollary 8.32 (faithful flatness)**: given a finite family of
flat `R`-algebras `B i` such that every prime of `R` is a `comap` of some
prime of some `B i`, the product algebra `∏ B i` is faithfully flat over `R`.

The hypothesis `hsurj` is the **lying-over** content of Cor 8.32 — it packages
the Wedhorn Spa-cover condition at the level of prime spectra. -/
theorem faithfullyFlat_pi_of_prime_surjection
    {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)]
    (hsurj : ∀ (p : Ideal R), p.IsPrime →
      ∃ (i : ι) (q : Ideal (B i)), q.IsPrime ∧ q.comap (algebraMap R (B i)) = p) :
    Module.FaithfullyFlat R (∀ i, B i) := by
  classical
  -- The product is flat.
  haveI : Module.Flat R (∀ i, B i) := Module.Flat.pi_of_algebra B
  -- Lying over at the level of the product: given prime `p`, lift to a prime
  -- of some component `B i`, then push to a prime of `∏ B i`.
  apply Module.FaithfullyFlat.of_comap_surjective
  rintro ⟨p, hp⟩
  obtain ⟨i, q, hq_prime, hq_comap⟩ := hsurj p hp
  -- The projection `π_i : ∏ B i → B i` is a surjective ring hom, so `comap`
  -- pulls primes of `B i` back to primes of `∏ B i`.
  let π : (∀ j, B j) →+* B i := Pi.evalRingHom (fun j => B j) i
  refine ⟨⟨q.comap π, hq_prime.comap π⟩, ?_⟩
  -- `comap (algebraMap R (∏ B j)) (q.comap π) = p` unfolds via
  -- `Ideal.comap_comap` and the fact that `π ∘ algebraMap R (∏ B j) = algebraMap R (B i)`.
  apply PrimeSpectrum.ext
  change (q.comap π).comap (algebraMap R (∀ j, B j)) = p
  rw [Ideal.comap_comap]
  have hcomp : (π.comp (algebraMap R (∀ j, B j))) = algebraMap R (B i) := by
    ext r
    change π (algebraMap R (∀ j, B j) r) = algebraMap R (B i) r
    simp [π, Pi.evalRingHom, Pi.algebraMap_apply]
  rw [hcomp]; exact hq_comap

/-- **Corollary 8.32 in injective form**: the product restriction is injective
given flatness + prime surjectivity.

This follows immediately from `faithfullyFlat_pi_of_prime_surjection` via
`Module.FaithfullyFlat.tensorProduct_mk_injective` applied to `M = R`, which
specializes to injectivity of the algebra map. -/
theorem algebraMap_pi_injective_of_prime_surjection
    {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Flat R (B i)]
    (hsurj : ∀ (p : Ideal R), p.IsPrime →
      ∃ (i : ι) (q : Ideal (B i)), q.IsPrime ∧ q.comap (algebraMap R (B i)) = p) :
    Function.Injective (algebraMap R (∀ i, B i)) := by
  haveI := faithfullyFlat_pi_of_prime_surjection B hsurj
  exact FaithfulSMul.algebraMap_injective R (∀ i, B i)

/-! ### Injectivity of the product restriction from Spa-points lying-over

The concrete Cor 8.32 instantiation for `RationalCovering`. Given the
Spa-point lying-over hypothesis and the flatness of each cover piece over the
BASE, the product restriction is faithfully flat.

**Note**: This is stated for flatness of each `presheafValue D` over
`presheafValue C.base` (not over `A`). That flatness is precisely what
`restrictionMap_isLocalization` (Prop 8.15) delivers — currently conditional
on `restrictionMapHom_injective`. The `flat_over_base` hypothesis here captures
exactly that conditional content.
-/

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- The `presheafValue C.base`-module structure on `presheafValue D` induced
by the restriction ring homomorphism. -/
noncomputable abbrev restrictionModule (C : RationalCovering A)
    (D : { D : RationalLocData A // D ∈ C.covers }) :
    Module (presheafValue C.base) (presheafValue D.1) :=
  (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule

/-- The `presheafValue C.base`-algebra structure on `presheafValue D` induced
by the restriction ring homomorphism. -/
noncomputable abbrev restrictionAlgebra (C : RationalCovering A)
    (D : { D : RationalLocData A // D ∈ C.covers }) :
    Algebra (presheafValue C.base) (presheafValue D.1) :=
  (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra

/-- **Concrete Cor 8.32 (product restriction faithfully flat)**: given that
each cover-piece presheafValue is flat as a module over the base presheafValue
(via the restriction algebra map) and the Spa-point prime lifting condition
holds, the product restriction
`presheafValue C.base → ∀ D, presheafValue D.1` induces a faithfully flat
algebra.

**Hypotheses**:
* `flat_over_base D` : `presheafValue D.1` is flat as a `presheafValue C.base`-
  module (with respect to the `restrictionAlgebra` structure). By Wedhorn
  Prop 8.15 (`restrictionMap_isLocalization`), each restriction is a
  localization, hence flat; the caller supplies this fact as a hypothesis.
* `hSpa_surj` : for every prime `p` of `presheafValue C.base`, there is a cover
  piece `D` and a prime `q` of `presheafValue D.1` that `comap`s to `p`. This
  is the Spa-point lifting — for strongly noetherian Tate rings, it follows
  from the covering condition `⋃ rationalOpen Uᵢ = Spa A`. -/
theorem productRestriction_faithfullyFlat_abstract
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  -- Step A: wrap the cover pieces as a Type-family via a synonym that Lean
  -- can recognize non-reducibly for typeclass inference.
  -- The standard trick: use a local `let` defining the factor type, so we
  -- pin the elaboration context with concrete `CommRing`, `Algebra`,
  -- `Module.Flat` instances on the synonym.
  letI algInst : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
    (presheafValue D.1) := fun D =>
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  -- Direct application to concrete identifiers (no lambdas in `B`).
  haveI flatInst : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        (Algebra.toModule (R := presheafValue C.base) (A := presheafValue D.1)) :=
    flat_over_base
  -- Apply the abstract lemma directly with an explicit instance refinement.
  refine @faithfullyFlat_pi_of_prime_surjection (presheafValue C.base) _
    { D // D ∈ C.covers } _ (fun D : { D // D ∈ C.covers } => presheafValue D.1)
    (fun D => inferInstance) (fun D => inferInstance) (fun D => flatInst D) ?_
  intro p hp
  obtain ⟨D, q, hq_prime, hq_comap⟩ := hSpa_surj p hp
  refine ⟨D, q, hq_prime, ?_⟩
  change q.comap (algebraMap (presheafValue C.base) (presheafValue D.1)) = p
  have halg : (algebraMap (presheafValue C.base) (presheafValue D.1)) =
      restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) := rfl
  rw [halg]; exact hq_comap

/-- **Cor 8.32 in injective form for the product restriction**: the product
restriction is injective given the flatness of each single restriction
(over the base) and the Spa-point prime lifting condition.

This is the form consumed by `tateAcyclicity` Part 1: an element mapped to
zero on every cover piece (i.e., in the kernel of the product restriction)
must be zero. -/
theorem productRestriction_injective_of_flat_and_lifting
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    Function.Injective
      (fun (x : presheafValue C.base) (D : { D // D ∈ C.covers }) =>
        restrictionMap C.base D.1 (C.hsubset D.1 D.2) x) := by
  letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
    (presheafValue D.1) := fun D =>
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI := productRestriction_faithfullyFlat_abstract C flat_over_base hSpa_surj
  -- Under this algebra structure, the product's algebraMap is precisely the
  -- product restriction, so its injectivity transports directly.
  have hinj : Function.Injective
      (algebraMap (presheafValue C.base)
        (∀ D : { D // D ∈ C.covers }, presheafValue D.1)) :=
    FaithfulSMul.algebraMap_injective _ _
  intro x y hxy
  apply hinj
  -- Unfold: `algebraMap (∀ D, presheafValue D.1) x D = (algebraMap _ _ x) D`
  -- and for each `D`, `algebraMap (presheafValue D.1) x = restrictionMapHom ... x`.
  funext D
  change restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
    restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y
  exact congr_fun hxy D

/-! ### `tateAcyclicity` Part 1 consumed directly

The next two theorems show how the product-injectivity form feeds into the
exact shape of `tateAcyclicity` Part 1. A caller supplying `flat_over_base` +
`hSpa_surj` obtains the Part 1 kernel-triviality conclusion without routing
through `restrictionMapHom_injective`.
-/

/-- **`tateAcyclicity` Part 1, via Cor 8.32**. Given the flatness of each
restriction and the Spa-point prime lifting, Part 1 of Tate acyclicity —
`x mapped to zero everywhere implies x = 0` — follows from faithful flatness
of the product restriction.

This gives the same conclusion as `tateAcyclicity` Part 1 but via the Wedhorn
Cor 8.32 route (as opposed to a single-map `restrictionMapHom_injective`,
which is NOT directly derivable from Cor 8.32 since Cor 8.32 is inherently a
product statement; see the doc block of `restrictionMapHom_injective` in
`PresheafTateStructure.lean` for the detailed explanation).

The caller discharges `flat_over_base` via Wedhorn Prop 8.15 (still a sorry'd
ingredient via `restrictionMap_isLocalization`) and `hSpa_surj` via the
Spa-point covering condition. -/
theorem tateAcyclicity_zero_kernel_of_flat_and_lifting
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0 := by
  intro x hx
  have hinj := productRestriction_injective_of_flat_and_lifting C flat_over_base hSpa_surj
  apply hinj
  funext D
  -- LHS: `restrictionMap C.base D.1 _ x = 0` by `hx`. RHS: `restrictionMap ... 0 = 0`.
  change restrictionMap C.base D.1 (C.hsubset D.1 D.2) x =
    restrictionMap C.base D.1 (C.hsubset D.1 D.2) 0
  rw [hx D.1 D.2,
    show restrictionMap C.base D.1 (C.hsubset D.1 D.2) (0 : presheafValue C.base) = 0 from
      map_zero (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2))]

/-! ### Connection to `productRestrictionSub` -/

/-- The product-restriction-over-subtypes (`productRestrictionSub`) is injective
whenever flat + Spa-lifting hold.

This is the form that feeds into `IsSheafy.embedding`'s `Injective`
component via `Topology.IsEmbedding.injective`. -/
theorem productRestrictionSub_injective_of_flat_and_lifting
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p) :
    Function.Injective (productRestrictionSub A C) := by
  intro x y hxy
  apply productRestriction_injective_of_flat_and_lifting C flat_over_base hSpa_surj
  exact hxy

end ValuationSpectrum
