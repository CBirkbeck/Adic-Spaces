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

/-! ### T-WEDHORN-1: `productRestriction_injective_tate`

This is the packaged Part-1-of-tateAcyclicity form needed by T-WEDHORN-2
(the IsSheafy reroute). The target signature takes the same instance bundle
as `tateAcyclicity` (no extra `hSpa` or `IsDomain A` ingredient) and
produces kernel triviality of the product restriction.

## Discharge strategy analysis

The intended route (Wedhorn Cor 8.32) factors through
`tateAcyclicity_zero_kernel_of_flat_and_lifting`, which asks for:

* `flat_over_base D` — each `presheafValue D.1` is flat as a
  `presheafValue C.base`-module along the restriction homomorphism
  (Wedhorn Prop 8.15 / Prop 8.30).
* `hSpa_surj` — for every prime `𝔭 ⊆ presheafValue C.base`, there is a
  cover piece `D` and a prime `𝔮 ⊆ presheafValue D.1` comapping to `𝔭`
  (spectral lifting content of the covering condition).

### What is discharged in this file

* **`flat_over_base` is DISCHARGED** (`flat_over_base_tate`): each
  `presheafValue D.1` is flat as a `presheafValue C.base`-module, proved
  from `restrictionMap_isLocalization` (Wedhorn Prop 8.15) via
  `IsLocalization.flat`. This fully closes the flatness side of the
  Cor 8.32 route.

* **`hSpa_surj` is DISCHARGED modulo a span-top hypothesis**
  (`hSpa_surj_from_spanTop`): given that the images `canonicalMap D.s` do
  not all lie in any prime `𝔭` of `presheafValue C.base` — i.e., the
  covering-piece uniformizers generate the unit ideal there — the
  spectral lifting follows by `IsLocalization.isPrime_of_isPrime_disjoint`
  applied through Prop 8.15.

The residual hypothesis for `hSpa_surj_from_spanTop` is the **presheaf-level
span-top** condition, which is Wedhorn Cor 8.31 content. Note that the
analogous span-top fact in `Localization.Away C.base.s` is proved for the
discrete case (`TateAcyclicity.lean:475`); the presheafValue-level version
reduces to that via the coeRingHom bijectivity infrastructure.

### Why the present theorem (with the task's signature) delegates

Both `flat_over_base` and `hSpa_surj` remain inherited from
`restrictionMap_isLocalization` (Wedhorn Prop 8.15), which itself is
transitively `sorryAx`-dependent on `restrictionMapHom_injective`
(`PresheafTateStructure.lean:1313`) and `restrictionMapHom_surj`
(`PresheafTateStructure.lean:1127`, Baire-category completion argument).
Consequently, any concrete proof of the target signature (no extra
hypotheses) must inherit that sorry chain. The most economical route
preserving the target signature is direct delegation to `tateAcyclicity`
Part 1, which resides at the same level of the sorry chain.

Once `restrictionMap_isLocalization` is discharged unconditionally (the
hardest remaining algebraic content), `productRestriction_injective_tate_of_spanTop`
with a closed span-top proof gives the target theorem through the
Cor 8.32 route exclusively (without any further upstream dependencies).

## Packaging role

The present theorem's value is **interface**, not logical strength: it
exposes the Part-1 conclusion as a standalone `theorem` callable by
`productRestriction_injective_tate` (without the conjunction wrapper and the
extra Part-2 hypothesis-stacking that using `.1` of `tateAcyclicity`
requires at callsites). T-WEDHORN-2 consumes this packaging to avoid
pattern-matching the `tateAcyclicity` conjunction at every callsite.

## Axiom status

`#print axioms productRestriction_injective_tate` returns the same axiom set
as `#print axioms tateAcyclicity`, namely `[propext, sorryAx,
Classical.choice, Quot.sound]`. No new sorries are introduced in this file;
the remaining `sorryAx` dependency trace to the upstream chain in
`PresheafTateStructure.lean` and `LaurentRefinement.lean`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Corollary 8.32, Proposition
  8.15, Proposition 8.30, Theorem 8.28(b).
* `docs/TICKETS-tate-acyclicity.md` — T-WEDHORN-1 ticket.
* `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — Phase 3.
-/

/-- **T-WEDHORN-1 target theorem.** Part 1 (kernel-triviality) of
`tateAcyclicity`, exposed as a standalone packaged theorem for consumption
by T-WEDHORN-2's IsSheafy reroute.

Under the instance bundle `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A]` and the data `(P, C, hne)`, if an element
`x : presheafValue C.base` maps to zero on every cover piece `D ∈ C.covers`,
then `x = 0`.

**Proof route.** Delegates to `tateAcyclicity` Part 1
(`LaurentRefinement.lean:3671`). The Cor 8.32 route via
`tateAcyclicity_zero_kernel_of_flat_and_lifting` is available (see the
companion theorems `flat_over_base_tate`, `hSpa_surj_from_spanTop`, and
`productRestriction_injective_tate_of_spanTop` below, which discharge
`flat_over_base` unconditionally and `hSpa_surj` modulo a span-top
hypothesis); however, the residual span-top content at the presheaf level
is itself transitively `sorryAx`-dependent at the current infrastructure
state, so direct delegation to `tateAcyclicity` Part 1 is the most
economical target-signature proof.

**Signature preservation.** The instance bundle is identical to that of
`tateAcyclicity`; no extra typeclass or data hypothesis is required. This
matches the T-WEDHORN-1 target shape exactly. -/
theorem productRestriction_injective_tate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  (ValuationSpectrum.tateAcyclicity P C hne).1 x hx

/-! ### Cor 8.32-route alternative: conditional `productRestriction_injective_tate`

The theorem below supplies an alternative proof of
`productRestriction_injective_tate` via the Wedhorn Cor 8.32 faithful-flatness
route, conditional on the two ingredients `flat_over_base` and `hSpa_surj`
that abstract Cor 8.32 requires.

This is **not** a logical strengthening — it has strictly more hypotheses
than the direct-delegation version above — but it exposes the Cor 8.32
factorization as a callable lemma. Once either of `restrictionMap_isLocalization`
(Wedhorn Prop 8.15) or a direct presheafValue-flatness proof is discharged,
the caller can invoke this theorem with the freshly proved hypotheses and
thereby produce a proof of `productRestriction_injective_tate` that does
**not** route through `tateAcyclicity` Part 1's `restrictionMapHom_injective`.

The `tate` suffix flags that this is the T-WEDHORN-1-shape consumer (with
`hne` hypothesis instead of the empty-cover-handling `rationalCovering_hasSeparation`
form, which requires `IsDomain A`). -/
theorem productRestriction_injective_tate_via_cor832
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (_hne : C.covers.Nonempty)
    (flat_over_base : ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule))
    (hSpa_surj : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  tateAcyclicity_zero_kernel_of_flat_and_lifting C flat_over_base hSpa_surj x hx

/-! ### Prime-lifting scaffold for `hSpa_surj` (via Prop 8.15)

This lemma packages the **localization-style prime lifting** from an
`IsLocalization.Away` structure on the restriction map. It is **unconditional**
modulo the existing `restrictionMap_isLocalization` (Wedhorn Prop 8.15,
`PresheafTateStructure.lean:1499`), which is proved (transitively
`sorryAx`-dependent on the upstream `restrictionMapHom_injective` /
`restrictionMapHom_surj` chain, but compiles).

The scaffold converts "some cover piece `D` has `canonicalMap D.s ∉ 𝔭`" (the
span-top content of Wedhorn Cor 8.31) into the `hSpa_surj` hypothesis
required by `tateAcyclicity_zero_kernel_of_flat_and_lifting`. The algebraic
prime-lifting uses the standard `IsLocalization.isPrime_of_isPrime_disjoint`
route. -/
theorem hSpa_surj_from_spanTop
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (hspan_top : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p := by
  intro p hp
  obtain ⟨D, hD_notin⟩ := hspan_top p hp
  letI : Algebra (presheafValue C.base) (presheafValue D.1) :=
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI : @IsLocalization.Away (presheafValue C.base) _
      (C.base.canonicalMap D.1.s) (presheafValue D.1) _
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra :=
    restrictionMap_isLocalization P C.base D.1 (C.hsubset D.1 D.2)
  have hdisj : Disjoint
      (Submonoid.powers (C.base.canonicalMap D.1.s) : Set (presheafValue C.base))
      (p : Set (presheafValue C.base)) := by
    rw [Set.disjoint_right]
    rintro x hx ⟨n, rfl⟩
    exact hD_notin (hp.mem_of_pow_mem n hx)
  refine ⟨D, p.map (algebraMap (presheafValue C.base) (presheafValue D.1)),
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers (C.base.canonicalMap D.1.s))
      (presheafValue D.1) p hp hdisj, ?_⟩
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.powers (C.base.canonicalMap D.1.s))
    (presheafValue D.1) hp hdisj
  -- The algebraMap is definitionally equal to restrictionMapHom under the algebra
  -- structure we set up.
  convert hcomap using 1

/-! ### Flatness discharge for `flat_over_base` (via Prop 8.15)

**Unconditional discharge of the `flat_over_base` hypothesis** of
`tateAcyclicity_zero_kernel_of_flat_and_lifting`, modulo the existing
`restrictionMap_isLocalization`. Each `presheafValue D.1` is flat as a
`presheafValue C.base`-module along the restriction map, because
restrictions are localizations (Wedhorn Prop 8.15) and localizations are
flat (`IsLocalization.flat`). -/
theorem flat_over_base_tate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule) := by
  intro D
  letI : Algebra (presheafValue C.base) (presheafValue D.1) :=
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI : @IsLocalization.Away (presheafValue C.base) _
      (C.base.canonicalMap D.1.s) (presheafValue D.1) _
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra :=
    restrictionMap_isLocalization P C.base D.1 (C.hsubset D.1 D.2)
  -- `IsLocalization.flat` delivers `Module.Flat` from the `IsLocalization` structure.
  -- The ambient `Module` structure is `Algebra.toModule`, which matches
  -- `(restrictionMapHom ...).toModule` by definition.
  exact IsLocalization.flat (presheafValue D.1) (Submonoid.powers (C.base.canonicalMap D.1.s))

/-! ### End-to-end combinator via Prop 8.15 + span-top

Given the **span-top content** (Wedhorn Cor 8.31), `productRestriction_injective_tate`
follows via the Cor 8.32 faithful-flatness route without any further hypotheses.
This eliminates the `flat_over_base` hypothesis entirely by threading
`restrictionMap_isLocalization` (Prop 8.15) into both scaffolds.

`span-top` is the remaining residual: it states that for every prime `𝔭 ⊆
presheafValue C.base`, the canonical images `canonicalMap D.s` of the cover
pieces do not all lie in `𝔭` — equivalently, the ideal generated by
`{canonicalMap D.s : D ∈ C.covers}` is the unit ideal in `presheafValue
C.base`. This is Wedhorn Cor 8.31 content (once translated through
`presheafValue C.base ≅ completion of Localization.Away C.base.s`). -/
theorem productRestriction_injective_tate_of_spanTop
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (hspan_top : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_via_cor832 P C hne
    (flat_over_base_tate P C)
    (hSpa_surj_from_spanTop P C hspan_top)
    x hx

end ValuationSpectrum
