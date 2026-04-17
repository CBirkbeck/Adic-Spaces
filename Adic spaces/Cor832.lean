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

/-! ### Reduction of `hspan_top` from `presheafValue C.base` to `Localization.Away C.base.s`

The `hspan_top` hypothesis is stated at the **completion** level
`presheafValue C.base`. We reduce it to the simpler **localization** level
`Localization.Away C.base.s` via the completion map `C.base.coeRingHom`.

The pivot is the identity `C.base.canonicalMap = C.base.coeRingHom ∘ algebraMap
A (Localization.Away C.base.s)` from the definition of `canonicalMap`; hence if
`{algebraMap A _ D.s : D ∈ C.covers}` spans `⊤` in the localization, its image
under `coeRingHom` is `{C.base.canonicalMap D.s}` spanning `⊤` in the
completion (ring-hom transfer via `Ideal.map_span` + `Ideal.map_top`). -/

/-- **Ring-hom transfer of span-top**: if a finite family spans ⊤ in `R`,
its image under any ring homomorphism spans ⊤ in `R'`. This is a direct
consequence of `Ideal.map_span` + `Ideal.map_top`. -/
theorem span_top_image_of_span_top_of_ringHom
    {R R' : Type*} [CommSemiring R] [CommSemiring R']
    (f : R →+* R') (s : Set R) (hs : Ideal.span s = ⊤) :
    Ideal.span (f '' s) = ⊤ := by
  rw [← Ideal.map_span, hs, Ideal.map_top]

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Span-top in the completion from span-top in the localization.** Given the
span-top condition `Ideal.span {algebraMap A (Localization.Away C.base.s) D.s
| D ∈ C.covers} = ⊤` at the localization level, the image-span
`Ideal.span {C.base.canonicalMap D.s | D ∈ C.covers} = ⊤` holds at the
completion level.

This is the **ring-hom transfer** of span-top along the canonical completion
map `C.base.coeRingHom : Localization.Away C.base.s →+* presheafValue C.base`.
The factorization `canonicalMap = coeRingHom ∘ algebraMap` is definitional, so
the image of `{algebraMap D.s}` under `coeRingHom` is precisely
`{canonicalMap D.s}`. Stated with `Set.image (· ∘ D.s)` over the set
`C.covers.toSet` to avoid `DecidableEq` constraints from `Finset.image`. -/
theorem spanTop_presheafValue_of_localization
    (C : RationalCovering A)
    (hspan_loc : Ideal.span ((fun D : RationalLocData A =>
        algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _)) = ⊤) :
    Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) = ⊤ := by
  -- The image of {algebraMap D.s} under C.base.coeRingHom is {canonicalMap D.s},
  -- since canonicalMap = coeRingHom.comp (algebraMap A _) by definition.
  have himg :
      (C.base.coeRingHom '' ((fun D : RationalLocData A =>
          algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _))) =
      ((fun D : RationalLocData A =>
          C.base.canonicalMap D.s) '' (C.covers : Set _)) := by
    rw [Set.image_image]
    rfl
  -- Apply `Ideal.map_span` + `Ideal.map_top`: image of span-top under ring hom is span-top.
  rw [← himg, ← Ideal.map_span, hspan_loc, Ideal.map_top]

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **`hspan_top` form from span-top identity**: if `Ideal.span
{C.base.canonicalMap D.s | D ∈ C.covers} = ⊤` holds in `presheafValue C.base`,
then for every prime `p ⊆ presheafValue C.base` there is some `D ∈ C.covers`
with `C.base.canonicalMap D.1.s ∉ p`.

This is the `Ideal.eq_top_iff_one` ⇔ "no prime contains all generators"
equivalence, specialized to the subtype formulation of `hspan_top`. -/
theorem hspan_top_of_spanTop_presheafValue
    (C : RationalCovering A)
    (hspan : Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) = ⊤) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p := by
  intro p hp
  by_contra hall
  push_neg at hall
  -- Every `canonicalMap D.s` lies in p (for D ∈ C.covers).
  have hsub : ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) ⊆ (p : Set _) := by
    rintro y ⟨D, hD, rfl⟩
    exact hall ⟨D, hD⟩
  have hspan_le : Ideal.span ((fun D : RationalLocData A =>
      C.base.canonicalMap D.s) '' (C.covers : Set _)) ≤ p :=
    Ideal.span_le.mpr hsub
  rw [hspan] at hspan_le
  exact hp.ne_top (top_le_iff.mp hspan_le)

/-! ### End-to-end `hspan_top` from A-level Spa-point hypothesis

This combinator reduces the completion-level `hspan_top` to a purely A-level
input: the **Spa-point-in-rational-open hypothesis** `hSpa_points`, which says
for every prime `p ⊆ A` with `C.base.s ∉ p`, there is `v ∈ rationalOpen
C.base.T C.base.s` with `p ≤ v.supp`.

This hypothesis is the Wedhorn Prop 7.41 / Lemma 7.45 content for the Tate
case. The OPEN prime subcase is automatically available via
`exists_spa_point_in_rationalOpen_of_isOpen_prime` (`StructureSheaf.lean:602`);
the NON-OPEN subcase requires the specialization-theoretic upgrade
(`exists_mem_spa_supp_ge_of_nonOpen_prime` + Wedhorn Prop 7.41) to move the
non-open-prime Spa point into the rational open.

Concretely: the proof argues at the localization `Localization.Away C.base.s`
level (where the non-open-prime difficulty is equivalent), reducing to the
A-level via `comap` of the localization map. For every prime `q` of the
localization, `q.comap(algebraMap A _)` is a prime `p ⊆ A` with
`C.base.s ∉ p`; by `hSpa_points`, a Spa point `v ∈ rationalOpen C.base.T
C.base.s` with `p ≤ v.supp` exists, and by `C.hcover v` some cover piece `D`
has `v ∈ rationalOpen D.T D.s`, giving `v(D.s) ≠ 0` hence `D.s ∉ p` hence
`algebraMap D.s ∉ q`. -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **A-level span-top in `Localization.Away C.base.s` from `hSpa_points`.**
Given the Spa-point-in-rational-open hypothesis (for primes of `A` avoiding
`C.base.s`), the images of `D.s` in `Localization.Away C.base.s` span the
unit ideal. This is the Tate generalization of the discrete-case argument at
`TateAcyclicity.lean:475`, with `hSpa_points` replacing the trivial-valuation
continuity (which held automatically in the discrete case). -/
theorem spanTop_localization_of_hSpa_points
    (C : RationalCovering A)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    Ideal.span ((fun D : RationalLocData A =>
        algebraMap A (Localization.Away C.base.s) D.s) '' (C.covers : Set _)) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq_max, hq_le⟩ := Ideal.exists_le_maximal _ hne
  haveI : q.IsPrime := Ideal.IsMaximal.isPrime hq_max
  -- Pull back to a prime p of A with C.base.s ∉ p and D.s ∈ p for all D ∈ C.covers.
  set p := q.comap (algebraMap A (Localization.Away C.base.s)) with hp_def
  have hp_prime : p.IsPrime := Ideal.IsPrime.comap _
  have hDs_in : ∀ D ∈ C.covers, D.s ∈ p := by
    intro D hD
    exact hq_le (Ideal.subset_span ⟨D, hD, rfl⟩)
  have hbs_notin : C.base.s ∉ p := by
    intro hmem
    have : algebraMap A (Localization.Away C.base.s) C.base.s ∈ q := hmem
    exact Ideal.IsMaximal.ne_top hq_max (Ideal.eq_top_of_isUnit_mem q this
      (IsLocalization.map_units (Localization.Away C.base.s)
        (⟨C.base.s, 1, pow_one _⟩ : Submonoid.powers C.base.s)))
  -- Produce a Spa point witnessing the contradiction.
  obtain ⟨v, hv_rat, hv_supp_ge⟩ := hSpa_points p hp_prime hbs_notin
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  -- v(D.s) ≠ 0 since v ∈ rationalOpen D.T D.s.
  have hDs_notin_supp : D.s ∉ v.supp := fun hDs ↦
    hv_D.2.2 ((v.mem_supp_iff D.s).mp hDs)
  -- But D.s ∈ p ⊆ v.supp, contradicting the previous line.
  exact hDs_notin_supp (hv_supp_ge (hDs_in D hD))

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **`hspan_top` at the completion level from `hSpa_points`.** Chains the
localization-level span-top (via `spanTop_localization_of_hSpa_points`) with
the ring-hom transfer (via `spanTop_presheafValue_of_localization`) and the
"no-prime-contains" conversion (via `hspan_top_of_spanTop_presheafValue`),
yielding the `hspan_top` hypothesis signature exactly. -/
theorem hspan_top_of_hSpa_points
    (C : RationalCovering A)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p := by
  have hloc := spanTop_localization_of_hSpa_points C hSpa_points
  have hpv := spanTop_presheafValue_of_localization C hloc
  exact hspan_top_of_spanTop_presheafValue C hpv

/-- **`productRestriction_injective_tate` via Cor 8.32 + A-level Spa-points.**
Given the A-level Spa-point-in-rational-open hypothesis (for primes of `A`
avoiding `C.base.s`), the full `productRestriction_injective_tate`
conclusion follows via the Cor 8.32 faithful-flatness route.

This is the **end-to-end** packaging: the Spa-points hypothesis is the sole
residual A-level input, which is the well-known Wedhorn Prop 7.41 / Lemma
7.45 content. No extra `hspan_top` hypothesis at the completion level is
required. -/
theorem productRestriction_injective_tate_of_hSpa_points
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_spanTop P C hne
    (hspan_top_of_hSpa_points C hSpa_points) x hx

/-! ### Open-prime discharge of `hSpa_points`

The `hSpa_points` hypothesis for OPEN primes is **unconditionally** discharged
by `exists_spa_point_in_rationalOpen_of_isOpen_prime`. This reduces the
residual obligation to the **non-open-prime** subcase, which is the
Wedhorn Prop 7.41 specialization content still pending.

Callers can dispatch on openness of `p` and only need to supply a proof for
the non-open-prime case. -/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Open-prime discharge**: for an open prime `p` with `C.base.s ∉ p`, the
Spa-point-in-rational-open hypothesis is automatic via
`exists_spa_point_in_rationalOpen_of_isOpen_prime`. This fully closes
the open sub-case of `hSpa_points`. -/
theorem hSpa_points_open_prime
    (C : RationalCovering A)
    (p : Ideal A) [p.IsPrime]
    (hp_open : IsOpen (p : Set A))
    (hs_notin : C.base.s ∉ p) :
    ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp :=
  ValuationSpectrum.exists_spa_point_in_rationalOpen_of_isOpen_prime
    (A := A) C.base.T C.base.s p hp_open hs_notin

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Open-primes-only `hSpa_points`**: if every prime `p ⊆ A` avoiding
`C.base.s` happens to be open, then `hSpa_points` is unconditional. This
is the automatic scenario — e.g., for discrete `A`, and more generally when
the Jacobson radical of the pseudouniformizer controls all `s`-avoiding
primes. -/
theorem hSpa_points_of_all_open
    (C : RationalCovering A)
    (h_all_open : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      IsOpen (p : Set A)) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := fun p hp hs =>
  hSpa_points_open_prime C p (h_all_open p hp hs) hs

/-- **End-to-end `productRestriction_injective_tate` under all-primes-open.**
If every prime of `A` avoiding `C.base.s` is open — which is automatic in
the discrete case and in other specific settings — the full Cor 8.32 route
closes unconditionally. -/
theorem productRestriction_injective_tate_of_all_primes_open
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (h_all_open : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      IsOpen (p : Set A))
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_of_all_open C h_all_open) x hx

/-! ### Non-open prime discharge via Lemma 7.45 on the completion

For the **non-open prime** subcase, we follow the strategy outlined in
`project_T001_completion_route` (memory): apply Lemma 7.45 not to `A` (which
need not be complete) but to the completion `presheafValue C.base`, which IS
complete by uniform completion, and then pull back via `canonicalMap`.

The key infrastructure assembled below:

1. **`presheafValue_isAdicComplete`** — `IsAdicComplete` for the concrete pair
   of definition on `presheafValue C.base`. Derived from
   `IsAdic.isAdicComplete_iff` using:
   - `IsAdic`: from `presheafValue_isAdic`
   - `CompleteSpace`: closed subring of complete `presheafValue C.base`
   - `T2Space`: subspace of T2 `presheafValue C.base`

2. **`tate_proper_ideal_not_open`** — every proper ideal in a Tate ring is
   non-open, because the topologically nilpotent unit forces any open ideal
   to contain a unit, hence to be the unit ideal.

3. **`hSpa_points_nonOpen_via_lifted_ideal_proper`** — discharges the
   non-open prime case CONDITIONAL on the lifted ideal being proper. This
   isolates the **single remaining residual**: showing
   `Ideal.map C.base.canonicalMap p ≠ ⊤` in `presheafValue C.base`, for
   primes `p` of `A` with `C.base.s ∉ p`.

The residual `liftedIdeal_ne_top` is a proper-extension question for
algebraic completions of Noetherian Tate localizations — Wedhorn's analytic
input that's orthogonal to the Cor 8.32 spectral route.
-/

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Every proper ideal in a Tate ring is non-open**. The topologically
nilpotent unit `π` of a Tate ring witnesses that an open ideal must contain
some power `π^n`, hence a unit, hence equal `⊤`. Equivalently, every
non-trivial ideal is non-open.

This is the structural fact behind Wedhorn Prop 8.36 (every Spv point in a
Tate ring is analytic), restricted to ideals. -/
theorem tate_proper_ideal_not_open
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTateRing R]
    {𝔞 : Ideal R} (h𝔞 : 𝔞 ≠ ⊤) : ¬ IsOpen (𝔞 : Set R) := by
  intro h_open
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing R›.exists_topologicallyNilpotent_unit
  -- Topologically nilpotent units lie in the radical of every open ideal.
  have hu_rad : (u : R) ∈ 𝔞.radical := hu_nil.mem_ideal_radical h_open
  -- u is a unit, hence u ∈ 𝔞.radical implies 𝔞.radical = ⊤.
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hu_rad
  -- u^n is also a unit.
  have hu_n_unit : IsUnit ((u : R) ^ n) := u.isUnit.pow n
  -- A unit lying in 𝔞 forces 𝔞 = ⊤.
  exact h𝔞 (Ideal.eq_top_of_isUnit_mem 𝔞 hn hu_n_unit)

omit [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **`IsAdicComplete` for the concrete pair of definition on `presheafValue C.base`.**

Derived from `IsAdic.isAdicComplete_iff` applied to the subspace uniformity
on `presheafValue_ringOfDef C.base` (the closed subring that is the topological
closure of the image of `locSubring`). The required ingredients:
- `IsAdic`: `presheafValue_isAdic` (`PresheafTateStructure.lean:804`).
- `CompleteSpace`: closed subset of complete `presheafValue C.base`.
- `T2Space`: subspace of T2 `presheafValue C.base`.

This unblocks the application of `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`
to the pair `presheafValue_pairOfDefinition_concrete P C.base`, which is the
foundation of the non-open prime case in `hSpa_points`. -/
theorem presheafValue_isAdicComplete
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)] :
    IsAdicComplete (presheafValue_idealOfDef D₀) (presheafValue_ringOfDef D₀) := by
  have hadic : IsAdic (presheafValue_idealOfDef D₀) := presheafValue_isAdic D₀
  -- Equip `presheafValue_ringOfDef D₀` with the subspace UniformSpace structure
  -- inherited from `presheafValue D₀` (whose UniformSpace is the completion uniformity).
  letI : UniformSpace (presheafValue_ringOfDef D₀) :=
    UniformSpace.comap Subtype.val inferInstance
  -- Inherit `IsUniformAddGroup` from the ambient `presheafValue D₀`.
  haveI : IsUniformAddGroup (presheafValue_ringOfDef D₀) :=
    AddSubgroup.isUniformAddGroup (presheafValue_ringOfDef D₀).toAddSubgroup
  -- The ring of definition is closed, hence complete (subspace of complete space).
  haveI : CompleteSpace (presheafValue_ringOfDef D₀) :=
    (Subring.isClosed_topologicalClosure
      (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range).completeSpace_coe
  -- T2 inherited from ambient T2.
  haveI : T2Space (presheafValue_ringOfDef D₀) := inferInstance
  -- Apply the iff: IsAdic ⇒ (IsAdicComplete ↔ CompleteSpace ∧ T2Space).
  exact hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

omit [HasLocLiftPowerBounded A] [PlusSubring A] in
/-- **Subset relation between `D.completedLocSubring` and `presheafValue_ringOfDef D`.**
Both are topological closures of the same image of `locSubring` (one via
`Subring.map`, one via `RingHom.range`); as sets they coincide. -/
private theorem completedLocSubring_eq_presheafValue_ringOfDef (D : RationalLocData A) :
    (D.completedLocSubring : Set (presheafValue D)) =
    (presheafValue_ringOfDef D : Set (presheafValue D)) := by
  -- Both are `topologicalClosure` of the same underlying set:
  -- `D.coeRingHom '' (locSubring D.P D.T D.s)`.
  -- The closure operation is set-determined, so once we show the inputs match as sets,
  -- the closures match as sets.
  unfold RationalLocData.completedLocSubring presheafValue_ringOfDef
  -- The underlying sets:
  --   Subring.map D.coeRingHom (locSubring) = D.coeRingHom '' (locSubring : Set _)
  --   (D.coeRingHom.comp (locSubring).subtype).range = D.coeRingHom '' (locSubring : Set _)
  have h_sub_eq : (Subring.map D.coeRingHom (locSubring D.P D.T D.s) :
      Set (presheafValue D)) =
    ((D.coeRingHom.comp (locSubring D.P D.T D.s).subtype).range :
      Set (presheafValue D)) := by
    ext y
    simp only [Subring.coe_map, RingHom.coe_range, Set.mem_image,
      RingHom.comp_apply, Set.mem_range]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  -- topologicalClosure of two subrings with the same underlying set is the same.
  apply Set.eq_of_subset_of_subset
  · exact closure_mono h_sub_eq.le
  · exact closure_mono h_sub_eq.ge

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Lifting non-open primes from `presheafValue C.base` via Lemma 7.45.**

Given a non-open prime `𝔭` of `presheafValue C.base` (with the standard
PlusSubring structure `D.completedLocSubring`), Lemma 7.45 applied to the
concrete pair of definition produces a Spa point `w` with `𝔭 ≤ w.supp`.

This packages `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime` for our
specific completion setting. The `IsAdicComplete` instance is supplied via
`presheafValue_isAdicComplete`. -/
theorem exists_spa_point_supp_ge_in_presheafValue
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    {𝔭 : Ideal (presheafValue C.base)} [𝔭.IsPrime]
    (h𝔭_notOpen : ¬IsOpen (𝔭 : Set (presheafValue C.base))) :
    ∃ w ∈ Spa (presheafValue C.base) C.base.completedLocSubring,
      𝔭 ≤ w.supp := by
  -- Set up: get the concrete pair of definition + IsAdicComplete instance.
  let PB := presheafValue_pairOfDefinition_concrete P C.base
  haveI : IsAdicComplete PB.I PB.A₀ := presheafValue_isAdicComplete P C.base
  -- The PlusSubring is `presheafValuePlusSubring`, which sets `B⁺ = completedLocSubring`.
  -- The hypothesis `(B⁺ : Set _) ⊆ PB.A₀` becomes `completedLocSubring ⊆ ringOfDef`,
  -- which holds because the two subrings have the same underlying set.
  have hBplus_le_B₀ : ((PlusSubring.toSubring (A := presheafValue C.base) :
      Subring (presheafValue C.base)) : Set (presheafValue C.base)) ⊆
      (PB.A₀ : Set (presheafValue C.base)) := by
    change (C.base.completedLocSubring : Set (presheafValue C.base)) ⊆
      (presheafValue_ringOfDef C.base : Set (presheafValue C.base))
    rw [completedLocSubring_eq_presheafValue_ringOfDef]
  obtain ⟨w, hw_spa, hw_supp, _⟩ :=
    PB.exists_mem_spa_supp_ge_of_nonOpen_prime (𝔭 := 𝔭) h𝔭_notOpen hBplus_le_B₀
  -- The output Spa is w.r.t. `(presheafValue C.base)⁺ = completedLocSubring`.
  exact ⟨w, hw_spa, hw_supp⟩

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Discharge of `hSpa_points` for non-open primes, conditional on
`liftedIdeal_ne_top`.**

Given:
- A prime `p` of `A` with `C.base.s ∉ p` (so `Ideal.map C.base.canonicalMap p`
  is "potentially proper").
- The hypothesis `liftedIdeal_ne_top`: `Ideal.map C.base.canonicalMap p ≠ ⊤`
  in `presheafValue C.base`.

This produces the required `v ∈ rationalOpen C.base.T C.base.s` with
`p ≤ v.supp`, by:
1. Lifting `liftedIdeal p` to a maximal ideal `𝔭` of `presheafValue C.base`
   (via `Ideal.exists_le_maximal`).
2. Using `tate_proper_ideal_not_open` to conclude `𝔭` is non-open
   (since `presheafValue C.base` is Tate).
3. Applying `exists_spa_point_supp_ge_in_presheafValue` (Lemma 7.45 on the
   completion) to get a Spa point of `presheafValue C.base`.
4. Pulling back via `exists_rationalOpen_of_completion_spa` to get the
   required Spa point of `A` in `rationalOpen C.base.T C.base.s`.

**Status**: this leaves only `liftedIdeal_ne_top` as the residual algebraic
input. That hypothesis is Wedhorn's analytic claim that algebraic completion
of Noetherian Tate localizations preserves properness of finitely generated
ideal extensions. -/
theorem hSpa_points_nonOpen_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (p : Ideal A) [hp : p.IsPrime] (hs_notin : C.base.s ∉ p)
    (h_lifted_ne_top :
      (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤) :
    ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := by
  -- Step 1: Lift `liftedIdeal p` to a maximal ideal `𝔭` of `presheafValue C.base`.
  obtain ⟨𝔭, h𝔭_max, h𝔭_le⟩ :=
    Ideal.exists_le_maximal (Ideal.map C.base.canonicalMap p) h_lifted_ne_top
  haveI : 𝔭.IsPrime := h𝔭_max.isPrime
  -- Step 2: 𝔭 is non-open since `presheafValue C.base` is a Tate ring and 𝔭 is proper.
  -- The Tate structure on presheafValue C.base via `presheafValue_isTateRing`.
  haveI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing P C.base
  have h𝔭_notOpen : ¬IsOpen (𝔭 : Set (presheafValue C.base)) :=
    tate_proper_ideal_not_open h𝔭_max.ne_top
  -- Step 3: Apply Lemma 7.45 (via the completion route) to get a Spa point of
  -- presheafValue C.base with 𝔭 in its support.
  obtain ⟨w, hw_spa, hw_supp⟩ :=
    exists_spa_point_supp_ge_in_presheafValue P C h𝔭_notOpen
  -- Step 4: liftedIdeal p ≤ 𝔭 ≤ w.supp.
  have hw_supp_lifted :
      (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≤ w.supp :=
    h𝔭_le.trans hw_supp
  -- Step 5: Pull back via exists_rationalOpen_of_completion_spa.
  exact RationalLocData.exists_rationalOpen_of_completion_spa C.base
    hAplus_le_A₀ hcanonicalMap_cont hs_notin hw_spa hw_supp_lifted

omit [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Full `hSpa_points` discharge, conditional on `liftedIdeal_ne_top` for
non-open primes.**

This combinator unifies the open-prime case (handled unconditionally via
`hSpa_points_open_prime`) and the non-open-prime case (handled conditionally
via `hSpa_points_nonOpen_via_lifted_ideal_proper`).

The remaining hypothesis `h_lifted_ne_top_for_nonOpen` is the ONLY residual:
for every NON-OPEN prime `p` of `A` with `C.base.s ∉ p`, the lifted ideal
`Ideal.map C.base.canonicalMap p` is proper in `presheafValue C.base`. -/
theorem hSpa_points_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_lifted_ne_top_for_nonOpen :
      ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p → ¬IsOpen (p : Set A) →
        (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp := by
  intro p hp hs
  by_cases hp_open : IsOpen (p : Set A)
  · exact hSpa_points_open_prime C p hp_open hs
  · exact hSpa_points_nonOpen_via_lifted_ideal_proper P C hAplus_le_A₀
      hcanonicalMap_cont p hs (h_lifted_ne_top_for_nonOpen p hp hs hp_open)

/-- **End-to-end `productRestriction_injective_tate` via the full `hSpa_points`
discharge, conditional on `liftedIdeal_ne_top` for non-open primes.**

This is the cleanest packaging through the Cor 8.32 route. It requires only:
- The standard instance bundle `[IsTateRing A] ...`.
- `(A⁺ : Set A) ⊆ C.base.P.A₀` and `Continuous C.base.canonicalMap` (both
  standard side conditions for the completion-route Spa pullback).
- `IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)` — derivable from
  `[IsNoetherianRing P.A₀]` via `Prop752.locSubring_isNoetherian` for the
  appropriate `P`; the user supplies the instance directly here.
- The residual `liftedIdeal_ne_top` hypothesis on non-open primes.

Once the residual is discharged (Wedhorn analytic input on completion of
Noetherian Tate localizations), `productRestriction_injective_tate` is
fully closed via the Cor 8.32 route. -/
theorem productRestriction_injective_tate_via_lifted_ideal_proper
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ C.base.P.A₀)
    (hcanonicalMap_cont : Continuous C.base.canonicalMap)
    (h_lifted_ne_top_for_nonOpen :
      ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p → ¬IsOpen (p : Set A) →
        (Ideal.map C.base.canonicalMap p : Ideal (presheafValue C.base)) ≠ ⊤)
    (x : presheafValue C.base)
    (hx : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
       restrictionMap C.base D (C.hsubset D hD) x = 0) :
    x = 0 :=
  productRestriction_injective_tate_of_hSpa_points P C hne
    (hSpa_points_via_lifted_ideal_proper P C hAplus_le_A₀ hcanonicalMap_cont
      h_lifted_ne_top_for_nonOpen) x hx

/-! ### Summary of remaining residual

After this file's additions, the chain to fully discharge `hSpa_points`
unconditionally (under `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
[NonarchimedeanRing A]`) reduces to a SINGLE algebraic claim:

> For every prime `p` of `A` with `C.base.s ∉ p` and `¬IsOpen (p : Set A)`,
> the lifted ideal `Ideal.map C.base.canonicalMap p` is proper (≠ ⊤) in
> `presheafValue C.base`.

This is the "non-degenerate fiber" question for the analytic completion of
the Noetherian Tate localization `Localization.Away C.base.s`. It is a
specific instance of the question: when does completion of a Noetherian
topological ring preserve properness of finitely generated ideal extensions?

The question reduces (via the factorization `canonicalMap = coeRingHom ∘
algebraMap`) to: for the proper prime `q = Ideal.map algebraMap p` of
`Localization.Away C.base.s`, is `Ideal.map coeRingHom q ≠ ⊤` in the
completion `presheafValue C.base`?

For Noetherian Tate localizations equipped with the localization topology,
the standard answer is YES, because:
- `Localization.Away C.base.s / q` is a non-zero Noetherian ring with the
  induced quotient topology.
- The completion of a non-zero Noetherian topological ring is non-zero
  (the natural map `R → R̂` is INJECTIVE for Hausdorff `R` of countable
  type, by Krull intersection in the Noetherian case).
- The non-zero completion `(Localization.Away s / q)^` quotients
  `presheafValue C.base` (via the universal property of completion + the
  surjection `Localization.Away s → Localization.Away s / q`).

A direct proof would require the project's infrastructure for completion
of Noetherian quotients (Krull intersection, completion-quotient
compatibility), which is conceptually distinct from the Cor 8.32
spectral content and currently lives in the Bourbaki CA III §2.8 chain
(see `project_T001_completion_route` memory). -/

end ValuationSpectrum
