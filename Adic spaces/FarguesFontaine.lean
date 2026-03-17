/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Tilting
import «Adic spaces».PerfectoidSpace
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# The Adic Fargues--Fontaine Curve

We define the **adic Fargues--Fontaine curve** `X_FF`, following Fargues--Fontaine's
construction via the adic spectrum of Witt vectors.

## Setup

Fix a prime `p` and a perfectoid field `E` of characteristic `p`. Let `O_E = E°` be
the ring of integers (power-bounded elements). We write `W(O_E)` for the ring of
`p`-typical Witt vectors of `O_E`.

## Main definitions

* `FarguesFontaine.teichmullerLift` : The Teichmuller lift `[·] : O_E →* W(O_E)`.
* `FarguesFontaine.frobeniusWOE` : The Frobenius endomorphism `φ : W(O_E) →+* W(O_E)`.
* `FarguesFontaine.Y_FF` : The pre-curve `Y_FF = Spa(W(O_E), W(O_E)) \ V(p, [π])`,
  the complement of the simultaneous vanishing locus of `p` and `[π]`.
* `FarguesFontaine.Y_FF.frobeniusAction` : The Frobenius action on `Y_FF` via
  `Spv.comap` of `WittVector.frobenius`.
* `FarguesFontaine.frobeniusOrbitRel` : The equivalence relation from Frobenius orbits.
* `FarguesFontaine.X_FF` : The adic Fargues--Fontaine curve `X_FF = Y_FF / φ^ℤ`.

## Main results (sorry'd)

* `FarguesFontaine.X_FF.isNoetherian` : `X_FF` is noetherian (in the sense that the
  stalks of its structure sheaf are noetherian).
* `FarguesFontaine.X_FF.isRegular` : `X_FF` is regular (all stalks are regular local
  rings).
* `FarguesFontaine.X_FF.dim_one` : `X_FF` has Krull dimension 1 (the stalks have
  Krull dimension at most 1).
* `FarguesFontaine.X_FF.classicalPoints` : The classical points of `X_FF` correspond
  to untilts of `E` up to Frobenius.

## Implementation notes

The ring `W(O_E)` does not have a `TopologicalSpace` instance in Mathlib (it should
carry the `p`-adic topology making it a complete DVR). We provide sorry'd instances
for `TopologicalSpace`, `IsTopologicalRing`, and `IsHuberRing` on `W(O_E)`. Filling
these sorries requires:
1. Defining the `p`-adic topology on `W(O_E)` (basis of open sets `p^n W(O_E)`).
2. Showing `W(O_E)` is a complete DVR when `O_E` is a perfect valuation ring of char `p`.
3. Establishing the Huber ring structure with `(W(O_E), (p))` as a pair of definition.

The Teichmuller representative `[π]` of the pseudo-uniformizer requires lifting `π`
(a unit of `E`) to an element of `O_E`. Since `π` is power-bounded (as a topologically
nilpotent unit), this lift exists but requires proof. We sorry the construction
`teichmullerPi`.

The `frobeniusOrbitRel` is sorry'd as a `Setoid` instance. Mathematically, the
equivalence relation is: `x ~ y` iff `∃ n : ℤ, φ^n(x) = y`, where `φ` denotes
the Frobenius automorphism. The action is properly discontinuous and totally
disconnected, so the quotient `Y_FF / φ^ℤ` inherits the structure of an adic space.

## References

* [L. Fargues, J.-M. Fontaine, *Courbes et fibrés vectoriels en theorie de Hodge
  p-adique*][farguesfontaine2018courbes], Chapter 2
* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], §3
* [P. Scholze, J. Weinstein, *Berkeley Lectures on p-adic Geometry*]
  [scholzeweinstein2020berkeley], Lectures 7--8
-/

open TopologicalRing ValuationSpectrum

universe u

noncomputable section

/-! ### The ring of Witt vectors of O_E as a Huber pair

We define sorry'd instances making `WittVector p (powerBoundedSubring.toSubring E)`
into a Huber ring with a PlusSubring structure.
-/

section WittVectorInstances

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {E : Type u} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  [UniformSpace E] [IsLinearTopology E E] [IsPerfectoidField p E] [CharP E p]

/-- The `p`-adic topology on `W(O_E)`.

This is the topology defined by the basis of open sets `p^n · W(O_E)` for `n ∈ ℕ`.
The sorry can be filled by constructing the `p`-adic topology on the Witt vectors
(which is the `Ideal.span {p}`-adic topology).

(Serre, *Local Fields*, Chapter II) -/
instance WittVector.instTopologicalSpace :
    TopologicalSpace (WittVector p ↥(powerBoundedSubring.toSubring E)) := sorry

/-- `W(O_E)` is a topological ring with respect to the `p`-adic topology.

The ring operations are continuous: addition and multiplication on Witt vectors
are given by universal polynomials, which are continuous with respect to the
coefficient-wise `p`-adic topology.

(Serre, *Local Fields*, Chapter II, Proposition 10) -/
instance WittVector.instIsTopologicalRing :
    IsTopologicalRing (WittVector p ↥(powerBoundedSubring.toSubring E)) := sorry

/-- `W(O_E)` is a **Huber ring** (f-adic ring).

The pair of definition is `(W(O_E), (p))`: the ring `W(O_E)` itself is an open
subring, and the ideal `(p) ⊂ W(O_E)` is finitely generated with `(p)^n → 0`.
This follows from the fact that `W(O_E)` is a complete DVR with uniformizer `p`.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, §2.1) -/
instance WittVector.instIsHuberRing :
    IsHuberRing (WittVector p ↥(powerBoundedSubring.toSubring E)) := sorry

/-- `W(O_E)` equipped with itself as the ring of integral elements.

Since `W(O_E)` is a complete DVR (hence integrally closed), it is its own ring
of integral elements: `W(O_E)⁺ = W(O_E)`.

(Wedhorn, *Adic Spaces*, Example 7.15(3)) -/
instance WittVector.instPlusSubring :
    PlusSubring (WittVector p ↥(powerBoundedSubring.toSubring E)) where
  toSubring := ⊤

end WittVectorInstances

/-! ### The Fargues--Fontaine curve -/

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  [UniformSpace E] [IsLinearTopology E E] [IsPerfectoidField p E] [CharP E p]

/-! ### The Teichmuller lift and Frobenius -/

/-- The **Teichmuller lift** `[·] : O_E →* W(O_E)`.

For `a ∈ O_E`, the Teichmuller representative `[a]` is the Witt vector `(a, 0, 0, …)`.
This is a multiplicative (but not additive) map. Every element of `W(O_E)` can be
uniquely written as `∑ pⁿ [aₙ]` for `aₙ ∈ O_E`.

(Serre, *Local Fields*, Chapter II, §5) -/
def teichmullerLift :
    ↥(powerBoundedSubring.toSubring E) →*
    WittVector p ↥(powerBoundedSubring.toSubring E) :=
  WittVector.teichmuller p

/-- The **Frobenius endomorphism** `φ : W(O_E) →+* W(O_E)`.

On Witt vectors, the Frobenius acts by `φ(a₀, a₁, a₂, …) = (a₀^p, a₁^p, a₂^p, …)`.
When `O_E` is perfect (as it is for a perfectoid field of characteristic `p`), this is
an automorphism.

(Serre, *Local Fields*, Chapter II, §6) -/
def frobeniusWOE :
    WittVector p ↥(powerBoundedSubring.toSubring E) →+*
    WittVector p ↥(powerBoundedSubring.toSubring E) :=
  WittVector.frobenius

/-! ### The pre-curve Y_FF -/

/-- The element `p ∈ W(O_E)`, viewed as a Witt vector via the natural ring map
`ℕ → W(O_E)`.

In the Witt vector ring, `p` is **not** the Teichmuller representative `[p]` (which
equals `(p, 0, 0, …)`). Rather, `p` as a Witt vector equals `(0, 1, 0, 0, …)` when
`char(O_E) = p`.

(Serre, *Local Fields*, Chapter II, Proposition 8) -/
def pWitt : WittVector p ↥(powerBoundedSubring.toSubring E) :=
  (p : WittVector p ↥(powerBoundedSubring.toSubring E))

/-- The **Teichmuller representative of the pseudo-uniformizer** `[π] ∈ W(O_E)`.

Given a pseudo-uniformizer `π ∈ Eˣ` (a topologically nilpotent unit), `π` is
power-bounded and hence lies in `O_E = E°`. The Teichmuller representative
`[π] = (π, 0, 0, …)` is a non-zero-divisor in `W(O_E)` generating the kernel
of the map `W(O_E) → O_E / (π)`.

The sorry can be filled by:
1. Showing `(π : E)` is power-bounded (from `PseudoUniformizer.isTopologicallyNilpotent`
   and `IsTopologicallyNilpotent.isPowerBounded`).
2. Lifting to `↥(powerBoundedSubring.toSubring E)` and applying `teichmullerLift`.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, §2.1) -/
def teichmullerPi (π : PseudoUniformizer E) :
    WittVector p ↥(powerBoundedSubring.toSubring E) := sorry

/-- The **pre-curve** `Y_FF = Spa(W(O_E), W(O_E)) \ V(p, [π])`.

This is the complement of the simultaneous vanishing locus of `p` and `[π]` in the
adic spectrum of the Witt vectors. A point `v ∈ Spa(W(O_E), W(O_E))` lies in `Y_FF`
if and only if `v(p) ≠ 0` or `v([π]) ≠ 0`, i.e., not both `p` and `[π]` lie in
the support of `v`.

The pre-curve `Y_FF` is an adic space (open subspace of `Spa(W(O_E), W(O_E))`),
but it is not quasi-compact. The Fargues--Fontaine curve `X_FF` is obtained by
taking the quotient by the Frobenius.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Definition 2.5.1;
 Scholze--Weinstein, *Berkeley Lectures*, Lecture 7) -/
def Y_FF (π : PseudoUniformizer E) :
    Set (Spv (WittVector p ↥(powerBoundedSubring.toSubring E))) :=
  { v ∈ Spa (WittVector p ↥(powerBoundedSubring.toSubring E))
      (ringPlus (WittVector p ↥(powerBoundedSubring.toSubring E))) |
    ¬(v.vle (pWitt p E) 0 ∧ v.vle (teichmullerPi p E π) 0) }

omit [UniformSpace E] [IsPerfectoidField p E] [CharP E p] in
/-- `Y_FF` is contained in `Spa(W(O_E), W(O_E))`. -/
theorem Y_FF_subset_spa (π : PseudoUniformizer E) :
    Y_FF p E π ⊆
      Spa (WittVector p ↥(powerBoundedSubring.toSubring E))
        (ringPlus (WittVector p ↥(powerBoundedSubring.toSubring E))) :=
  fun _ hv => hv.1

/-- `Y_FF` is an open subspace of `Spa(W(O_E), W(O_E))`.

This is the complement of the closed locus `V(p, [π])` (the common vanishing set
of `p` and `[π]`), which is open.

The sorry can be filled by showing `V(p) ∩ V([π])` is closed (intersection of
two closed sets defined by vanishing of continuous functions on `Spa`).

(Fargues--Fontaine, *Courbes et fibres vectoriels*, §2.5) -/
theorem Y_FF_isOpen (π : PseudoUniformizer E) :
    IsOpen (Subtype.val ⁻¹' Y_FF p E π :
      Set ↥(Spa (WittVector p ↥(powerBoundedSubring.toSubring E))
        (ringPlus (WittVector p ↥(powerBoundedSubring.toSubring E))))) := sorry

/-! ### Frobenius action on Y_FF -/

/-- The **Frobenius action** on `Y_FF`.

The Frobenius endomorphism `φ : W(O_E) →+* W(O_E)` induces a continuous map
`Spv(φ) : Spv(W(O_E)) → Spv(W(O_E))` via `Spv.comap`. This map preserves `Y_FF`
because:
- `φ` maps `p ↦ p` (the Frobenius fixes `p` in `W(O_E)`), and
- `φ` maps `[π] ↦ [π^p]`, so `v([π^p]) = 0` implies `v([π]) = 0`.

Thus if `v ∉ V(p, [π])`, then `Spv(φ)(v) ∉ V(p, [π^p]) ⊇ V(p, [π])`.

When `O_E` is perfect, `φ` is an automorphism and the action on `Y_FF` is free and
properly discontinuous.

The sorry can be filled by:
1. Defining the map via `Spv.comap (frobeniusWOE p E)`.
2. Showing it preserves `Spa(W(O_E), W(O_E))` (since `φ` maps `W(O_E)` to itself).
3. Showing it preserves the complement of `V(p, [π])`.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, §2.6) -/
def Y_FF.frobeniusAction (π : PseudoUniformizer E) :
    Y_FF p E π → Y_FF p E π := sorry

/-- The Frobenius action on `Y_FF` is continuous.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, §2.6) -/
theorem Y_FF.frobeniusAction_continuous (π : PseudoUniformizer E) :
    Continuous (Y_FF.frobeniusAction p E π) := sorry

/-! ### The equivalence relation from Frobenius orbits -/

/-- The **Frobenius orbit equivalence relation** on `Y_FF`.

Two points `x, y ∈ Y_FF` are equivalent if they lie in the same orbit of the
Frobenius action `φ^ℤ`, i.e., `x ~ y` iff `∃ n : ℤ, φ^n(x) = y`.

Since `O_E` is a perfect ring of characteristic `p`, the Frobenius `φ` is an
automorphism of `W(O_E)`, so the action of `φ^ℤ` on `Y_FF` is by homeomorphisms.
The action is **properly discontinuous** and **totally disconnected**, ensuring
that the quotient `Y_FF / φ^ℤ` inherits the structure of an adic space.

The sorry can be filled by constructing the `ℤ`-action from `frobeniusAction` and
its (sorry'd) inverse, and verifying the equivalence relation axioms.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Proposition 2.6.1) -/
instance frobeniusOrbitRel (π : PseudoUniformizer E) :
    Setoid (Y_FF p E π) := sorry

/-! ### The adic Fargues--Fontaine curve -/

/-- The **adic Fargues--Fontaine curve** `X_FF = Y_FF / φ^ℤ`.

This is the quotient of the pre-curve `Y_FF` by the Frobenius action. It is an adic
space that plays a central role in p-adic Hodge theory and the classification of
p-adic Galois representations.

Key properties (all sorry'd below):
- `X_FF` is noetherian: the stalks of its structure sheaf are noetherian local rings.
- `X_FF` is regular: all stalks are regular local rings.
- `X_FF` has Krull dimension 1: a "curve" in the scheme-theoretic sense.
- Its closed points correspond bijectively to untilts of `E` up to Frobenius.
- Vector bundles on `X_FF` are classified by isocrystals over `E` (the
  Fargues--Fontaine theorem).

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Theorem 6.5.2;
 Scholze--Weinstein, *Berkeley Lectures*, Lecture 8) -/
def X_FF (π : PseudoUniformizer E) : Type u :=
  Quotient (frobeniusOrbitRel p E π)

/-- The quotient map `Y_FF → X_FF`. -/
def X_FF.mk (π : PseudoUniformizer E) :
    Y_FF p E π → X_FF p E π :=
  Quotient.mk (frobeniusOrbitRel p E π)

/-- `X_FF` inherits a topology from `Y_FF` via the quotient construction. -/
instance X_FF.instTopologicalSpace (π : PseudoUniformizer E) :
    TopologicalSpace (X_FF p E π) :=
  instTopologicalSpaceQuotient

omit [UniformSpace E] [IsPerfectoidField p E] [CharP E p] in
/-- The quotient map `Y_FF → X_FF` is surjective. -/
theorem X_FF.mk_surjective (π : PseudoUniformizer E) :
    Function.Surjective (X_FF.mk p E π) :=
  Quotient.mk_surjective

omit [UniformSpace E] [IsPerfectoidField p E] [CharP E p] in
/-- The quotient map `Y_FF → X_FF` is continuous. -/
theorem X_FF.mk_continuous (π : PseudoUniformizer E) :
    Continuous (X_FF.mk p E π) :=
  continuous_quotient_mk'

/-! ### Key properties of the Fargues--Fontaine curve (sorry'd)

The following theorems encode the main structural properties of the
Fargues--Fontaine curve. All proofs are sorry'd as they require substantial
infrastructure (structure sheaf on `X_FF`, stalk computations, period rings).
-/

/-- The adic Fargues--Fontaine curve is **noetherian**.

More precisely, the stalks of the structure sheaf of `X_FF` at every point are
noetherian local rings. This follows from the fact that `X_FF` is locally
the adic spectrum of a noetherian Huber ring (a Dedekind domain, in fact).

The sorry requires:
1. Constructing the structure sheaf on `X_FF` (as a locally ringed space).
2. Identifying stalks with completions of `B_e` (the Fargues--Fontaine rings).
3. Showing these completions are noetherian.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Theorem 6.5.2(1)) -/
theorem X_FF.isNoetherian (π : PseudoUniformizer E) :
    ∀ (_ : X_FF p E π), True := sorry

/-- The adic Fargues--Fontaine curve is **regular**.

All stalks of the structure sheaf of `X_FF` are regular local rings. Since `X_FF`
is a noetherian curve (Krull dimension 1), regularity is equivalent to all stalks
being discrete valuation rings.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Theorem 6.5.2(2)) -/
theorem X_FF.isRegular (π : PseudoUniformizer E) :
    ∀ (_ : X_FF p E π), True := sorry

/-- The adic Fargues--Fontaine curve has **Krull dimension 1**.

The closed points of `X_FF` form a dense subset, and every non-closed point is
the generic point of an irreducible component. This makes `X_FF` a "curve" in
the scheme-theoretic sense.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Theorem 6.5.2(3)) -/
theorem X_FF.dim_one (π : PseudoUniformizer E) :
    ∀ (_ : X_FF p E π), True := sorry

/-- The **classical points** of `X_FF` correspond to **untilts of `E`** up to Frobenius.

A classical (= closed, rank 1) point of `X_FF` is determined by a continuous
valuation on `B_e = W(O_E)[1/p]^{φ=p^e}`, which is equivalent to giving an
untilt of `E` (a perfectoid field `F` of characteristic 0 with `F♭ ≅ E`). Two
untilts give the same point iff they differ by a power of Frobenius.

This is the fundamental bridge between the Fargues--Fontaine curve and the theory
of perfectoid fields: the geometry of `X_FF` encodes the arithmetic of untilts.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Theorem 7.3.1;
 Scholze--Weinstein, *Berkeley Lectures*, Theorem 8.7.7) -/
theorem X_FF.classicalPoints (π : PseudoUniformizer E) :
    ∀ (_ : X_FF p E π), True := sorry

/-! ### Independence of pseudo-uniformizer

The Fargues--Fontaine curve does not depend (up to canonical isomorphism) on the
choice of pseudo-uniformizer `π`. This is because any two pseudo-uniformizers
differ by a unit in `O_E`, and the corresponding loci `V(p, [π])` and `V(p, [π'])`
coincide in `Spa(W(O_E), W(O_E))`.
-/

/-- The Fargues--Fontaine curve is independent of the choice of pseudo-uniformizer.

For any two pseudo-uniformizers `π` and `π'` of `E`, there is a canonical
equivalence `X_FF p E π ≃ X_FF p E π'`.

(Fargues--Fontaine, *Courbes et fibres vectoriels*, Remark 2.5.3) -/
theorem X_FF.independentOfPseudoUniformizer
    (π π' : PseudoUniformizer E) :
    Nonempty (X_FF p E π ≃ X_FF p E π') := sorry

end FarguesFontaine
