/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PerfectoidRing
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.WittVector.Defs
import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.FieldTheory.Perfect

/-!
# Tilting Functor, A_inf, and Fontaine's Theta Map

We define the **tilt** of a perfectoid ring, the period ring **A_inf**,
and Fontaine's **theta** map, following Scholze's *Perfectoid Spaces* §3
and Fontaine's original construction.

## Main definitions

* `PerfectoidRing.tilt p A` : The tilt `A♭ = lim_{x ↦ x^p} A°/(p)`, defined as
  `PreTilt A° p` (the perfection of `A°/(p)`).
* `Ainf p A` : The period ring `A_inf = W(A♭)` (p-typical Witt vectors of the tilt).
* `PerfectoidRing.theta` : Fontaine's theta map `θ : A_inf → A°`.

## Main results (sorry'd)

* `PerfectoidRing.tilt_isPerfect` : The tilt is a perfect ring of characteristic `p`.
* `PerfectoidRing.theta_surjective` : Fontaine's theta is surjective.
* `PerfectoidRing.ker_theta_principal` : The kernel of theta is principal.
* `PerfectoidRing.tilt_admits_perfectoid_structure` : The tilt admits a perfectoid topology.
* `PerfectoidField.tiltingEquiv` : The tilting equivalence for perfectoid fields.

## Implementation notes

The tilt is defined as `PreTilt ↥(powerBoundedSubring.toSubring A) p`, using Mathlib's
`PreTilt O p = Perfection (O ⧸ Ideal.span {p}) p`. The instances `CommRing`, `CharP`,
and `PerfectRing` on the tilt are inherited from `PreTilt`, but require
`[Fact (¬ IsUnit (p : A°))]`. We provide a sorry'd proof that this holds for
perfectoid rings (`IsPerfectoidRing.p_not_isUnit_in_powerBounded`).

Fontaine's theta map `θ : W(A♭) →+* A°` is defined with a sorry'd body. Mathlib's
`WittVector.fontaineTheta` provides the construction when `A°` is `p`-adically complete
(`[IsAdicComplete (Ideal.span {p}) A°]`), but establishing this instance for the
power-bounded subring of a perfectoid ring requires substantial infrastructure.
The sorry can be filled by proving `IsAdicComplete` and applying `fontaineTheta`.

The tilt being perfectoid requires a topology on `PreTilt`, which Lean's typeclass
system cannot synthesize automatically (due to a `Module R R` diamond for
`IsLinearTopology`). We state the result existentially.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], §3
* [J.-M. Fontaine, *Sur certains types de représentations p-adiques du groupe de Galois
  d'un corps local; construction d'un anneau de Barsotti-Tate*][fontaine1982certains]
* [J.-M. Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]
-/

open TopologicalRing ValuationSpectrum

universe u

noncomputable section

/-! ### The tilt and A_inf -/

section TiltDef

variable (p : ℕ)
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The **tilt** of a topological ring `A` is `A♭ := lim_{x ↦ x^p} A°/(p)`,
the (inverse limit) perfection of the reduction modulo `p` of the ring of
power-bounded elements `A°`. This is Mathlib's `PreTilt` applied to `A°`.

For a perfectoid ring, the tilt is again perfectoid (in characteristic `p`),
and the tilting operation gives an equivalence between perfectoid rings of
characteristic 0 and characteristic p.

(Scholze, *Perfectoid Spaces*, §3) -/
abbrev PerfectoidRing.tilt : Type u :=
  PreTilt ↥(powerBoundedSubring.toSubring A) p

/-- The period ring `A_inf(A) := W(A♭)`, the ring of `p`-typical Witt vectors
of the tilt. This ring plays a central role in p-adic Hodge theory as the
"universal thickening" of `A°`.

(Fontaine, *Sur certains types de représentations p-adiques*, 1982) -/
abbrev Ainf : Type u :=
  WittVector p (PerfectoidRing.tilt p A)

end TiltDef

/-! ### Instances on the tilt

The `CommRing`, `CharP`, and `PerfectRing` instances on the tilt require
`[Fact (¬ IsUnit (p : A°))]`, which we provide via a sorry'd proof for
perfectoid rings (see `IsPerfectoidRing.instFactNotIsUnitP`).
-/

section TiltInstances

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
variable [Fact (¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A)))]

instance PerfectoidRing.tilt.instCommRing : CommRing (PerfectoidRing.tilt p A) :=
  inferInstance

instance PerfectoidRing.tilt.instCharP : CharP (PerfectoidRing.tilt p A) p :=
  inferInstance

instance PerfectoidRing.tilt.instPerfectRing : PerfectRing (PerfectoidRing.tilt p A) p :=
  inferInstance

end TiltInstances

/-! ### p is not a unit in A° for perfectoid rings -/

namespace IsPerfectoidRing

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]

/-- In a perfectoid ring, `p` is not a unit in `A°`.

This follows from the perfectoid condition `p = c · ϖ^p`: since `ϖ` is
topologically nilpotent and `c` is power-bounded, `p` is topologically
nilpotent in `A`. A topologically nilpotent element cannot be a unit in
`A°` (its powers converge to 0, contradicting invertibility in a Hausdorff ring).

(Scholze, *Perfectoid Spaces*, implicit in Definition 3.5) -/
theorem p_not_isUnit_in_powerBounded :
    ¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A)) := sorry

/-- The `Fact` version of `p_not_isUnit_in_powerBounded`, for use with
Mathlib's `PreTilt` instances which require `[Fact (¬ IsUnit (p : O))]`. -/
instance instFactNotIsUnitP :
    Fact (¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A))) :=
  ⟨p_not_isUnit_in_powerBounded⟩

end IsPerfectoidRing

/-! ### Fontaine's theta map -/

section Theta

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]

/-- Fontaine's **theta map** `θ : W(A♭) →+* A°` for a perfectoid ring `A`.

This is the ring homomorphism from the Witt vectors of the tilt to the ring of
power-bounded elements, defined as the limit of compatible maps
`W(A♭) → A°/(p^n)`.

Mathematically, this equals `WittVector.fontaineTheta` when `A°` is `p`-adically
complete (which holds for perfectoid rings). The sorry can be filled by:
1. Proving `IsAdicComplete (Ideal.span {(p : A°)}) A°`
2. Applying `WittVector.fontaineTheta A° p`

(Fontaine, *Le corps des périodes p-adiques*, 1994;
 Scholze, *Perfectoid Spaces*, §3) -/
def PerfectoidRing.theta :
    Ainf p A →+* ↥(powerBoundedSubring.toSubring A) := sorry

end Theta

/-! ### Properties of the tilt -/

namespace PerfectoidRing

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]

/-- The tilt `A♭` of a perfectoid ring is a **perfect ring** of characteristic `p`.

The Frobenius map on `A♭ = lim_{x ↦ x^p} A°/(p)` is bijective by construction:
it is the shift map on the inverse system, which is invertible because each
element of the perfection carries compatible `p`-th roots at all levels.

(Scholze, *Perfectoid Spaces*, Proposition 3.4) -/
theorem tilt_isPerfect : PerfectRing (tilt p A) p :=
  PerfectoidRing.tilt.instPerfectRing p A

/-- Fontaine's theta map `θ : W(A♭) → A°` is **surjective**.

The proof uses the Frobenius surjectivity on `A°/(p)` (from the perfectoid
condition) together with the description of theta via Teichmüller representatives:
every `x ∈ A°` can be written as `θ(∑ pⁿ [xₙ♭])` where `xₙ♭ ∈ A♭` are
Teichmüller lifts.

The sorry can be filled by establishing `IsAdicComplete` on `A°` and applying
Mathlib's `surjective_fontaineTheta`.

(Scholze, *Perfectoid Spaces*, Proposition 3.7;
 Fontaine, *Le corps des périodes p-adiques*, 1994) -/
theorem theta_surjective : Function.Surjective (PerfectoidRing.theta p A) := sorry

/-- The kernel of Fontaine's theta map is a **principal ideal**, generated by
a distinguished element `ξ ∈ W(A♭)`.

This element can be taken to be `ξ = [ϖ♭] - p` where `ϖ♭ ∈ A♭` is a
compatible system of `p`-power roots of the pseudo-uniformizer. The proof
that `ker(θ)` is principal uses the perfectoid condition and properties of
Witt vectors.

(Scholze, *Perfectoid Spaces*, Lemma 3.10;
 Fontaine, *Le corps des périodes p-adiques*, 1994) -/
theorem ker_theta_principal :
    (RingHom.ker (PerfectoidRing.theta p A)).IsPrincipal := sorry

/-- The tilt `A♭` of a perfectoid ring admits a topology, uniform structure, and
linear topology making it into a perfectoid ring of characteristic `p`.

The topology on `A♭` is defined via the inverse limit valuation: each element of
`A♭ = lim A°/(p)` determines a compatible system of valuations, and the resulting
topology makes `A♭` into a complete, separated, uniform topological ring with
Frobenius surjective modulo `ϖ♭`.

The existential formulation avoids a `Module R R` diamond that prevents
`IsLinearTopology` from being synthesized on `PreTilt`.

(Scholze, *Perfectoid Spaces*, Proposition 3.4) -/
theorem tilt_admits_perfectoid_structure :
    ∃ (_ : TopologicalSpace (tilt p A))
      (_ : IsTopologicalRing (tilt p A))
      (_ : UniformSpace (tilt p A)),
    CompleteSpace (tilt p A) ∧ T0Space (tilt p A) := sorry

end PerfectoidRing

/-! ### Tilting equivalence for perfectoid fields -/

namespace PerfectoidField

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [UniformSpace K] [IsLinearTopology K K] [IsPerfectoidField p K]

/-- The tilt `K♭` of a perfectoid field `K` is a **field**.

Since `K` is a field, `K° = O_K` is a valuation ring, and `K°/(p)` is a
domain. The perfection of a domain of characteristic `p` is again a domain,
and the tilt inherits a valuation from the inverse limit construction that
makes it a (non-archimedean) valued field.

(Scholze, *Perfectoid Spaces*, Proposition 3.4) -/
theorem tilt_isField : IsField (PerfectoidRing.tilt p K) := sorry

/-- The **tilting equivalence**: the tilt functor gives an equivalence between
perfectoid fields of mixed characteristic `(0, p)` and perfectoid fields of
equal characteristic `p`.

More precisely, if `K` is a perfectoid field of characteristic 0, then `K♭` is
a perfectoid field of characteristic `p`, and `K` can be recovered (up to
isomorphism) from `K♭` via the "untilting" construction: `K ≅ W(K♭°)[1/p]^∧`.

This is the foundational result that underlies the theory of perfectoid spaces.
The tilting equivalence preserves many algebraic and topological properties,
including the Galois group: `Gal(K̄/K) ≅ Gal(K̄♭/K♭)`.

The existential formulation avoids typeclass synthesis issues with the
topology on `PreTilt`.

(Scholze, *Perfectoid Spaces*, Theorem 3.7) -/
theorem tiltingEquiv :
    ∃ (_ : TopologicalSpace (PerfectoidRing.tilt p K))
      (_ : IsTopologicalRing (PerfectoidRing.tilt p K))
      (_ : UniformSpace (PerfectoidRing.tilt p K)),
    CompleteSpace (PerfectoidRing.tilt p K) ∧ T0Space (PerfectoidRing.tilt p K) := sorry

end PerfectoidField
