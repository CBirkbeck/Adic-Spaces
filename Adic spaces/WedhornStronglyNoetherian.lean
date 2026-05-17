/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornBanachTheorem
import «Adic spaces».HuberRings
import «Adic spaces».RestrictedPowerSeries
import «Adic spaces».TateAlgebra

/-!
# Wedhorn 6.36 / 6.18 chain — strongly noetherian Tate equivalences

This file ports the audit-pass-2 trio referenced by the Wedhorn-exact
`isSheafy_ofStronglyNoetherianTate` chain in `StructureSheaf.lean`:

* `isStronglyNoetherian_of_isNoetherianRing_isTateRing` — Wedhorn 6.36
  forward direction: noetherian Tate + complete + nonarchimedean ⇒
  strongly noetherian (via Wedhorn 6.18 + Stacks 00MA).
* `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` — for
  strongly noetherian Tate `A`, the principal pair (Wedhorn p.61) has
  noetherian `A₀`.
* `exists_hSpa_points_global_of_stronglyNoetherianTate` — Spa-point
  existence at every prime, via Wedhorn 7.45 noetherian-ring-of-definition
  variant.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934:
  - Def 6.36 (p. 53): strongly noetherian Tate equivalent conditions.
  - Remark 6.37(2) (p. 54): Tate algebras over complete non-arch fields
    are strongly noetherian (cites [BGR] 5.2.6 Thm 1).
  - Remark 6.37(3) (p. 54): noetherian-ring-of-definition ⇒ strongly noetherian.
  - Lemma 7.45 (p. 67): Spa-point at non-open prime.
  - Remark 6.19 (p. 50): principal pair construction.
* Stacks Project, Tag 00MA: I-adic completion of noetherian is noetherian
  (mathlib gap T-MATHLIB-STACKS-00MA, ticket #36).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §5.2.6 Theorem 1: T_n is noetherian (= base case of strongly noetherian
  for k a non-arch field).

## Project roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` Layers 5-6.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn 6.36 forward (= Remark 6.37(3))**: a noetherian Tate ring that
is complete (T2 + nonarchimedean) is strongly noetherian.

**Source** (Wedhorn Remark 6.37(3), p. 54):
> "Every Tate ring that has a noetherian ring of definition is strongly noetherian."

The base case (k=0) is `A` itself noetherian. The inductive step requires
showing `A⟨X⟩` noetherian when `A` is. This is:

* **Algebraic part**: `A⟨X⟩` = I-adic completion of `A[X]` where `I` is the
  ideal of definition. Polynomial extension preserves noetherianness
  (Hilbert basis); I-adic completion preserves noetherianness
  (**Stacks 00MA = T-MATHLIB-STACKS-00MA**, ticket #36 — mathlib gap).
* **Topological part**: the completion topology coincides with the
  restricted-power-series topology (project's existing `TateAlgebra` /
  `RestrictedPowerSeries` infrastructure).

Inductive step iterates k times.

**Depends on**: T-MATHLIB-STACKS-00MA (ticket #36) for the I-adic completion
preservation step. -/
theorem isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    IsStronglyNoetherian A :=
  sorry

/-- **Wedhorn principal-pair A₀ noetherian** (cf. Wedhorn Remark 6.19, p. 50):
for a strongly noetherian Tate ring `A`, the ring of definition `A₀` of the
canonical principal pair (constructive selector `IsTateRing.principalPair`)
is noetherian.

**Source** (Wedhorn Remark 6.19, p. 50):
> "Let `A` be a complete noetherian Tate ring, `A₀` a ring of definition and
> `s ∈ A₀` a topologically nilpotent unit of `A` (such that `A₀` has the
> `sA₀`-adic topology). ... Then `{sⁿM₀ ; n ∈ ℕ}` is a fundamental system
> of open neighborhoods of 0 in `M` for the topology defined in Proposition 6.18."

**Proof outline**:
* The principal pair has `A₀ = closure of (image of polynomial ring in s)`
  where `s` is the topologically nilpotent unit.
* For strongly noetherian Tate `A`, `A₀` itself is noetherian: take the
  Wedhorn 6.18(1) topology on `A` regarded as an `A`-module; the open
  subring `A₀` inherits noetherianness via the descent
  `A₀ ↪ A` + closed-subring-of-noetherian argument.

Strictly, this needs:
* Wedhorn 6.18 (for module-topology uniqueness).
* `A₀ ⊆ A` is open (so the I-adic topology on `A₀` coincides with the
  subspace topology).
* Descent of noetherianness from `A` (or rather from `A⟨X⟩` for some `X`)
  to `A₀` along the localization `A = A₀[1/s]`. -/
theorem isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] :
    IsNoetherianRing ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
  sorry

/-- **Wedhorn principal-pair noetherian — general pair version**: any
`PairOfDefinition A` (not just the principal pair) has noetherian `A₀`,
given strongly noetherian Tate. -/
theorem isNoetherianRing_A₀_of_stronglyNoetherianTate_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) :
    IsNoetherianRing ↥P.A₀ :=
  sorry

/-- **Wedhorn 7.45 globalised**: for a strongly noetherian Tate ring, every
prime `p` of `A` with `s ∉ p` (for any `s ∈ A`) admits a Spa-point `v` whose
support contains `p` and which lies in the rational subset `R(T/s)`.

**Source** (Wedhorn Lemma 7.45, p. 67):
> "Let `A` be a complete affinoid ring. Let `p` be a non-open prime ideal
> of `A`. Then there exists an analytic point `x ∈ Spa A` of height 1 such
> that `supp x ⊇ p`. If `A` has a noetherian ring of definition, we may
> assume in addition that `x` is a discrete valuation and that `supp x = p`."

For our setting (strongly noetherian Tate), the principal pair has
noetherian `A₀` (= `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
above), so the **noetherian-ring-of-definition** case of Wedhorn 7.45
applies directly. The non-open case is handled via the standard
Krull-Akizuki + DVR construction (Wedhorn proves this case explicitly —
not "Missing").

The open-prime case is via trivial valuation (project's existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime`).

**Depends on**: `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`
(audit-pass-2 lemma above) for the noetherian A₀; existing
`exists_spa_point_in_rationalOpen_of_isOpen_prime` for the open case;
existing `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` from
`Lemma745.lean` for the non-open case. -/
theorem exists_hSpa_points_global_of_stronglyNoetherianTate_proof
    [PlusSubring A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp :=
  sorry

end ValuationSpectrum
