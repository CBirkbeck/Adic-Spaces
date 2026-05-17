/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Banach's open mapping theorem for complete metric topological abelian groups

This file contains the **Bourbaki [TG] Ch. III §3 no. 3 Théorème 1** version of
Banach's open mapping theorem, specialised to topological abelian groups. The
classical statement is:

> Let G, H be Hausdorff topological abelian groups whose topologies are defined by
> countable fundamental systems of neighbourhoods of 0. Assume G is complete. Let
> f : G →+ H be a continuous group homomorphism. If f is surjective and H is
> complete, then f is open.

This is the version cited by **Huber** in "*A generalization of formal schemes and
rigid analytic varieties*", Math. Z. 217 (1994), Lemma 2.4(i) (p. 16):

> "In order to prove (i) one can take over without any change the proof of Banach's
> open mapping theorem (cf. **[B1, 1.3.3]**)."

and used implicitly by **BGR §3.7** as a prerequisite (per BGR Introduction p. 5:
"besides the **Open Mapping Theorem for BANACH spaces**, only some basic facts
from commutative algebra are assumed"). It is the substantive analytical input
underlying:

* **Wedhorn 6.16** (Banach's theorem for Tate rings — "Proof. Missing")
* **Wedhorn 6.17** (noetherian ⇔ every ideal closed)
* **Wedhorn 6.18** (unique fg-module topology + continuous + open maps)

The proof structure is the classical Banach argument adapted to the group setting:

1. The source `G` is a Baire space (mathlib instance
   `BaireSpace.of_pseudoEMetricSpace_completeSpace` for complete uniform spaces
   with countably-generated uniformity).
2. For any neighbourhood `U` of 0 in `G`, the image `f(n·U) = n·f(U)` covers `H`
   by countable union (use any countable fundamental system).
3. `H` is Baire ⇒ some `n·f(U)` has nonempty interior ⇒ `f(U) − f(U)` contains a
   neighbourhood of 0 in `H`.
4. Cauchy completeness of `G` lifts the "approximate preimage" to an exact preimage:
   for any element of a small neighbourhood `V` in `H`, build a Cauchy sequence in
   `G` whose image converges to that element; the limit in `G` (using completeness)
   maps into the desired neighbourhood of `f(0) = 0`.
5. Translation-invariance gives openness at every point.

## References

* N. Bourbaki, *Topologie Générale*, Chapter III §3 no. 3 Théorème 1 (the
  group-level Banach open mapping theorem).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994), Lemma 2.4 (p. 16).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis* (Springer 1984),
  §3.7 (Banach algebras) — uses Banach OMT as prerequisite.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, §6.3 Theorem 6.16 (refers out).

## Project status

This file states the theorem and immediate corollaries. The proof is left as
`sorry` — to be discharged as the Layer-1 mathlib gap from the roadmap at
`docs/plans/2026-05-17-wedhorn-618-roadmap.md`.

Once proved, the result is suitable for upstreaming to Mathlib as
`Mathlib.Topology.Algebra.Group.OpenMappingCompleteMetric`.
-/

namespace AddMonoidHom

universe u v

/-- **Banach's open mapping theorem for complete metric topological abelian groups**
(Bourbaki [TG] Ch. III §3 no. 3 Théorème 1; Huber [Hu3] Lemma 2.4(i)).

Let `G, H` be Hausdorff topological abelian groups with countably-generated
uniformities (i.e. metrizable), both complete. Then every continuous surjective
additive group homomorphism `f : G →+ H` is open.

This is the substantive analytical input for Wedhorn 6.16/6.17/6.18 and for the
audit-pass-2 trio in `StructureSheaf.lean`.

**Proof sketch** (Bourbaki):
1. `G` is BaireSpace via complete + countably-generated uniformity.
2. For any neighbourhood `U` of 0 in `G`, `f(n·U)` covers `H` by countable union.
3. `H` Baire ⇒ some `n·f(U)` has nonempty interior ⇒ `f(U) − f(U)` contains nbhd of 0.
4. Cauchy completeness of `G` lifts approximate preimages to exact ones.
5. Translation invariance ⇒ open everywhere.

**Mathlib lemmas needed**:
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` (Baire from complete + countably-generated)
- `Filter.HasBasis.mem_iff`, `nhds_zero` basis lemmas
- `nonempty_interior_of_iUnion_of_closed` (Baire category for closed sets)
- `CauchySeq.tendsto_of_completeSpace` (completeness ⇒ Cauchy converges) -/
theorem isOpenMap_of_completeSpace_of_countablyGenerated
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  sorry

/-- **Corollary — Banach's theorem for surjections.** A continuous surjective
group homomorphism between complete metric topological abelian groups is a
quotient map (open + surjective).

Discharged trivially from `isOpenMap_of_completeSpace_of_countablyGenerated` +
the `IsOpenMap.isQuotientMap` characterization. -/
theorem isQuotientMap_of_completeSpace_of_countablyGenerated
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    Topology.IsQuotientMap f :=
  sorry

/-- **Bourbaki's full any-two-imply-third statement** — the version Wedhorn 6.16
states. Let `G, H` be Hausdorff topological abelian groups with countably-
generated uniformities. Assume `G` is complete. Let `f : G →+ H` be continuous.
Among:
- (a) `H` is complete
- (b) `f` is surjective
- (c) `f` is open

any two imply the third.

(In the project we will mostly use the "(a) ∧ (b) ⇒ (c)" direction, which is
`isOpenMap_of_completeSpace_of_countablyGenerated` above.) -/
theorem banach_two_of_three
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) :
    ((CompleteSpace H ∧ Function.Surjective f) → IsOpenMap f) ∧
    ((CompleteSpace H ∧ IsOpenMap f) → Function.Surjective f) ∧
    ((Function.Surjective f ∧ IsOpenMap f) → CompleteSpace H) :=
  sorry

end AddMonoidHom
