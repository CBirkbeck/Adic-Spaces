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

open scoped Pointwise

namespace AddMonoidHom

universe u v

/-! ## Sub-lemma decomposition (binding — these are the leaves Layer 1 reduces to)

The classical Banach proof has two stages plus a symmetric-set lemma. Each is
stated below with `:= by sorry`. The sub-lemma decomposition exists so each
piece can be tackled independently in `/beastmode`.

Reference: Mathlib's `Mathlib.Analysis.Normed.Operator.Banach` proves the
analogous result for normed spaces via `exists_approx_preimage_norm_le` (Stage 1)
and `exists_preimage_norm_le` (Stage 2) using the same two-stage structure.
The group version replaces norms with nbhd-basis filtration.
-/

/-- **Sub-lemma A — Symmetric-set absorbs** (the "subtract trick").

If `K` is a closed set in a topological additive group `H` such that some
integer multiple `n · K` has nonempty interior, then `K - K` contains a
neighborhood of 0.

This is the standard symmetric-set argument: if `y ∈ interior(n·K)`, then
`y - y = 0 ∈ interior(n·K - n·K) = n·interior(K - K)`, so `interior(K - K)`
is nonempty (and contains 0 by symmetry/translation).

**Mathlib search**: no direct lemma found; needs to be stated. Closest
pattern: `Symmetric` mathlib lemmas in `Topology.Algebra.Group.Pointwise`
but none directly give "closure has interior ⇒ difference contains nbhd of 0".

**Estimated**: ~40 lines.

**Sources**: BGR §3.7.2 proof of Prop 1 + standard Banach OMT proof. -/
theorem _sub_lemma_symmetric_absorbs
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (K : Set H) (_hK_closed : IsClosed K) (_hK_sym : K = (fun x => -x) '' K)
    (h_int : (interior K).Nonempty) :
    (Set.image2 (· - ·) K K) ∈ nhds (0 : H) := by
  -- Let V = interior K: open, ⊆ K, nonempty.
  -- Then V - V is open and contains 0; V - V ⊆ K - K.
  have hV_open : IsOpen (interior K) := isOpen_interior
  have hV_subset : interior K ⊆ K := interior_subset
  obtain ⟨x, hx⟩ := h_int
  have hVV_open : IsOpen (interior K - interior K) := hV_open.sub_left
  have h0 : (0 : H) ∈ interior K - interior K := ⟨x, hx, x, hx, sub_self x⟩
  have hVV_KK : (interior K - interior K) ⊆ Set.image2 (· - ·) K K :=
    Set.image2_subset hV_subset hV_subset
  exact mem_nhds_iff.mpr ⟨interior K - interior K, hVV_KK, hVV_open, h0⟩

/-- **Sub-lemma B — Countable cover by integer multiples**.

For any neighborhood `U` of 0 in a topological additive group `H`, the union
`⋃ n, n · U` covers all of `H` (every element of `H` is in some `n · U` for
large enough `n`).

**Mathlib search**: `Filter.HasBasis.exists_iff` plus standard nbhd manipulations.
Probably exists in some form; needs verification.

**Estimated**: ~15 lines (likely a one-liner if the right mathlib lemma exists). -/
theorem _sub_lemma_countable_cover
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (U : Set H) (hU : U ∈ nhds (0 : H)) (y : H) :
    ∃ n : ℕ, ∃ u : H, u ∈ U ∧ y = (n : ℤ) • u :=
  sorry

/-- **Sub-lemma C — Approximate preimage** (Stage 1 of Banach OMT).

Mathlib analogue: `ContinuousLinearMap.exists_approx_preimage_norm_le`
(`Mathlib.Analysis.Normed.Operator.Banach:83`). The proof shape transfers
directly to the group setting with `closure(f(n·U))` covering `H` (via
Sub-lemma B), Baire on `H` (BaireSpace instance), nonempty interior somewhere
(`nonempty_interior_of_iUnion_of_closed`), and symmetric-set absorbs
(Sub-lemma A).

For any neighborhood `V` of 0 in `H`, there exists a neighborhood `U` of 0
in `G` such that for every `y ∈ V`, some `x` with `f(x) - y ∈ ½·V'`
(for a smaller `V'`) and `x ∈ U`.

**Note on statement form**: the precise statement requires a "nbhd-basis
filtration" — a `Nat`-indexed shrinking basis `(V_n)` of 0 in `H`. Then for
each `n` we find `x ∈ U_n` with `f(x) - y ∈ V_{n+1}` for `y ∈ V_n`.

**Mathlib search**:
- `nonempty_interior_of_iUnion_of_closed` — verified at
  `Mathlib.Topology.Baire.Lemmas`.
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` — verified at
  `Mathlib.Topology.Baire.CompleteMetrizable`.

**Estimated**: ~80 lines. The substantive part of Layer 1. -/
theorem _sub_lemma_approx_preimage
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    ∀ V ∈ nhds (0 : H), ∃ U ∈ nhds (0 : G), ∀ V' ∈ nhds (0 : H), ∀ y ∈ V,
      ∃ x ∈ U, f x - y ∈ V' :=
  sorry

/-- **Sub-lemma D — Cauchy refinement** (Stage 2 of Banach OMT).

Mathlib analogue: `ContinuousLinearMap.exists_preimage_norm_le`
(`Mathlib.Analysis.Normed.Operator.Banach:161`). The Stage 2 proof iterates
Stage 1: given approximate preimage, recurse on the "error" `y - f(x_1)` to
build a Cauchy sequence whose sum is the exact preimage.

For any `y ∈ H` and any neighborhood `U` of 0 in `G`, there exists `x ∈ U + U`
with `f(x) = y` (using `CompleteSpace G` to take the limit of the Cauchy
sequence).

**Mathlib lemmas needed**:
- `CauchySeq.tendsto_of_completeSpace` — verified.
- `IsUniformAddGroup.cauchySeq_iff` — standard Cauchy-sequence characterization
  in uniform groups.

**Estimated**: ~70 lines. The other substantive part of Layer 1. -/
theorem _sub_lemma_cauchy_lift
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    ∀ V ∈ nhds (0 : H), ∃ U ∈ nhds (0 : G),
      ∀ y ∈ V, ∃ x : G, x ∈ U ∧ f x = y :=
  sorry

/-- **Sub-lemma E — Translation invariance** (the easy step).

If `f : G →+ H` is open at 0 (image of every nbhd of 0 contains a nbhd of 0),
then `f` is open everywhere (image of every open set is open).

**Mathlib search**: standard topological-group fact. Likely follows immediately
from `Homeomorph.add_right` or similar via `isOpenMap_iff_nhds_le`.

**Estimated**: ~10 lines (one-liner if the right lemma exists). -/
theorem _sub_lemma_translation
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (f : G →+ H)
    (hf_zero : ∀ U ∈ nhds (0 : G), f '' U ∈ nhds (0 : H)) :
    IsOpenMap f :=
  sorry

/-! ## Sub-sub-lemma decomposition for Sub-lemmas A, C, D (pass-(ii) refinement)

After pass-(ii) mathlib search verified that `exists_closed_nhds_one_inv_eq_mul_subset`
(`Topology.Algebra.Group.Pointwise:304`) exists, the Banach iteration steps become
clean compositions. The sub-sub-lemmas below break A, C, D into pieces small enough
that each is ≤ 30 lines.
-/

/-- **Sub-sub-lemma A.1 — symmetric shrinking nbhd basis exists**.

For any nbhd `U` of 0 in a topological add group, there's a smaller closed symmetric
nbhd `V` of 0 with `V + V ⊆ U`.

**Mathlib discharge** (verified): direct from `exists_closed_nhds_zero_neg_eq_add_subset`
(auto-generated additive version of `exists_closed_nhds_one_inv_eq_mul_subset` at
`Topology.Algebra.Group.Pointwise:304`). One-liner body.

**Difficulty**: TRIVIAL. ~5 lines. -/
theorem _sub_sub_lemma_A_1_split_symmetric
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (U : Set H) (hU : U ∈ nhds (0 : H)) :
    ∃ V ∈ nhds (0 : H), IsClosed V ∧ (-V = V) ∧ V + V ⊆ U :=
  sorry  -- exact exists_closed_nhds_zero_neg_eq_add_subset hU

/-- **Sub-sub-lemma A.2 — interior of sum contains sum of interiors**.

For sets `S, T` in a topological add group, `interior S + interior T ⊆ interior (S + T)`.

**Mathlib discharge** (verified): `IsOpen.add_left` and `IsOpen.add_right`
exist via `Topology.Algebra.Group.Pointwise`. Compose for `interior + interior ⊆ interior(+)`.

**Difficulty**: EASY. ~15 lines. -/
theorem _sub_sub_lemma_A_2_interior_add
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (S T : Set H) :
    interior S + interior T ⊆ interior (S + T) :=
  sorry

/-- **Sub-sub-lemma C.1 — Countable closed cover via image-closure**.

For continuous surjective `f : G →+ H`, for every nbhd `U` of 0 in `G`,
`H = ⋃ n, closure (f '' ((n : ℤ) • U))` (countable cover by closed sets).

**Mathlib discharge route**:
- Surjectivity of f + integer scaling.
- `closure` is closed (`isClosed_closure`).
- Countable union argument.

**Difficulty**: EASY-MEDIUM. ~25 lines. -/
theorem _sub_sub_lemma_C_1_countable_closed_cover
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {H : Type v} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (f : G →+ H) (hsurj : Function.Surjective f)
    (U : Set G) (hU : U ∈ nhds (0 : G)) :
    ⋃ n : ℕ, closure (f '' ((n : ℤ) • U)) = Set.univ :=
  sorry

/-- **Sub-sub-lemma C.2 — Baire ⇒ nonempty interior in some closure**.

For a Baire space `H` covered by countably many closed sets, some closed set
has nonempty interior.

**Mathlib discharge** (verified): direct from `nonempty_interior_of_iUnion_of_closed`
in `Topology.Baire.Lemmas`. One-liner body.

**Difficulty**: TRIVIAL. ~5 lines. -/
theorem _sub_sub_lemma_C_2_baire_nonempty_interior
    {H : Type v} [TopologicalSpace H] [BaireSpace H]
    (S : ℕ → Set H) (hS_closed : ∀ n, IsClosed (S n))
    (hS_cover : ⋃ n, S n = Set.univ) :
    ∃ n, (interior (S n)).Nonempty :=
  sorry  -- exact nonempty_interior_of_iUnion_of_closed hS_closed hS_cover

/-- **Sub-sub-lemma D.1 — Inductive Cauchy sequence builder**.

Given approximate-preimage data: for each `n` we know `f(x_n) → y` faster than
the nbhd basis `V_n` shrinks. Builder constructs the Cauchy sequence `x_n`
with `x_{n+1} - x_n ∈ V_n` for the symmetric basis `V_n`.

**Mathlib discharge route**:
- `Nat.rec` for the inductive construction.
- `IsUniformAddGroup.cauchy_iff` for the Cauchy condition.

**Difficulty**: MEDIUM. ~40 lines. The substantive iteration. -/
theorem _sub_sub_lemma_D_1_cauchy_builder
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [(uniformity G).IsCountablyGenerated]
    (basis : ℕ → Set G) (hbasis : ∀ n, basis n ∈ nhds (0 : G))
    (hshrink : ∀ n, basis (n + 1) + basis (n + 1) ⊆ basis n)
    (step : (n : ℕ) → G) (hstep : ∀ n, step (n + 1) - step n ∈ basis n) :
    CauchySeq step :=
  sorry

/-- **Sub-sub-lemma D.2 — Cauchy limit lives in nbhd**.

If `x_n` is Cauchy with `x_{n+1} - x_n ∈ V_n` (shrinking basis at 0), then
the limit `x = lim x_n` satisfies `x - x_0 ∈ V_0 + V_1 + ... ⊆ 2·V_0`.

**Mathlib discharge route**: `CauchySeq.tendsto_of_completeSpace` + sum-of-nbhds
inclusion. ~25 lines. -/
theorem _sub_sub_lemma_D_2_limit_in_nbhd
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    (step : ℕ → G) (hcauchy : CauchySeq step)
    (V : Set G) (hV : V ∈ nhds (0 : G))
    (hstep_in_V : ∀ n, step n - step 0 ∈ V) :
    ∃ x : G, Filter.Tendsto step Filter.atTop (nhds x) ∧ x - step 0 ∈ closure V :=
  sorry

/-! ## Main theorem (composes sub-lemmas A-E from sub-sub-lemmas A.1, A.2, C.1, C.2, D.1, D.2)
-/

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
