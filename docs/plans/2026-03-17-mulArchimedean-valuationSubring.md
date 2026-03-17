# Plan: `exists_mulArchimedean_valuationSubring_of_prime`

> **File:** `Adic spaces/Lemma745.lean:466`
> **Date:** 2026-03-17
> **Blocker for:** AdicMorphisms Lemma 7.46(2), Prop 8.39, Cor 8.40

## Goal

```lean
theorem exists_mulArchimedean_valuationSubring_of_prime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A)) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits ∧
      MulArchimedean V.ValueGroup
```

Find a **rank-1** (MulArchimedean) valuation subring V of `Frac(A/𝔭)` such that
(1) A₀-image ⊆ V, (2) I-images ⊆ V.nonunits.

## Existing infrastructure

| Lemma | Location | What it gives |
|-------|----------|---------------|
| `exists_valuationSubring_of_prime` | Lemma745:149 | V₀ with conditions (1)-(2), NOT rank 1 |
| `ValuationSubring.ofPrime V Q` | Mathlib | Coarsened ring V' ≥ V at prime Q |
| `ValuationSubring.le_ofPrime` | Mathlib | V ≤ V.ofPrime Q |
| `ValuationSubring.idealOfLE_ofPrime` | Mathlib | idealOfLE(V, V.ofPrime Q) = Q |
| `Ideal.exists_minimalPrimes_le` | Mathlib | Minimal prime over any ideal ≤ given prime |
| `mulArchimedean_of_no_proper_nontrivial` | OrderedGroupConvex:366 | No proper nontrivial convex subgroups ⟹ MulArchimedean |
| `maxAvoid`, `maxAvoid_mem_of_nontrivial` | OrderedGroupConvex:274,304 | Convex subgroup avoiding an element |

## Proof strategy

### Approach A: Via `ValuationSubring.ofPrime` (recommended)

1. **Get V₀** from `exists_valuationSubring_of_prime`.
2. **Lift I-images to V₀:** The I-image elements lie in `V₀.nonunits` (by hypothesis),
   hence in `IsLocalRing.maximalIdeal V₀`. They generate an ideal `J` of `V₀`.
3. **Find minimal prime:** Use `Ideal.exists_minimalPrimes_le` with `J ≤ maximalIdeal V₀`
   to get a minimal prime `Q` of `V₀` over `J`.
4. **Set V' = V₀.ofPrime Q.**

**Condition (1) — Range containment:**
`V₀ ≤ V' = V₀.ofPrime Q` by `le_ofPrime`. Since A₀-image ⊆ V₀, it's also ⊆ V'.

**Condition (2) — I-images nonunits:**
I-image elements are in `J ⊆ Q`. An element `x ∈ V₀` with `⟨x, hx⟩ ∈ Q` is a nonunit
of `V.ofPrime Q`. Proof: by `idealOfLE_ofPrime`, `Q = V₀.idealOfLE (V₀.ofPrime Q) _`.
The `idealOfLE` ideal consists of elements of V₀ that are nonunits of V₀.ofPrime Q.
So membership in Q implies membership in nonunits.

**Condition (3) — MulArchimedean:**
This is the hardest step. Q is a minimal prime of V₀ over J.

*Helper lemma needed:*
```lean
theorem ValuationSubring.mulArchimedean_ofPrime_of_minimalPrime
    {K : Type*} [Field K] (V : ValuationSubring K)
    {J : Ideal V} (hJ : J ≠ ⊥) {Q : Ideal V} (hQ : Q ∈ J.minimalPrimes) :
    MulArchimedean (V.ofPrime Q).ValueGroup
```

The proof uses the Galois correspondence: primes of V ↔ convex subgroups of V.ValueGroup
(order-reversing). Q minimal over J (nonzero) corresponds to a maximal convex subgroup H
avoiding the J-values. The quotient V.ValueGroup / H is MulArchimedean because any
nontrivial convex subgroup of the quotient would correspond (via preimage) to a convex
subgroup C with H ⊊ C, contradicting maximality.

### Approach B: Direct coarsening via convex subgroups

Use the existing `Valuation.coarsenByUnits` (Lemma745:403) + `maxAvoid` (OrderedGroupConvex:274).

1. Get V₀ and its valuation v₀ = V₀.valuation.
2. Pick any I-image element a₀ ∈ I \ 𝔭 (exists by non-openness of 𝔭).
3. Let γ = v₀(a₀) ∈ V₀.ValueGroupˣ (nonzero since a₀ ∉ supp(v₀) = 𝔭).
4. H = maxAvoid(γ) in V₀.ValueGroupˣ.
5. v' = v₀.coarsenByUnits H.
6. V' = v'.valuationSubring.

**Problem with Approach B:** The quotient by `maxAvoid(γ)` is NOT automatically
MulArchimedean (counterexample: Γ = ℤ×ℤ lex, γ = (0,1)). It IS archimedean
when γ generates a cofinal sequence in the quotient, which requires γ to be
"height-1" — i.e., there is no element strictly between 1 and γ modulo H.

This can be fixed by instead choosing H = maxAvoid(S) where S = {v₀(aᵢ) : aᵢ generators of I},
and showing the quotient is archimedean. But this requires the same Galois correspondence
argument as Approach A.

## Required helper lemmas (Approach A)

### Lemma 1: I-images generate a nonzero ideal of V₀

```lean
-- The I-image ideal in V₀ is nonzero (since I has elements not in 𝔭)
theorem I_ideal_ne_bot ...
```

Follows from `exists_mem_I_not_mem_of_not_isOpen` (existing in the file).

### Lemma 2: Elements of idealOfLE are nonunits

```lean
-- x ∈ V.idealOfLE(V') implies x is a nonunit of V'
theorem mem_idealOfLE_nonunits (V V' : ValuationSubring K) (hle : V ≤ V')
    (x : K) (hxV : x ∈ V) (hx : (⟨x, hxV⟩ : V) ∈ V.idealOfLE V' hle) :
    x ∈ V'.nonunits
```

This should follow from the definition of `idealOfLE`: it's `{x ∈ V : x⁻¹ ∉ V'}`.

### Lemma 3: MulArchimedean at minimal primes (the hard one)

```lean
theorem mulArchimedean_ofPrime_of_minimalPrime ...
```

Requires formalizing: in a valuation ring, primes correspond to convex subgroups
(order-reversing), and a minimal nonzero prime gives an archimedean quotient group.

**Mathlib status:** The correspondence `primes ↔ convex subgroups` for valuation rings
is NOT formalized in Mathlib (as of v4.29.0-rc3). It would need to be built from:
- `ValuationSubring.valuation_lt_one_iff` — characterizes nonunits via valuation
- `Valuation.IsEquiv` — valuation equivalence
- `ConvexSubgroup` from our `OrderedGroupConvex.lean`

## Estimated effort

| Step | Difficulty | Lines |
|------|-----------|-------|
| Lemma 1 (J ≠ ⊥) | Easy | 10 |
| Lemma 2 (idealOfLE → nonunits) | Medium | 15 |
| Lemma 3 (MulArchimedean at minimal prime) | **Hard** | 40-60 |
| Main theorem assembly | Medium | 20 |
| **Total** | | **85-105** |

Lemma 3 is the critical path. It may require 2-3 additional helper lemmas about
the prime-convex-subgroup correspondence in valuation rings.
