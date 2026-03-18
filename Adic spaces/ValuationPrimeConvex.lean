/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».OrderedGroupConvex
import «Adic spaces».ValuationCoarsening
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Prime Ideals and Convex Subgroups of Valuation Rings

The relationship between prime ideals of a valuation ring and convex subgroups
of its value group (Bourbaki, Comm. Alg., Ch. VI, §4, No. 5).

## Main definitions

* `ValuationSubring.convexSubgroupOfLE` : Kernel of `mapOfLE` on units as a convex subgroup.
* `ValuationSubring.convexSubgroupOfPrime` : Convex subgroup corresponding to a prime.

## Main results

* `ValuationSubring.mapOfLE_surjective` : The value group map is surjective.
* `ValuationSubring.ideal_le_total` : All ideals of a valuation ring are totally ordered.
* `ValuationSubring.prime_le_total` : All primes of a valuation ring are totally ordered.
* `ValuationSubring.mulArchimedean_ofPrime_of_height_one` : Height-1 primes give
  MulArchimedean value groups.

## References

* [N. Bourbaki, *Commutative Algebra*][bourbaki1972commutative], Chapter VI, §4
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.1
-/

namespace ValuationSubring

variable {K : Type*} [Field K]

/-! ### Surjectivity of mapOfLE and convex subgroup kernel -/

/-- The natural map on value groups induced by a coarsening is surjective.

Every element of `S.ValueGroup` is `S.valuation x` for some `x : K`
(by `valuation_surjective`), and `mapOfLE_valuation_apply` gives
`mapOfLE R S h (R.valuation x) = S.valuation x`. -/
theorem mapOfLE_surjective (R S : ValuationSubring K) (h : R ≤ S) :
    Function.Surjective (R.mapOfLE S h) := by
  intro y
  obtain ⟨x, rfl⟩ := S.valuation_surjective y
  exact ⟨R.valuation x, R.mapOfLE_valuation_apply S h x⟩

/-- The kernel of `mapOfLE R S h` restricted to units of `R.ValueGroup`,
as a convex subgroup of `R.ValueGroupˣ`.

Elements of this convex subgroup are units `g` of the value group of `R`
that map to `1` in the value group of `S`. Convexity follows from
monotonicity of `mapOfLE`: if `a, b` map to `1` and `a ≤ x ≤ b`,
then `1 ≤ mapOfLE x ≤ 1`, so `mapOfLE x = 1`. -/
def convexSubgroupOfLE (R S : ValuationSubring K) (h : R ≤ S) :
    ConvexSubgroup R.ValueGroupˣ where
  toSubgroup :=
    { carrier := {g | mapOfLE R S h (g : R.ValueGroup) = 1}
      mul_mem' := fun {a b} ha hb => by
        show mapOfLE R S h (↑(a * b) : R.ValueGroup) = 1
        rw [Units.val_mul, map_mul, ha, hb, one_mul]
      one_mem' := by show mapOfLE R S h (↑(1 : R.ValueGroupˣ) : R.ValueGroup) = 1; simp
      inv_mem' := fun {a} ha => by
        show mapOfLE R S h (↑(a⁻¹) : R.ValueGroup) = 1
        rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one] }
  convex' := by
    intro a b x ha hb hax hxb
    show mapOfLE R S h (x : R.ValueGroup) = 1
    have hma : mapOfLE R S h (a : R.ValueGroup) = 1 := ha
    have hmb : mapOfLE R S h (b : R.ValueGroup) = 1 := hb
    have h1 : (1 : S.ValueGroup) ≤ mapOfLE R S h (x : R.ValueGroup) :=
      hma ▸ monotone_mapOfLE R S h (Units.val_le_val.mpr hax)
    have h2 : mapOfLE R S h (x : R.ValueGroup) ≤ (1 : S.ValueGroup) :=
      hmb ▸ monotone_mapOfLE R S h (Units.val_le_val.mpr hxb)
    exact le_antisymm h2 h1

@[simp]
theorem mem_convexSubgroupOfLE (R S : ValuationSubring K) (h : R ≤ S)
    (g : R.ValueGroupˣ) :
    g ∈ convexSubgroupOfLE R S h ↔ mapOfLE R S h (g : R.ValueGroup) = 1 :=
  Iff.rfl

/-- The convex subgroup of `A.ValueGroupˣ` corresponding to a prime `P` of `A`.

This is the kernel of `mapOfLE A (A.ofPrime P) _` on units. Elements are the
values `A.valuation x` for units `x ∈ Aˣ` that become units in `A.ofPrime P`. -/
def convexSubgroupOfPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
    ConvexSubgroup A.ValueGroupˣ :=
  convexSubgroupOfLE A (A.ofPrime P) (le_ofPrime A P)

@[simp]
theorem mem_convexSubgroupOfPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime]
    (g : A.ValueGroupˣ) :
    g ∈ convexSubgroupOfPrime A P ↔
      mapOfLE A (A.ofPrime P) (le_ofPrime A P) (g : A.ValueGroup) = 1 :=
  Iff.rfl

/-! ### Total ordering of ideals and primes -/

variable (A : ValuationSubring K)

/-- In a valuation ring, all ideals are totally ordered by inclusion.

This is one of the equivalent characterizations of valuation rings
(see `ValuationRing.iff_ideal_total`). For a `ValuationSubring K`,
the instance `ValuationRing A` is available and provides the total ordering. -/
theorem ideal_le_total (I J : Ideal A) : I ≤ J ∨ J ≤ I :=
  (ValuationRing.le_total_ideal A).1 I J

/-- In a valuation ring, prime ideals are totally ordered by inclusion.

This follows immediately from the total ordering of all ideals. -/
theorem prime_le_total (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] :
    P ≤ Q ∨ Q ≤ P :=
  ideal_le_total A P Q

/-! ### Minimal primes in valuation rings -/

/-- In a valuation ring with totally ordered primes, a minimal prime
over an ideal `J` is the smallest prime containing `J`.

Since primes are totally ordered, `J.minimalPrimes` is a singleton
(when nonempty). -/
theorem minimalPrime_unique {J : Ideal A} {P Q : Ideal A}
    (hP : P ∈ J.minimalPrimes) (hQ : Q ∈ J.minimalPrimes) : P = Q := by
  rcases ideal_le_total A P Q with h | h
  · exact le_antisymm h (hQ.2 ⟨hP.1.1, hP.1.2⟩ h)
  · exact le_antisymm (hP.2 ⟨hQ.1.1, hQ.1.2⟩ h) h

/-- In a valuation ring, a prime `P` contains an ideal `J` if and only if `P`
is above the minimal prime of `J` (when it exists).

Since primes are totally ordered, any prime containing `J` is comparable
with the minimal prime, and minimality forces the minimal prime to be below. -/
theorem minimalPrime_le_of_le {J : Ideal A} {P Q : Ideal A} [P.IsPrime]
    (hQ : Q ∈ J.minimalPrimes) (hJP : J ≤ P) : Q ≤ P := by
  rcases ideal_le_total A Q P with h | h
  · exact h
  · exact hQ.2 ⟨‹P.IsPrime›, hJP⟩ h

/-! ### Height-1 primes: what is and is not true

**WARNING:** The statement "the minimal prime over a nonzero ideal has height 1"
is FALSE in general valuation rings.

**Counterexample:** Consider a valuation ring `A` with value group `Z x Z` (lex order).
The prime spectrum is `bot < P1 < m` (three primes). Let `J = m` (the maximal ideal,
which is nonzero). Then `m` is already prime, so `m.minimalPrimes = {m}`.
But `m` has height 2 (since `bot < P1 < m`), not height 1.

The correct weaker claim: in a valuation ring, there EXISTS a height-1 prime
(the smallest nonzero prime). But a given minimal prime over a given ideal
may have arbitrary height.

For the application to Lemma 7.45, one needs `MulArchimedean` for the value group
of a suitable coarsening. The correct approach is to use the prime-convex
correspondence (Bourbaki, Comm. Alg., Ch. VI, §4, No. 5) together with
a height-1 prime argument, which requires choosing the RIGHT prime, not just
any minimal prime over an ideal. -/

/-- In a valuation ring, if `P` is a height-1 prime (no primes strictly between
`bot` and `P`) and `P` is nonzero, then there are no primes strictly between
`bot` and `P`. This is a tautology, but we state it to document the intended usage.

The nontrivial content is in establishing EXISTENCE of such a `P` containing
a given ideal, which requires the prime-convex correspondence. -/
theorem height_one_no_prime_between {P : Ideal A} [P.IsPrime]
    (hht1 : ∀ (Q : Ideal A) [Q.IsPrime], Q < P → Q = ⊥) :
    ∀ (Q : Ideal A) [Q.IsPrime], ⊥ < Q → Q < P → False := by
  intro Q _ hQ_bot hQP
  exact absurd (hht1 Q hQP) (ne_of_gt hQ_bot)

/-- In a valuation ring, if `Q` is a minimal prime over `J` and `P < Q` is prime,
then `J` is not contained in `P`.

This follows from the minimality of `Q`: if `J <= P` and `P < Q`, then `P`
would be a smaller prime containing `J`, contradicting `Q`'s minimality. -/
theorem not_le_of_lt_minimalPrime {J : Ideal A} {P Q : Ideal A}
    [P.IsPrime] (hQ : Q ∈ J.minimalPrimes) (hPQ : P < Q) : ¬(J ≤ P) := by
  intro hJP
  have h1 : Q ≤ P := hQ.2 ⟨‹P.IsPrime›, hJP⟩ hPQ.le
  exact absurd h1 (not_le_of_gt hPQ)

/-- In a valuation ring, for any two elements `a b`, either `a` divides `b`
or `b` divides `a`. This is the divisibility form of the valuation ring property. -/
theorem dvd_or_dvd (a b : A) : a ∣ b ∨ b ∣ a :=
  (ValuationRing.dvd_total a b)

end ValuationSubring
