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
noncomputable def convexSubgroupOfPrime (A : ValuationSubring K) (P : Ideal A) [P.IsPrime] :
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

/-! ### Composition and factorization of mapOfLE -/

/-- The value group map `mapOfLE` factors through intermediate coarsenings:
`mapOfLE R T = mapOfLE S T ∘ mapOfLE R S` for `R ≤ S ≤ T`.

Both sides agree on `R.valuation x` by `mapOfLE_valuation_apply`, and
`R.valuation` is surjective, giving equality everywhere. -/
theorem mapOfLE_comp (R S T : ValuationSubring K) (hRS : R ≤ S) (hST : S ≤ T)
    (hRT : R ≤ T) (x : R.ValueGroup) :
    mapOfLE R T hRT x = mapOfLE S T hST (mapOfLE R S hRS x) := by
  obtain ⟨k, rfl⟩ := R.valuation_surjective x; simp [mapOfLE_valuation_apply]

/-! ### Map on units induced by mapOfLE -/

/-- The restriction of `mapOfLE` to units of the value groups.
This is a group homomorphism `R.ValueGroupˣ →* S.ValueGroupˣ`. -/
noncomputable def mapOfLEUnits (R S : ValuationSubring K) (h : R ≤ S) :
    R.ValueGroupˣ →* S.ValueGroupˣ :=
  Units.map (R.mapOfLE S h).toMonoidHom

/-- The unit-level map `mapOfLEUnits` is monotone (order-preserving). -/
theorem monotone_mapOfLEUnits (R S : ValuationSubring K) (h : R ≤ S) :
    Monotone (mapOfLEUnits R S h) :=
  fun _ _ hab => Units.val_le_val.mp (monotone_mapOfLE R S h (Units.val_le_val.mpr hab))

/-- The unit-level map `mapOfLEUnits` is surjective.

Given a unit `u` of `S.ValueGroup`, lift it to `x : K` via `S.valuation_surjective`.
Then `R.valuation x` is a unit (since `x ≠ 0`) mapping to `u`. -/
theorem surjective_mapOfLEUnits (R S : ValuationSubring K) (h : R ≤ S) :
    Function.Surjective (mapOfLEUnits R S h) := by
  intro u
  obtain ⟨x, hx⟩ := S.valuation_surjective (u : S.ValueGroup)
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero u (hx ▸ (show S.valuation x = 0 by simp [he]))
  exact ⟨Units.mk0 (R.valuation x) (by rwa [Valuation.ne_zero_iff]),
    Units.ext (show mapOfLE R S h (R.valuation x) = (u : S.ValueGroup) by
      rw [mapOfLE_valuation_apply, hx])⟩

/-- The underlying value of `mapOfLEUnits R S h g` in `S.ValueGroup` equals
`mapOfLE R S h` applied to the underlying value of `g` in `R.ValueGroup`. -/
theorem mapOfLEUnits_val (R S : ValuationSubring K) (h : R ≤ S) (g : R.ValueGroupˣ) :
    ((mapOfLEUnits R S h g : S.ValueGroupˣ) : S.ValueGroup) =
      mapOfLE R S h (g : R.ValueGroup) := rfl

/-! ### Antitonicity of convexSubgroupOfPrime -/

/-- The map `P ↦ convexSubgroupOfPrime A P` is antitone (order-reversing):
`P ≤ Q` implies `convexSubgroupOfPrime A Q ≤ convexSubgroupOfPrime A P`.

This follows from the factorization `mapOfLE A (ofPrime P) = mapOfLE (ofPrime Q) (ofPrime P)
∘ mapOfLE A (ofPrime Q)`, since `ofPrime_le_of_le` gives `ofPrime Q ≤ ofPrime P`. -/
theorem convexSubgroupOfPrime_antitone (A : ValuationSubring K)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    convexSubgroupOfPrime A Q ≤ convexSubgroupOfPrime A P := by
  intro g hg
  show mapOfLE A (A.ofPrime P) (le_ofPrime A P) (g : A.ValueGroup) = 1
  have hg' : mapOfLE A (A.ofPrime Q) (le_ofPrime A Q) (g : A.ValueGroup) = 1 := hg
  rw [mapOfLE_comp A (A.ofPrime Q) (A.ofPrime P) (le_ofPrime A Q)
    (ofPrime_le_of_le A P Q h) (le_ofPrime A P)]
  rw [hg', map_one]

/-! ### convexSubgroupOfPrime at the zero ideal -/

/-- The convex subgroup corresponding to the zero ideal is the full group:
`convexSubgroupOfPrime A ⊥ = ⊤`.

Since `ofPrime A ⊥` is the localization at all nonzero elements (the full field),
every nonzero element becomes a unit, so the kernel of `mapOfLE` on units is everything.
The proof uses `ofPrime_valuation_eq_one_iff_mem_primeCompl`: for `a ∈ A` nonzero,
`(ofPrime A ⊥).valuation a = 1` since `a ∈ (⊥ : Ideal A).primeCompl`. -/
theorem convexSubgroupOfPrime_bot (A : ValuationSubring K) :
    convexSubgroupOfPrime A (⊥ : Ideal A) = ⊤ := by
  ext g
  simp only [ConvexSubgroup.mem_top, iff_true]
  show mapOfLE A (A.ofPrime ⊥) (le_ofPrime A ⊥) (g : A.ValueGroup) = 1
  obtain ⟨x, hx⟩ := A.valuation_surjective (g : A.ValueGroup)
  rw [show (g : A.ValueGroup) = A.valuation x from hx.symm, mapOfLE_valuation_apply]
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero g (hx ▸ (show A.valuation x = 0 by simp [he]))
  rcases A.mem_or_inv_mem x with hxA | hxA
  · have : (⟨x, hxA⟩ : A) ∈ (⊥ : Ideal A).primeCompl := by
      simp [Ideal.primeCompl]; exact fun h => hx_ne (Subtype.mk.inj h ▸ rfl)
    exact (ofPrime_valuation_eq_one_iff_mem_primeCompl A ⊥ ⟨x, hxA⟩).mpr this
  · have : (⟨x⁻¹, hxA⟩ : A) ∈ (⊥ : Ideal A).primeCompl := by
      simp [Ideal.primeCompl]; exact fun h => inv_ne_zero hx_ne (Subtype.mk.inj h ▸ rfl)
    have h1 := (ofPrime_valuation_eq_one_iff_mem_primeCompl A ⊥ ⟨x⁻¹, hxA⟩).mpr this
    rw [map_inv₀] at h1; exact inv_eq_one.mp h1

/-! ### Maximality of convexSubgroupOfPrime for height-1 primes -/

/-- **Maximality of the kernel convex subgroup for height-1 primes.**

If `Q` is a height-1 prime (no prime P with ⊥ < P < Q) and `C` is a convex
subgroup of `A.ValueGroupˣ` strictly containing `convexSubgroupOfPrime A Q`,
then `C = ⊤`.

This is the key step connecting the prime lattice to the convex subgroup lattice.
It follows from the Bourbaki correspondence (Comm. Alg., Ch. VI, §4, No. 5):
convex subgroups of the value group biject (order-reversing) with primes of the
valuation ring. Since Q is height-1, `convexSubgroupOfPrime A Q` is a maximal
proper convex subgroup.

The full proof requires the inverse map of the Galois correspondence: given a
convex subgroup `C`, construct the prime `{a ∈ A | A.valuation a ∉ Cˣ}` and
show it equals the expected prime. This is left as a sorry pending the full
correspondence implementation. -/
theorem convexSubgroupOfPrime_maximal_of_height_one (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (_ : Q ≠ ⊥)
    (_ : ∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥)
    (C : ConvexSubgroup A.ValueGroupˣ)
    (_ : convexSubgroupOfPrime A Q < C) : C = ⊤ := by
  sorry

/-! ### Height-1 primes give MulArchimedean value groups -/

/-- **Height-1 primes give MulArchimedean value groups.**

If `Q` is a height-1 prime of valuation ring `A` (`Q ≠ ⊥` and no prime `P` with
`⊥ < P < Q`), then `(A.ofPrime Q).ValueGroup` is `MulArchimedean`.

**Proof outline:**
1. Show `MulArchimedean` on units `(A.ofPrime Q).ValueGroupˣ` using
   `mulArchimedean_of_no_proper_nontrivial`: every convex subgroup is `⊥` or `⊤`.
2. For any nontrivial convex subgroup `L` of the target units, pull back via
   `mapOfLEUnits` to get `C` in the source. The kernel `convexSubgroupOfPrime A Q`
   is contained in `C`, and strictly so when `L ≠ ⊥` (by surjectivity).
3. By `convexSubgroupOfPrime_maximal_of_height_one`, `C = ⊤`, forcing `L = ⊤`.
4. Lift from units to the full `ValueGroup` (a `LinearOrderedCommGroupWithZero`)
   by handling the zero case separately. -/
theorem mulArchimedean_ofPrime_of_height_one (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hht1 : ∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥) :
    MulArchimedean (A.ofPrime Q).ValueGroup := by
  let W := A.ofPrime Q
  let f := mapOfLEUnits A W (le_ofPrime A Q)
  have hf_surj := surjective_mapOfLEUnits A W (le_ofPrime A Q)
  have hf_mono := monotone_mapOfLEUnits A W (le_ofPrime A Q)
  -- Step 1: MulArchimedean on units via no-proper-nontrivial convex subgroups
  have harch_units : MulArchimedean W.ValueGroupˣ := by
    apply ConvexSubgroup.mulArchimedean_of_no_proper_nontrivial
    intro L
    by_cases hL : L = ⊥
    · exact .inl hL
    · refine .inr ?_
      -- Pull back L to a convex subgroup of A.ValueGroupˣ
      let C := L.comap f hf_mono
      -- The kernel convexSubgroupOfPrime A Q ≤ C
      have hHC : convexSubgroupOfPrime A Q ≤ C := by
        intro g hg; show f g ∈ L
        have hval : (f g : W.ValueGroup) = 1 :=
          (mapOfLEUnits_val A W (le_ofPrime A Q) g).trans hg
        rw [show f g = 1 from Units.val_eq_one.mp hval]
        exact L.toSubgroup.one_mem
      -- The containment is strict because L ≠ ⊥ and f is surjective
      have hHC_strict : convexSubgroupOfPrime A Q < C := by
        rw [lt_iff_le_and_ne]
        refine ⟨hHC, fun heq => hL (ConvexSubgroup.ext fun k => ⟨fun hk => by
          obtain ⟨g, rfl⟩ := hf_surj k
          have hgC : g ∈ C := hk
          have hgH : g ∈ convexSubgroupOfPrime A Q := heq ▸ hgC
          exact Units.val_eq_one.mp ((mapOfLEUnits_val A W _ g).trans hgH),
        fun hk => ConvexSubgroup.mem_bot.mp hk ▸ L.toSubgroup.one_mem⟩)⟩
      -- By maximality from height-1: C = ⊤
      have hC_top := convexSubgroupOfPrime_maximal_of_height_one A Q hQ hht1 C hHC_strict
      -- Since f is surjective and C = ⊤: L = ⊤
      ext k; simp only [ConvexSubgroup.mem_top, iff_true]
      obtain ⟨g, rfl⟩ := hf_surj k
      exact (hC_top ▸ trivial : g ∈ C)
  -- Step 2: Lift from units to the full ValueGroup
  constructor; intro x y hy
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (show (0 : W.ValueGroup) ≤ y ^ 0 by simp)⟩
  · have hy0 : y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
    obtain ⟨n, hn⟩ := harch_units.arch (Units.mk0 x hx) (show 1 < Units.mk0 y hy0 from hy)
    exact ⟨n, by simpa [Units.val_pow_eq_pow_val] using hn⟩

end ValuationSubring
