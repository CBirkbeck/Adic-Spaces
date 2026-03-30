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
        change mapOfLE R S h (↑(a * b) : R.ValueGroup) = 1
        rw [Units.val_mul, map_mul, ha, hb, one_mul]
      one_mem' := by change mapOfLE R S h (↑(1 : R.ValueGroupˣ) : R.ValueGroup) = 1; simp
      inv_mem' := fun {a} ha => by
        change mapOfLE R S h (↑(a⁻¹) : R.ValueGroup) = 1
        rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one] }
  convex' := by
    intro a b x ha hb hax hxb
    change mapOfLE R S h (x : R.ValueGroup) = 1
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
  change mapOfLE A (A.ofPrime P) (le_ofPrime A P) (g : A.ValueGroup) = 1
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
  change mapOfLE A (A.ofPrime ⊥) (le_ofPrime A ⊥) (g : A.ValueGroup) = 1
  obtain ⟨x, hx⟩ := A.valuation_surjective (g : A.ValueGroup)
  rw [show (g : A.ValueGroup) = A.valuation x from hx.symm, mapOfLE_valuation_apply]
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero g (hx ▸ (show A.valuation x = 0 by simp [he]))
  rcases A.mem_or_inv_mem x with hxA | hxA
  · have : (⟨x, hxA⟩ : A) ∈ (⊥ : Ideal A).primeCompl := by
      simp only [Ideal.primeCompl, Submodule.bot_coe, Submonoid.mem_mk, Subsemigroup.mem_mk,
        Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => hx_ne (Subtype.mk.inj h ▸ rfl)
    exact (ofPrime_valuation_eq_one_iff_mem_primeCompl A ⊥ ⟨x, hxA⟩).mpr this
  · have : (⟨x⁻¹, hxA⟩ : A) ∈ (⊥ : Ideal A).primeCompl := by
      simp only [Ideal.primeCompl, Submodule.bot_coe, Submonoid.mem_mk, Subsemigroup.mem_mk,
        Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => inv_ne_zero hx_ne (Subtype.mk.inj h ▸ rfl)
    have h1 := (ofPrime_valuation_eq_one_iff_mem_primeCompl A ⊥ ⟨x⁻¹, hxA⟩).mpr this
    rw [map_inv₀] at h1; exact inv_eq_one.mp h1

/-! ### The inverse map: from convex subgroups to prime ideals -/

/-- Helper: coerce `(a + b : A)` to `K` gives `(a : K) + (b : K)`. -/
private theorem coe_add_val (A : ValuationSubring K) (a b : A) :
    ((a + b : A) : K) = (a : K) + (b : K) := rfl

/-- Helper: coerce `(c • a : A)` to `K` gives `(c : K) * (a : K)`. -/
private theorem coe_smul_val (A : ValuationSubring K) (c a : A) :
    ((c • a : A) : K) = (c : K) * (a : K) := rfl

/-- Helper: coerce `(a * b : A)` to `K` gives `(a : K) * (b : K)`. -/
private theorem coe_mul_val (A : ValuationSubring K) (a b : A) :
    ((a * b : A) : K) = (a : K) * (b : K) := rfl

/-- The prime ideal of `A` associated to a convex subgroup `C` of `A.ValueGroupˣ`.
This is the inverse direction of the Bourbaki correspondence.

The carrier is `{a ∈ A | ∀ (ha : A.valuation a ≠ 0), Units.mk0 (A.valuation a) ha ∉ C}`. -/
noncomputable def primeOfConvexSubgroup (A : ValuationSubring K)
    (C : ConvexSubgroup A.ValueGroupˣ) : Ideal A where
  carrier := {a | ∀ (ha : A.valuation (a : K) ≠ 0), Units.mk0 (A.valuation (a : K)) ha ∉ C}
  add_mem' := by
    intro a b ha hb hne
    have hne' : A.valuation ((a : K) + (b : K)) ≠ 0 := hne
    by_cases hva : A.valuation (a : K) = 0
    · have ha_zero : (a : K) = 0 := by rwa [Valuation.zero_iff] at hva
      have hval_eq : A.valuation ((a : K) + (b : K)) = A.valuation (b : K) := by
        rw [ha_zero, zero_add]
      have hvb : A.valuation (b : K) ≠ 0 := hval_eq ▸ hne'
      have hueq : Units.mk0 (A.valuation ((a + b : A) : K)) hne =
          Units.mk0 (A.valuation (b : K)) hvb :=
        Units.ext (by change A.valuation ((a + b : A) : K) = A.valuation (b : K); exact hval_eq)
      rw [hueq]; exact hb hvb
    · by_cases hvb : A.valuation (b : K) = 0
      · have hb_zero : (b : K) = 0 := by rwa [Valuation.zero_iff] at hvb
        have hval_eq : A.valuation ((a : K) + (b : K)) = A.valuation (a : K) := by
          rw [hb_zero, add_zero]
        have hueq : Units.mk0 (A.valuation ((a + b : A) : K)) hne =
            Units.mk0 (A.valuation (a : K)) hva :=
          Units.ext (by change A.valuation ((a + b : A) : K) = A.valuation (a : K); exact hval_eq)
        rw [hueq]; exact ha hva
      · have hua := ha hva
        have hub := hb hvb
        have hva_lt1 : Units.mk0 (A.valuation (a : K)) hva < 1 :=
          lt_of_le_of_ne (A.valuation_le_one a)
            (fun heq => hua (heq ▸ C.toSubgroup.one_mem))
        have hvb_lt1 : Units.mk0 (A.valuation (b : K)) hvb < 1 :=
          lt_of_le_of_ne (A.valuation_le_one b)
            (fun heq => hub (heq ▸ C.toSubgroup.one_mem))
        intro hmem
        have hab_le : A.valuation ((a + b : A) : K) ≤
            max (A.valuation (a : K)) (A.valuation (b : K)) :=
          Valuation.map_add A.valuation _ _
        have ha_lt := C.lt_of_not_mem_of_lt_one hua hva_lt1 hmem
        have hb_lt := C.lt_of_not_mem_of_lt_one hub hvb_lt1 hmem
        rcases le_max_iff.mp hab_le with h | h
        · exact absurd (h : (Units.mk0 _ hne : A.ValueGroupˣ) ≤ Units.mk0 _ hva)
            (not_le_of_gt ha_lt)
        · exact absurd (h : (Units.mk0 _ hne : A.ValueGroupˣ) ≤ Units.mk0 _ hvb)
            (not_le_of_gt hb_lt)
  smul_mem' := by
    intro c a ha hne
    have hva : A.valuation (a : K) ≠ 0 := by
      intro heq; apply hne; rw [coe_smul_val, Valuation.map_mul, heq, mul_zero]
    have hua := ha hva
    intro hmem
    by_cases hva_eq1 : Units.mk0 (A.valuation (a : K)) hva = 1
    · exact hua (hva_eq1 ▸ C.toSubgroup.one_mem)
    · have hva_lt1 : Units.mk0 (A.valuation (a : K)) hva < 1 :=
        lt_of_le_of_ne (A.valuation_le_one a) hva_eq1
      have hca_le : A.valuation ((c • a : A) : K) ≤ A.valuation (a : K) := by
        rw [coe_smul_val, Valuation.map_mul]
        calc A.valuation (c : K) * A.valuation (a : K)
            ≤ 1 * A.valuation (a : K) := by
              exact mul_le_mul_left (A.valuation_le_one c) _
          _ = A.valuation (a : K) := one_mul _
      have hlt := C.lt_of_not_mem_of_lt_one hua hva_lt1 hmem
      exact absurd (hca_le : (Units.mk0 _ hne : A.ValueGroupˣ) ≤ Units.mk0 _ hva)
        (not_le_of_gt hlt)
  zero_mem' := by intro h; exact absurd (map_zero _) h

/-- Membership in `primeOfConvexSubgroup` spelled out. -/
@[simp]
theorem mem_primeOfConvexSubgroup_iff (A : ValuationSubring K)
    (C : ConvexSubgroup A.ValueGroupˣ) (a : A) :
    a ∈ primeOfConvexSubgroup A C ↔
      ∀ (ha : A.valuation (a : K) ≠ 0), Units.mk0 (A.valuation (a : K)) ha ∉ C := by
  constructor
  · intro h ha; exact h ha
  · intro h ha; exact h ha

/-- Negation of membership. -/
theorem not_mem_primeOfConvexSubgroup_iff (A : ValuationSubring K)
    (C : ConvexSubgroup A.ValueGroupˣ) (a : A) :
    a ∉ primeOfConvexSubgroup A C ↔
      ∃ (ha : A.valuation (a : K) ≠ 0), Units.mk0 (A.valuation (a : K)) ha ∈ C := by
  simp only [mem_primeOfConvexSubgroup_iff, not_forall, not_not]

/-- The prime-of-convex construction produces a prime ideal. -/
instance primeOfConvexSubgroup_isPrime (A : ValuationSubring K)
    (C : ConvexSubgroup A.ValueGroupˣ) : (primeOfConvexSubgroup A C).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    rw [mem_primeOfConvexSubgroup_iff] at h1
    apply h1 (by simp [Valuation.map_one])
    rw [show Units.mk0 (A.valuation ((1 : A) : K)) _ = 1 from
      Units.ext (by simp [Valuation.map_one])]
    exact C.toSubgroup.one_mem
  mem_or_mem' := by
    intro a b hab
    by_contra hc; push_neg at hc; obtain ⟨hna, hnb⟩ := hc
    rw [not_mem_primeOfConvexSubgroup_iff] at hna hnb
    obtain ⟨hva, hua⟩ := hna
    obtain ⟨hvb, hub⟩ := hnb
    rw [mem_primeOfConvexSubgroup_iff] at hab
    have hvab : A.valuation ((a * b : A) : K) ≠ 0 := by
      rw [coe_mul_val, Valuation.map_mul]; exact mul_ne_zero hva hvb
    apply hab hvab
    rw [show Units.mk0 (A.valuation ((a * b : A) : K)) hvab =
      Units.mk0 (A.valuation (a : K)) hva * Units.mk0 (A.valuation (b : K)) hvb from
      Units.ext (by simp [coe_mul_val, Valuation.map_mul])]
    exact C.toSubgroup.mul_mem hua hub

/-! ### Containment properties of primeOfConvexSubgroup -/

/-- If `convexSubgroupOfPrime A Q ≤ C`, then `primeOfConvexSubgroup A C ≤ Q`.

Elements of `primeOfConvex C` have unit part outside `C`, hence outside `H_Q`
(since `H_Q ≤ C`), so they map nontrivially under `mapOfLE A (ofPrime Q)`,
meaning they are nonunits in `ofPrime Q`, hence in `Q`. -/
theorem primeOfConvexSubgroup_le_of_le (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (C : ConvexSubgroup A.ValueGroupˣ)
    (hle : convexSubgroupOfPrime A Q ≤ C) :
    primeOfConvexSubgroup A C ≤ Q := by
  intro a ha
  by_cases hva : A.valuation (a : K) = 0
  · have : (a : K) = 0 := by rwa [Valuation.zero_iff] at hva
    have : a = 0 := Subtype.ext this
    rw [this]; exact Q.zero_mem
  · have hua := (mem_primeOfConvexSubgroup_iff A C a).mp ha hva
    have hua_H : Units.mk0 (A.valuation (a : K)) hva ∉ convexSubgroupOfPrime A Q := by
      intro hmem; exact hua (hle _ hmem)
    rw [mem_convexSubgroupOfPrime] at hua_H
    push_neg at hua_H
    have hmap : mapOfLE A (A.ofPrime Q) (le_ofPrime A Q) (A.valuation (a : K)) =
        (A.ofPrime Q).valuation (a : K) := mapOfLE_valuation_apply _ _ _ _
    rw [Units.val_mk0] at hua_H
    rw [hmap] at hua_H
    have hle1 : (A.ofPrime Q).valuation (a : K) ≤ 1 :=
      (A.ofPrime Q).valuation_le_one ⟨(a : K), le_ofPrime A Q a.2⟩
    have hlt1 : (A.ofPrime Q).valuation (a : K) < 1 :=
      lt_of_le_of_ne hle1 hua_H
    have hmem_max : (⟨(a : K), le_ofPrime A Q a.2⟩ : A.ofPrime Q) ∈
        IsLocalRing.maximalIdeal (A.ofPrime Q) :=
      (valuation_lt_one_iff _ _).mpr hlt1
    have := idealOfLE_ofPrime A Q
    have : a ∈ idealOfLE A (A.ofPrime Q) (le_ofPrime A Q) := hmem_max
    rwa [idealOfLE_ofPrime] at this

/-- If `convexSubgroupOfPrime A Q < C`, then `primeOfConvexSubgroup A C < Q`.

Pick `g ∈ C \ H_Q`. WLOG `g ≤ 1`. Since `g ∉ H_Q`, the corresponding element
of `A` has `(ofPrime Q).valuation < 1`, hence is in `Q`. But `g ∈ C` means
the element is NOT in `primeOfConvex C`. So `Q ⊄ primeOfConvex C`. -/
theorem primeOfConvexSubgroup_lt_of_lt (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (C : ConvexSubgroup A.ValueGroupˣ)
    (hlt : convexSubgroupOfPrime A Q < C) :
    primeOfConvexSubgroup A C < Q := by
  refine lt_of_le_of_ne (primeOfConvexSubgroup_le_of_le A Q C hlt.le) ?_
  intro heq
  have hne : convexSubgroupOfPrime A Q ≠ C := ne_of_lt hlt
  have : ∃ g, g ∈ C ∧ g ∉ convexSubgroupOfPrime A Q := by
    by_contra hall; push_neg at hall
    exact hne (le_antisymm hlt.le (fun x hx => hall x hx))
  obtain ⟨g, hgC, hgH⟩ := this
  have hg' : (if g ≤ 1 then g else g⁻¹) ∈ C := by
    split_ifs with h
    · exact hgC
    · exact inv_mem hgC
  have hg'H : (if g ≤ 1 then g else g⁻¹) ∉ convexSubgroupOfPrime A Q := by
    split_ifs with h
    · exact hgH
    · exact fun hmem => hgH (inv_inv g ▸ inv_mem hmem)
  have hg'_le1 : (if g ≤ 1 then g else g⁻¹) ≤ 1 := by
    split_ifs with h
    · exact h
    · push_neg at h; exact (inv_le_one_of_one_le h.le)
  set g' := if g ≤ 1 then g else g⁻¹ with hg'_def
  rw [mem_convexSubgroupOfPrime] at hg'H
  push_neg at hg'H
  obtain ⟨x, hx⟩ := A.valuation_surjective (g' : A.ValueGroup)
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero g' (by rw [← hx]; simp [he])
  have hx_le1 : A.valuation x ≤ 1 := hx ▸ Units.val_le_val.mpr hg'_le1
  have hx_mem_A : x ∈ A := A.mem_of_valuation_le_one x hx_le1
  set a : A := ⟨x, hx_mem_A⟩
  have hva : A.valuation (a : K) ≠ 0 := by
    rw [show (a : K) = x from rfl, hx]; exact Units.ne_zero g'
  have hunit_eq : Units.mk0 (A.valuation (a : K)) hva = g' := by
    ext; simp [show (a : K) = x from rfl, hx]
  have ha_not_prime : a ∉ primeOfConvexSubgroup A C := by
    rw [mem_primeOfConvexSubgroup_iff]
    push_neg; exact ⟨hva, hunit_eq ▸ hg'⟩
  have hmap : mapOfLE A (A.ofPrime Q) (le_ofPrime A Q) (A.valuation x) =
      (A.ofPrime Q).valuation x := mapOfLE_valuation_apply _ _ _ _
  have hmap2 : mapOfLE A (A.ofPrime Q) (le_ofPrime A Q) (g' : A.ValueGroup) =
      (A.ofPrime Q).valuation x := by rw [← hx, hmap]
  have hne1 : (A.ofPrime Q).valuation x ≠ 1 := by rw [← hmap2]; exact hg'H
  have hle1 : (A.ofPrime Q).valuation x ≤ 1 :=
    (A.ofPrime Q).valuation_le_one ⟨x, le_ofPrime A Q hx_mem_A⟩
  have hlt1 : (A.ofPrime Q).valuation x < 1 := lt_of_le_of_ne hle1 hne1
  have : (⟨x, le_ofPrime A Q hx_mem_A⟩ : A.ofPrime Q) ∈
      IsLocalRing.maximalIdeal (A.ofPrime Q) :=
    (valuation_lt_one_iff _ _).mpr hlt1
  have ha_in_idealOfLE : a ∈ idealOfLE A (A.ofPrime Q) (le_ofPrime A Q) := this
  rw [idealOfLE_ofPrime] at ha_in_idealOfLE
  exact ha_not_prime (heq ▸ ha_in_idealOfLE)

/-- If `primeOfConvexSubgroup A C = ⊥`, then `C = ⊤`.

When every nonzero element of `A` has its unit part in `C`, surjectivity of
`A.valuation` ensures every unit of the value group is in `C`. -/
theorem primeOfConvexSubgroup_eq_bot_imp_eq_top (A : ValuationSubring K)
    (C : ConvexSubgroup A.ValueGroupˣ)
    (h : primeOfConvexSubgroup A C = ⊥) : C = ⊤ := by
  ext u; simp only [ConvexSubgroup.mem_top, iff_true]
  obtain ⟨x, hx⟩ := A.valuation_surjective (u : A.ValueGroup)
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero u (by rw [← hx]; simp [he])
  rcases A.mem_or_inv_mem x with hxA | hxA
  · set a : A := ⟨x, hxA⟩
    have hva : A.valuation (a : K) ≠ 0 := by
      rw [show (a : K) = x from rfl]; rwa [Valuation.ne_zero_iff]
    have ha_not_mem : a ∉ primeOfConvexSubgroup A C := by
      intro hmem
      rw [h] at hmem
      have := Ideal.mem_bot.mp hmem
      exact hx_ne (Subtype.ext_iff.mp this)
    rw [not_mem_primeOfConvexSubgroup_iff] at ha_not_mem
    obtain ⟨_, hmem⟩ := ha_not_mem
    have : Units.mk0 (A.valuation (a : K)) hva = u := by
      ext; simp [show (a : K) = x from rfl, hx]
    rwa [this] at hmem
  · set a : A := ⟨x⁻¹, hxA⟩
    have hva : A.valuation (a : K) ≠ 0 := by
      rw [show (a : K) = x⁻¹ from rfl, Valuation.ne_zero_iff]; exact inv_ne_zero hx_ne
    have ha_not_mem : a ∉ primeOfConvexSubgroup A C := by
      intro hmem
      rw [h] at hmem
      have := Ideal.mem_bot.mp hmem
      exact inv_ne_zero hx_ne (Subtype.ext_iff.mp this)
    rw [not_mem_primeOfConvexSubgroup_iff] at ha_not_mem
    obtain ⟨_, hmem⟩ := ha_not_mem
    have hval_inv : A.valuation (a : K) = (↑u)⁻¹ := by
      rw [show (a : K) = x⁻¹ from rfl, map_inv₀, hx]
    have : Units.mk0 (A.valuation (a : K)) hva = u⁻¹ := by
      ext; simp [Units.val_mk0, hval_inv, Units.val_inv_eq_inv_val]
    rw [this] at hmem
    exact inv_inv u ▸ inv_mem hmem

/-! ### Maximality of convexSubgroupOfPrime for height-1 primes -/

/-- **Maximality of the kernel convex subgroup for height-1 primes.**

If `Q` is a height-1 prime (no prime P with ⊥ < P < Q) and `C` is a convex
subgroup of `A.ValueGroupˣ` strictly containing `convexSubgroupOfPrime A Q`,
then `C = ⊤`.

This follows from the Bourbaki correspondence (Comm. Alg., Ch. VI, §4, No. 5):
convex subgroups of the value group biject (order-reversing) with primes of the
valuation ring. Since Q is height-1, `convexSubgroupOfPrime A Q` is a maximal
proper convex subgroup.

The proof uses `primeOfConvexSubgroup`, the inverse map of the correspondence:
1. `primeOfConvexSubgroup A C` is a prime ideal strictly below Q (by containment).
2. Height-1 forces `primeOfConvexSubgroup A C = ⊥`.
3. `primeOfConvexSubgroup A C = ⊥` implies `C = ⊤`. -/
theorem convexSubgroupOfPrime_maximal_of_height_one (A : ValuationSubring K)
    (Q : Ideal A) [Q.IsPrime] (_ : Q ≠ ⊥)
    (hht1 : ∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥)
    (C : ConvexSubgroup A.ValueGroupˣ)
    (hHC : convexSubgroupOfPrime A Q < C) : C = ⊤ := by
  have hP := primeOfConvexSubgroup_lt_of_lt A Q C hHC
  have hP_eq_bot := hht1 (primeOfConvexSubgroup A C) hP
  exact primeOfConvexSubgroup_eq_bot_imp_eq_top A C hP_eq_bot

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
  have harch_units : MulArchimedean W.ValueGroupˣ := by
    apply ConvexSubgroup.mulArchimedean_of_no_proper_nontrivial
    intro L
    by_cases hL : L = ⊥
    · exact .inl hL
    · refine .inr ?_
      let C := L.comap f hf_mono
      have hHC : convexSubgroupOfPrime A Q ≤ C := by
        intro g hg; change f g ∈ L
        have hval : (f g : W.ValueGroup) = 1 :=
          (mapOfLEUnits_val A W (le_ofPrime A Q) g).trans hg
        rw [show f g = 1 from Units.val_eq_one.mp hval]
        exact L.toSubgroup.one_mem
      have hHC_strict : convexSubgroupOfPrime A Q < C := by
        rw [lt_iff_le_and_ne]
        refine ⟨hHC, fun heq => hL (ConvexSubgroup.ext fun k => ⟨fun hk => by
          obtain ⟨g, rfl⟩ := hf_surj k
          have hgC : g ∈ C := hk
          have hgH : g ∈ convexSubgroupOfPrime A Q := heq ▸ hgC
          exact Units.val_eq_one.mp ((mapOfLEUnits_val A W _ g).trans hgH),
        fun hk => ConvexSubgroup.mem_bot.mp hk ▸ L.toSubgroup.one_mem⟩)⟩
      have hC_top := convexSubgroupOfPrime_maximal_of_height_one A Q hQ hht1 C hHC_strict
      ext k; simp only [ConvexSubgroup.mem_top, iff_true]
      obtain ⟨g, rfl⟩ := hf_surj k
      exact (hC_top ▸ trivial : g ∈ C)
  constructor; intro x y hy
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (show (0 : W.ValueGroup) ≤ y ^ 0 by simp)⟩
  · have hy0 : y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
    obtain ⟨n, hn⟩ := harch_units.arch (Units.mk0 x hx) (show 1 < Units.mk0 y hy0 from hy)
    exact ⟨n, by simpa [Units.val_pow_eq_pow_val] using hn⟩

/-- **Round-trip: H ≤ convexSubgroupOfPrime(primeOfConvexSubgroup H).**

For `g ∈ H`, we need `mapOfLE A (A.ofPrime Q) _ (↑g) = 1` where `Q = primeOfConvexSubgroup A H`.
Lift `g` to `x : K` via `valuation_surjective`. Then `Units.mk0(v(x)) = g ∈ H`,
so `x` (or `x⁻¹`) is NOT in `Q` (by definition of `primeOfConvexSubgroup`), hence is in
`Q.primeCompl`. By `ofPrime_valuation_eq_one_iff_mem_primeCompl`, the value is `1`.

This is one direction of the Bourbaki correspondence (Comm. Alg., Ch. VI, §4, No. 5). -/
theorem le_convexSubgroupOfPrime_primeOfConvexSubgroup (A : ValuationSubring K)
    (H : ConvexSubgroup A.ValueGroupˣ) :
    H ≤ convexSubgroupOfPrime A (primeOfConvexSubgroup A H) := by
  intro g hg
  change mapOfLE A (A.ofPrime (primeOfConvexSubgroup A H))
    (le_ofPrime A (primeOfConvexSubgroup A H)) (g : A.ValueGroup) = 1
  obtain ⟨x, hx⟩ := A.valuation_surjective (g : A.ValueGroup)
  have hx_ne : x ≠ 0 := by
    intro he; exact Units.ne_zero g (hx ▸ (show A.valuation x = 0 by simp [he]))
  rw [show (g : A.ValueGroup) = A.valuation x from hx.symm, mapOfLE_valuation_apply]
  rcases A.mem_or_inv_mem x with hxA | hxA
  · set a : A := ⟨x, hxA⟩
    have hva : A.valuation (a : K) ≠ 0 := by
      rw [show (a : K) = x from rfl]; rwa [Valuation.ne_zero_iff]
    have hunit_eq : Units.mk0 (A.valuation (a : K)) hva = g := by
      ext; simp [show (a : K) = x from rfl, hx]
    have ha_not_mem : a ∉ primeOfConvexSubgroup A H := by
      rw [mem_primeOfConvexSubgroup_iff]; push_neg
      exact ⟨hva, hunit_eq ▸ hg⟩
    have ha_compl : a ∈ (primeOfConvexSubgroup A H).primeCompl := ha_not_mem
    exact (ofPrime_valuation_eq_one_iff_mem_primeCompl A
      (primeOfConvexSubgroup A H) a).mpr ha_compl
  · set a : A := ⟨x⁻¹, hxA⟩
    have hva : A.valuation (a : K) ≠ 0 := by
      rw [show (a : K) = x⁻¹ from rfl, Valuation.ne_zero_iff]; exact inv_ne_zero hx_ne
    have hunit_eq : Units.mk0 (A.valuation (a : K)) hva = g⁻¹ := by
      ext; simp [show (a : K) = x⁻¹ from rfl, map_inv₀, hx, Units.val_inv_eq_inv_val]
    have hg_inv : g⁻¹ ∈ H := inv_mem hg
    have ha_not_mem : a ∉ primeOfConvexSubgroup A H := by
      rw [mem_primeOfConvexSubgroup_iff]; push_neg
      exact ⟨hva, hunit_eq ▸ hg_inv⟩
    have ha_compl : a ∈ (primeOfConvexSubgroup A H).primeCompl := ha_not_mem
    have h1 := (ofPrime_valuation_eq_one_iff_mem_primeCompl A
      (primeOfConvexSubgroup A H) a).mpr ha_compl
    rw [show (a : K) = x⁻¹ from rfl, map_inv₀] at h1
    exact inv_eq_one.mp h1

/-! ### Existence of height-1 primes above a convex subgroup -/

/-- For a proper convex subgroup H of a valuation ring's value group, there exists
a height-1 prime Q with `convexSubgroupOfPrime A Q ⊇ H`. Since convex subgroups
are linearly ordered (Bourbaki), take the maximal proper convex subgroup above H
(exists by Zorn). Its corresponding prime is height-1. -/
theorem exists_height_one_prime_ge_convexSubgroup (A : ValuationSubring K)
    (H : ConvexSubgroup A.ValueGroupˣ) (hH : H ≠ ⊤) :
    ∃ (Q : Ideal A) (_ : Q.IsPrime), Q ≠ ⊥ ∧
      (∀ (P : Ideal A) [P.IsPrime], P < Q → P = ⊥) ∧
      H ≤ convexSubgroupOfPrime A Q := by
  -- Use primeOfConvexSubgroup to get a prime, then find a height-1 prime above it.
  -- The prime Q₀ := primeOfConvexSubgroup A H satisfies H ≤ convexSubgroupOfPrime A Q₀
  -- (by le_convexSubgroupOfPrime_primeOfConvexSubgroup).
  -- If Q₀ is height-1, we're done. Otherwise, take a height-1 prime Q ≤ Q₀.
  -- By convexSubgroupOfPrime_antitone, convexSubgroupOfPrime Q ⊇ convexSubgroupOfPrime Q₀ ⊇ H.
  set Q₀ := primeOfConvexSubgroup A H with hQ₀_def
  have hQ₀_prime : Q₀.IsPrime := inferInstance
  have hH_le : H ≤ convexSubgroupOfPrime A Q₀ :=
    le_convexSubgroupOfPrime_primeOfConvexSubgroup A H
  -- Q₀ = ⊥ ⟹ convexSubgroupOfPrime Q₀ = ⊤ (by convexSubgroupOfPrime_bot)
  -- ⟹ H ≤ ⊤ = H, so H = ⊤, contradicting hH.
  have hQ₀_ne_bot : Q₀ ≠ ⊥ := sorry
  -- Find a minimal nonzero prime Q ≤ Q₀ (height-1 prime).
  -- For valuation rings, primes are totally ordered, so a minimal nonzero prime
  -- exists below Q₀. By convexSubgroupOfPrime_antitone, H ≤ convexSubgroupOfPrime Q.
  -- TODO: needs existence of minimal nonzero prime (well-order on primes of valuation ring)
  sorry

end ValuationSubring
