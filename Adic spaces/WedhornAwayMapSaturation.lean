/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornLocTopologyLinear

/-!
# Away-to-away map saturation support (T105)

Public reusable API for the **away-to-away** ring hom `Localization.Away
s_0 →+* Localization.Away s` arising from a unit-witness hypothesis
`IsUnit (algebraMap A (Localization.Away s) s_0)` (typically obtained
from a radical relation `e * s_0 = s^N`). Mathlib's
`IsLocalization.Away.lift` provides the underlying construction; this
file lands the **application/extensionality lemmas** plus the
**radical-relation compatibility identities** that callers need to
identify their concrete localization-lift map (e.g., Primary's private
`locLift D₀ D h` in `PresheafTateStructure.lean`) with the abstract
away-to-away setup and to reason about its action on
`algebraMap`/`divByS`/powers via the radical inverse factor.

## Deliverables

* `awayLift_divByS_one_eq_unit_inv` — the away-to-away lift sends
  `divByS 1 s_0` to the unit inverse of `g s_0` in target.

* `awayLift_divByS_one_eq_via_radical` — using radical relation
  `e * s_0 = s^N`, the image of `divByS 1 s_0` equals the explicit
  T097 radical inverse factor `algebraMap e * (divByS 1 s)^N` in
  `Localization.Away s`.

* `awayLift_divByS_eq_via_radical` — for `t : A`, the image of
  `divByS t s_0` equals `algebraMap (t * e) * (divByS 1 s)^N` in
  `Localization.Away s`. The exact formula a consumer like Primary's
  T089 needs when computing `locLift (divByS t D₀.s)` explicitly via
  the radical relation.

* `awayLift_pow_divByS_one_eq_via_radical` — iterated form: the image
  of `(divByS 1 s_0)^k` equals `(algebraMap e)^k * (divByS 1 s)^(N*k)`
  in `Localization.Away s`. Lets the consumer reduce arbitrary
  source-side denominator-powers to target-side `divByS 1 s` powers
  scaled by `N`.

* `awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical` — generic
  `IsLocalization.Away.surj`-form: `awayLift (algebraMap α * (divByS 1
  s_0)^k) = algebraMap (α * e^k) * (divByS 1 s)^(N*k)`. The canonical
  decomposition Primary produces from Mathlib's
  `IsLocalization.Away.surj` and the explicit RHS in target.

These compatibility lemmas are **NOT wrappers** around T099–T104; they
prove concrete equalities of `IsLocalization.Away.lift` on the
canonical denominator generators of `Localization.Away s_0`, using
only Mathlib's `IsLocalization.Away.lift_eq` plus the unit-cancellation
identity `algebraMap s_0 * divByS 1 s_0 = 1` and T097's radical
inverse formula.

## Saturation theorem status (Option 4 partial)

The full saturation theorem
"`IsLocalization.Away.lift s_0 h_unit a ∈ locNhd P T s m → a ∈ locNhd
P_0 T_0 s_0 n ⊔ ker`"
is **identical** to Primary's hard lemma
`cross_localization_preimage_in_sup_ker` modulo renaming. Proving it
requires the same algebraic content (radical-rewrite + Artin-Rees +
small-rep extraction); it is not a wrapper. The deliverables in this
file are the **strongest compiling nontrivial lemmas** in the
saturation chain that don't require the full assembly: the explicit
application formulas for `Away.lift` on the canonical denominator
generators (via the radical inverse). These are exactly the facts
Primary's saturation proof unfolds at each algebraic step.

## Notes

* New leaf file; imports `WedhornLocTopologyLinear` (for T097's
  `algebraMap_mul_pow_divByS_eq_one_of_radical_relation` and T092's
  `algebraMap_mul_divByS_one_eq_one`).
* No edits to Primary-owned `PresheafTateStructure.lean`,
  `WedhornSourceLaurentMembershipInLocalizationBase.lean`, root
  imports, or final theorem signatures.
* No new sorries / custom axioms / partial declarations / native compilation.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`IsLocalization.Away.lift` value on `divByS 1 s_0`** (T105
reusable primitive — Mathlib-style identity).

For `s_0 : A` and `g : A →+* B` with `IsUnit (g s_0)`, applying the
canonical `IsLocalization.Away.lift s_0 hg : Localization.Away s_0 →+*
B` to `divByS 1 s_0 : Localization.Away s_0` yields the unit-inverse
of `g s_0` in `B`:

```
IsLocalization.Away.lift s_0 hg (divByS 1 s_0) = ↑hg.unit⁻¹
```

**Mathematical content**: the element `divByS 1 s_0` is the inverse of
`algebraMap s_0` in `Localization.Away s_0` (via T092's
`algebraMap_mul_divByS_one_eq_one`). The lift `Away.lift s_0 hg` is a
ring hom that sends `algebraMap s_0` to `g s_0` (by
`IsLocalization.Away.lift_eq`); applying the ring hom to the
cancellation identity and using `Units.mul_eq_one_iff_inv_eq` gives
the result.

**Use**: building block for the radical-relation compatibility
identities below. -/
theorem awayLift_divByS_one_eq_unit_inv
    {B : Type*} [CommRing B] (s_0 : A) {g : A →+* B}
    (hg : IsUnit (g s_0)) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS 1 s_0) = ↑hg.unit⁻¹ := by
  -- The lift sends (algebraMap s_0 * divByS 1 s_0 = 1) to
  -- (g s_0 * Away.lift hg (divByS 1 s_0) = 1). Combined with
  -- ↑hg.unit = g s_0, this gives the unit-inverse characterisation.
  have h_lift_one :
      IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (algebraMap A (Localization.Away s_0) s_0) *
        IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
          (divByS 1 s_0) = 1 := by
    rw [← map_mul, algebraMap_mul_divByS_one_eq_one, map_one]
  rw [IsLocalization.Away.lift_eq] at h_lift_one
  -- h_lift_one : g s_0 * (Away.lift hg) (divByS 1 s_0) = 1
  rw [show (g s_0 : B) = ↑hg.unit from hg.unit_spec.symm] at h_lift_one
  -- Now h_lift_one : ↑hg.unit * (Away.lift hg) (divByS 1 s_0) = 1
  exact (Units.mul_eq_one_iff_inv_eq.mp h_lift_one).symm

/-- **Radical-relation form of `awayLift` on `divByS 1 s_0`** (T105
ticket-named theorem).

Given the radical relation `e * s_0 = s^N` in `A`, the canonical
`IsLocalization.Away.lift s_0` (with target `Localization.Away s` and
unit witness from T097's `IsUnit.of_radical_relation`) applied to
`divByS 1 s_0` yields the T097 radical inverse factor `algebraMap e *
(divByS 1 s)^N` in `Localization.Away s`.

**Mathematical content**: by `awayLift_divByS_one_eq_unit_inv` the
LHS equals `↑hg.unit⁻¹`. By T097's
`algebraMap_mul_pow_divByS_eq_one_of_radical_relation`, `algebraMap
s_0 * (algebraMap e * (divByS 1 s)^N) = 1`, so by
`Units.mul_eq_one_iff_inv_eq`, `algebraMap e * (divByS 1 s)^N =
↑hg.unit⁻¹`. Equating gives the result.

**Use** (T089): Primary's `locLift D₀ D h := IsLocalization.Away.lift
D₀.s ...` directly inherits this identity once they identify the
unit-witness paths. This gives the explicit formula for `locLift
(divByS 1 D₀.s)` in `Localization.Away D.s`. -/
theorem awayLift_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS 1 s_0) =
      algebraMap A (Localization.Away s) e * (divByS 1 s) ^ N := by
  rw [awayLift_divByS_one_eq_unit_inv s_0 hg]
  -- Goal: ↑hg.unit⁻¹ = algebraMap e * (divByS 1 s)^N
  -- T097 inverse: algebraMap s_0 * (algebraMap e * (divByS 1 s)^N) = 1.
  have h_inv :
      algebraMap A (Localization.Away s) s_0 *
        (algebraMap A (Localization.Away s) e * (divByS 1 s) ^ N) = 1 :=
    algebraMap_mul_pow_divByS_eq_one_of_radical_relation h_rad
  rw [show (algebraMap A (Localization.Away s) s_0 : Localization.Away s) =
      ↑hg.unit from hg.unit_spec.symm] at h_inv
  -- h_inv : ↑hg.unit * (algebraMap e * (divByS 1 s)^N) = 1
  exact (Units.mul_eq_one_iff_inv_eq.mp h_inv)

/-- **`awayLift` on `divByS t s_0` via radical relation** (T105 reusable
identity).

For `t : A` and the radical relation `e * s_0 = s^N`, the canonical
away-lift maps `divByS t s_0` to `algebraMap (t * e) * (divByS 1 s)^N`
in `Localization.Away s`.

**Mathematical content**: `divByS t s_0 = algebraMap t * divByS 1 s_0`
in `Localization.Away s_0`. Apply `awayLift_divByS_one_eq_via_radical`
to the `divByS 1 s_0` factor and `IsLocalization.Away.lift_eq` to the
`algebraMap t` factor.

**Use** (T089): explicit formula for `locLift (divByS t D₀.s)` in
`Localization.Away D.s`. -/
theorem awayLift_divByS_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) (t : A) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (divByS t s_0) =
      algebraMap A (Localization.Away s) (t * e) * (divByS 1 s) ^ N := by
  -- divByS t s_0 = algebraMap t * divByS 1 s_0 in Loc s_0.
  have h_decomp : divByS t s_0 =
      algebraMap A (Localization.Away s_0) t * divByS 1 s_0 := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers s_0)
          (S := Localization.Away s_0) t,
        ← IsLocalization.mk'_mul, mul_one, one_mul]
  rw [h_decomp, map_mul, IsLocalization.Away.lift_eq s_0 hg t,
      awayLift_divByS_one_eq_via_radical h_rad hg, map_mul]
  ring

/-- **`awayLift` on `(divByS 1 s_0)^k` via radical relation** (T105
iterated form).

For `k : ℕ` and the radical relation `e * s_0 = s^N`, the canonical
away-lift maps `(divByS 1 s_0)^k` to `(algebraMap e)^k * (divByS 1
s)^(N*k)` in `Localization.Away s`.

**Use** (T089): when Primary applies `IsLocalization.Away.surj` to
write `a = algebraMap α * (divByS 1 s_0)^k_a`, this lemma gives the
explicit `(divByS 1 s)^(N * k_a)` factor — exactly the `k_a · N`
denominator-depth term that drives Primary's saturation analysis. -/
theorem awayLift_pow_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0)) (k : ℕ) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        ((divByS 1 s_0) ^ k) =
      (algebraMap A (Localization.Away s) e) ^ k *
        (divByS 1 s) ^ (N * k) := by
  rw [map_pow, awayLift_divByS_one_eq_via_radical h_rad hg, mul_pow,
      ← pow_mul, mul_comm N k]

/-- **Generic algebraMap saturation form for `awayLift` images** (T105
saturation prefix — strongest compiling form expressible without
`locLift`).

For `α : A` and `k : ℕ`, the canonical away-lift evaluates as

```
IsLocalization.Away.lift s_0 hg (algebraMap α * (divByS 1 s_0)^k) =
  algebraMap (α * e^k) * (divByS 1 s)^(N * k)   in Localization.Away s.
```

Direct combination of `IsLocalization.Away.lift_eq` (on the
`algebraMap α` factor) with `awayLift_pow_divByS_one_eq_via_radical`
(on the `(divByS 1 s_0)^k` factor).

**Use** (T089): the canonical form Primary produces from
`IsLocalization.Away.surj`-style decomposition `a = algebraMap α *
(divByS 1 s_0)^k_a`. The explicit RHS makes the target locNhd-depth
analysis tractable: by T095's iterated `divByS 1 s` shift, the
target-side `(divByS 1 s)^(N · k_a)` factor demands target depth
`m ≥ ?(N · k_a + n_target)` for source representative depth
`n_target`. -/
theorem awayLift_algebraMap_mul_pow_divByS_one_eq_via_radical
    {s_0 s e : A} {N : ℕ} (h_rad : e * s_0 = s ^ N)
    (hg : IsUnit (algebraMap A (Localization.Away s) s_0))
    (α : A) (k : ℕ) :
    IsLocalization.Away.lift (S := Localization.Away s_0) s_0 hg
        (algebraMap A (Localization.Away s_0) α * (divByS 1 s_0) ^ k) =
      algebraMap A (Localization.Away s) (α * e ^ k) *
        (divByS 1 s) ^ (N * k) := by
  rw [map_mul, IsLocalization.Away.lift_eq s_0 hg α,
      awayLift_pow_divByS_one_eq_via_radical h_rad hg, map_mul, map_pow]
  ring

end ValuationSpectrum
