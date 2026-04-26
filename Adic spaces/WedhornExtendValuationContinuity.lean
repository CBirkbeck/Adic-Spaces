/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LocalizationTopology
import «Adic spaces».ContinuousValuations

/-!
# Continuity of `Valuation.extendToLocalization` under `locTopology`

The single remaining residual identified in
`WedhornLocalizationLiftContinuity.lean`: continuity of the
`Valuation.extendToLocalization` (Mathlib) at the locTopology on
`Localization.Away s`.

## Audit and refinement

The full continuity statement as identified in the prior file's
trailing docblock requires a **uniform bound** on the extended valuation
across `locSubring` elements, which generally fails for arbitrary
valuations: a `locSubring` element such as `t/s` has extended-valuation
`ν(t)/ν(s)` — unbounded if `ν(t) > ν(s)`.

The bound DOES hold under two natural Wedhorn callsite hypotheses:

* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` — `ν` bounded by 1 on the ring of
  definition. Implied by `A₀ ⊆ A⁺` (Wedhorn 7.17 /
  `CompatiblePlusSubring`) plus `v ∈ Spa A A⁺`.

* `hν_T : ∀ t ∈ T, ν t ≤ ν s` — the test family `T` is
  `s`-non-archimedean-bounded. Implied by `v ∈ rationalOpen T s`.

Under these hypotheses, `ν` extends to `extendToLocalization` bounded
by 1 on `locSubring` (proved here), and continuity follows by combining
this bound with `ν`'s continuity on `A` and the `locNhd`-basis
structure.

## What this file provides

1. `extendToLocalization_le_one_of_locSubring` — the key bound:
   `(ν.extendToLocalization)` is bounded by `1` on `locSubring P T s`,
   under `hν_A₀` and `hν_T`. Proved by `Subring.closure_induction` on
   the generators `algebraMap '' A₀ ∪ {t/s : t ∈ T}`.

2. `extendToLocalization_isContinuous_locTopology_of_bounded` — the
   strengthened continuity theorem. Combines the locSubring bound with
   ν's continuity on A and the `locNhd`-basis structure.

3. Documented relation to the manager's original target signature
   (without the strengthened hypotheses): the abstract theorem as
   stated requires the additional hypotheses to hold; the strengthened
   form here is the natural Wedhorn-callsite version.

## Notes

* No root import; leaf-level file.
* No edits to `LocalizationTopology.lean`, `ContinuousValuations.lean`,
  or any committed bridge file.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Bound on `extendToLocalization` over `locSubring`** under natural
Wedhorn-callsite hypotheses.

If `ν : Valuation A Γ` satisfies:
* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` (`ν` bounded on the ring of definition)
* `hν_T : ∀ t ∈ T, ν t ≤ ν s` (test family s-bounded; equivalently,
  `ν(t/s) ≤ 1`)
* `hν_s_pos : ν s ≠ 0` (denominator non-degenerate)

then `(ν.extendToLocalization hS (Localization.Away s))` is bounded by
`1` on every element of `locSubring P T s`.

**Proof**: `Subring.closure_induction` on the closure-generators
`algebraMap '' A₀ ∪ {t/s : t ∈ T}`. For `a ∈ A₀`:
`(extendToLocalization)(algebraMap a) = ν a ≤ 1`. For `t/s`:
`(extendToLocalization)(t/s) = ν(t) · (ν(s))⁻¹ ≤ 1` since
`ν(t) ≤ ν(s)`. Closure operations preserve `≤ 1` (sum: max of bounds;
product: product of bounds; etc.). -/
theorem extendToLocalization_le_one_of_locSubring
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ)
    (hν_A₀ : ∀ a ∈ P.A₀, ν a ≤ 1)
    (hν_T : ∀ t ∈ T, ν t ≤ ν s)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl)
    {x : Localization.Away s} (hx : x ∈ locSubring P T s) :
    (ν.extendToLocalization hS (Localization.Away s)) x ≤ 1 := by
  -- `Submonoid.powers s ≤ ν.supp.primeCompl` ⟹ `s ∉ ν.supp` ⟹ `ν s ≠ 0`.
  have hs_pos : ν s ≠ 0 := by
    intro hνs0
    have hs_supp : s ∈ ν.supp := by rw [Valuation.mem_supp_iff]; exact hνs0
    exact hS (Submonoid.mem_powers s) hs_supp
  -- `(ν s)⁻¹ ≤ (ν s)⁻¹` (will be used as a bound for t/s ≤ 1).
  -- The inverse of a unit `≤ 1` is `≥ 1`, so we need ν(t) · ν(s)⁻¹ ≤ 1 ↔ ν(t) ≤ ν(s).
  set ν_loc := ν.extendToLocalization hS (Localization.Away s) with hν_loc
  refine Subring.closure_induction (p := fun y _ => ν_loc y ≤ 1) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · -- Generators: y ∈ algebraMap '' A₀ ∪ Set.range (fun t : T => divByS t s).
    rintro y (⟨a, ha, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · -- y = algebraMap a, a ∈ A₀.
      show ν_loc (algebraMap A (Localization.Away s) a) ≤ 1
      rw [hν_loc, Valuation.extendToLocalization_apply_map_apply]
      exact hν_A₀ a ha
    · -- y = divByS (t : A) s = IsLocalization.mk' _ t ⟨s, ⟨1, pow_one s⟩⟩.
      show ν_loc (divByS (t : A) s) ≤ 1
      simp only [divByS, hν_loc, Valuation.extendToLocalization_mk']
      calc ν (t : A) * (ν s)⁻¹
          ≤ ν s * (ν s)⁻¹ := mul_le_mul_right' (hν_T t ht) _
        _ = 1 := mul_inv_cancel₀ hs_pos
  · -- 0 case: ν_loc 0 = 0 ≤ 1.
    show ν_loc 0 ≤ 1
    rw [map_zero]; exact zero_le_one
  · -- 1 case: ν_loc 1 = 1 ≤ 1.
    show ν_loc 1 ≤ 1
    rw [map_one]
  · -- Sum: ν_loc(a + b) ≤ max ≤ 1.
    intro a b _ _ ha hb
    show ν_loc (a + b) ≤ 1
    refine le_trans (ν_loc.map_add a b) ?_
    exact max_le ha hb
  · -- Negation: ν_loc(-a) = ν_loc(a) ≤ 1.
    intro a _ ha
    show ν_loc (-a) ≤ 1
    rw [Valuation.map_neg]; exact ha
  · -- Product: ν_loc(a * b) = ν_loc a * ν_loc b ≤ 1 * 1 = 1.
    intro a b _ _ ha hb
    show ν_loc (a * b) ≤ 1
    rw [map_mul]
    exact mul_le_one' ha hb

/-- **Strengthened continuity of `extendToLocalization` under
`locTopology`** (the natural Wedhorn-callsite version).

Given the natural Wedhorn-callsite hypotheses:

* `hν_cont : ν.IsContinuous` — original valuation is continuous on `A`.
* `hν_A₀ : ∀ a ∈ A₀, ν a ≤ 1` — bounded on the ring of definition.
* `hν_T : ∀ t ∈ T, ν t ≤ ν s` — `t/s` ratios bounded by 1.
* `hS : Submonoid.powers s ≤ ν.supp.primeCompl` — `ν s ≠ 0`.

the extended valuation `ν.extendToLocalization` is continuous on
`Localization.Away s` under `locTopology P T s hopen`.

**Proof structure**:

1. By `Subring.closure_induction` (`extendToLocalization_le_one_of_locSubring`),
   the extended valuation is bounded by `1` on `locSubring P T s`.

2. For any `γ ∈ Γ`, use `ν`'s continuity at `0 : A` to find `m : ℕ`
   such that `algebraMap (P.I^m) ⊆ {b | ν b < γ}` (via
   `P.hasBasis_nhds_zero` and `extendToLocalization_apply_map_apply`).

3. For `d ∈ locNhd m` (image of `(locIdeal)^m` in `Localization.Away s`):
   the locSubring bound (step 1) plus the `algebraMap (P.I^m)` bound
   (step 2) combine via `≤ max` (non-archimedean) to give
   `(ν.extendToLocalization) d < γ`.

The final IsOpen-at-0 follows; full IsContinuous via translation by
the `IsTopologicalAddGroup` structure of `locTopology`. -/
theorem extendToLocalization_isContinuous_locTopology_of_bounded
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation A Γ) (hν_cont : ν.IsContinuous)
    (hν_A₀ : ∀ a ∈ P.A₀, ν a ≤ 1)
    (hν_T : ∀ t ∈ T, ν t ≤ ν s)
    (hS : Submonoid.powers s ≤ ν.supp.primeCompl) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    (ν.extendToLocalization hS (Localization.Away s)).IsContinuous := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  set ν_loc := ν.extendToLocalization hS (Localization.Away s) with hν_loc
  -- The locSubring bound (step 1).
  have h_locSubring_bound : ∀ x ∈ locSubring P T s, ν_loc x ≤ 1 :=
    fun x hx => extendToLocalization_le_one_of_locSubring P T s ν hν_A₀ hν_T hS hx
  -- For continuity, it suffices (by IsTopologicalAddGroup) to verify continuity at 0.
  -- For each γ ∈ Γ, need {b | ν_loc b < γ} to be open.
  -- We show it contains a locNhd m for some m.
  intro γ
  -- Step 2: find m such that ν(P.I^m) < γ.
  -- Use ν.IsContinuous: {a | ν a < γ} is open in A, so contains a basic nhd of 0,
  -- which by P.hasBasis_nhds_zero has the form `Subtype.val '' (P.I^m)`.
  by_cases hγ : γ = 0
  · subst hγ
    convert isOpen_empty
    ext b
    simp [not_lt_zero']
  -- γ ≠ 0, so γ is a unit. Use ltAddSubgroup characterization.
  set γu : Γˣ := Units.mk0 γ hγ with hγu
  rw [show { b : Localization.Away s | ν_loc b < γ } =
        (ν_loc.ltAddSubgroup γu : Set (Localization.Away s)) from
      (Valuation.coe_ltAddSubgroup ν_loc γu).symm]
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  rw [(locBasis P T s hopen).hasBasis_nhds_zero.mem_iff]
  have h_open_A : IsOpen { a : A | ν a < γ } := hν_cont γ
  obtain ⟨m, _, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (h_open_A.mem_nhds (by simp [zero_lt_iff.mpr hγ] : (0 : A) ∈ {a | ν a < γ}))
  refine ⟨m, trivial, ?_⟩
  intro d hd
  -- d ∈ locNhd m, i.e., ∃ d' ∈ (locIdeal)^m, subtype.val d' = d.
  obtain ⟨d', hd'_mem, rfl⟩ := hd
  -- Goal: subtype.val d' ∈ ↑(ν_loc.ltAddSubgroup γu).
  show ν_loc ((d' : locSubring P T s) : Localization.Away s) < γ
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I^m), Ideal.map_span] at hd'_mem
  refine Submodule.span_induction (p := fun x _ =>
    ν_loc (((x : locSubring P T s) : Localization.Away s)) < γ)
    ?_ ?_ ?_ ?_ hd'_mem
  · -- Generator case: x = algebraMapD b for b ∈ P.I^m.
    rintro x ⟨b, hb, rfl⟩
    show ν_loc ((algebraMapD P T s b : locSubring P T s)
      : Localization.Away s) < γ
    have heq : ((algebraMapD P T s b : locSubring P T s) :
        Localization.Away s) = algebraMap A (Localization.Away s) (b : A) :=
      rfl
    rw [heq, hν_loc, Valuation.extendToLocalization_apply_map_apply]
    exact hm ⟨b, hb, rfl⟩
  · -- Zero case.
    show ν_loc (((0 : locSubring P T s) : Localization.Away s)) < γ
    simp [zero_lt_iff.mpr hγ]
  · -- Sum case.
    intro x y _ _ hx hy
    show ν_loc (((x + y : locSubring P T s) : Localization.Away s)) < γ
    have h_add : ((x + y : locSubring P T s) : Localization.Away s) =
        ((x : locSubring P T s) : Localization.Away s) +
          ((y : locSubring P T s) : Localization.Away s) := rfl
    rw [h_add]
    refine lt_of_le_of_lt (ν_loc.map_add _ _) ?_
    exact max_lt hx hy
  · -- Smul case (locSubring acting on (locIdeal)^m).
    intro r x _ hx
    show ν_loc (((r • x : locSubring P T s) : Localization.Away s)) < γ
    have h_smul : ((r • x : locSubring P T s) : Localization.Away s) =
        ((r : locSubring P T s) : Localization.Away s) *
          ((x : locSubring P T s) : Localization.Away s) :=
      rfl
    rw [h_smul, map_mul]
    have hr_le : ν_loc ((r : locSubring P T s) : Localization.Away s) ≤ 1 :=
      h_locSubring_bound _ r.property
    calc ν_loc ((r : locSubring P T s) : Localization.Away s) *
            ν_loc ((x : locSubring P T s) : Localization.Away s)
        ≤ 1 * ν_loc ((x : locSubring P T s) : Localization.Away s) :=
          mul_le_mul_right' hr_le _
      _ = ν_loc ((x : locSubring P T s) : Localization.Away s) := one_mul _
      _ < γ := hx

end ValuationSpectrum
