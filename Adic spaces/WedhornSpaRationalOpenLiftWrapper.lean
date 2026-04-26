/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornLocalizationLiftContinuityBounded

/-!
# Spa-rationalOpen wrapper for the bounded localization lift

The natural Wedhorn 8.34(ii) callsite for `valuationLocalizationLift_of_bounded`
(`Adic spaces/WedhornLocalizationLiftContinuityBounded.lean`) discharges
its three boundedness hypotheses (`hν_A₀`, `hv_T`, `hvs`) from a single
`v ∈ rationalOpen T s` plus the standard pair-of-definition direction
`hA₀_le : P.A₀ ≤ A⁺`. This file lands the wrapper.

## Hypothesis discharge structure

* `v ∈ rationalOpen T s` unpacks to `(v ∈ Spa A A⁺) ∧ (∀ t ∈ T, v.vle t s)
  ∧ ¬ v.vle s 0` — discharges `hv`, `hv_T`, `hvs` directly.

* `hA₀_le : P.A₀ ≤ A⁺` plus `v ∈ Spa A A⁺` discharges `hν_A₀ : ∀ a ∈
  P.A₀, v.vle a 1` via `vle_one_of_mem_spa hv (hA₀_le ha)`.

**Note on direction**: this requires `P.A₀ ≤ A⁺` (the standard
`Cor732.lean:207` / `SpaCompact.lean:412` setup), NOT `A⁺ ≤ P.A₀` (the
`CompatiblePlusSubring.aplus_le_pod` form, which is the opposite
direction and does NOT bound `v` on `P.A₀`).

## What this file provides

`valuationLocalizationLift_of_spa_rationalOpen` — the wrapper. Single
hypothesis `hv_rat : v ∈ rationalOpen T s` plus `hA₀_le : P.A₀ ≤ A⁺`
plus the standard `hopen` localization-topology data; produces the
localized Spa point + comap identity directly.

This is the **callsite-ready** form for Wedhorn 8.34(ii) downstream
consumers; no abstract continuity hypothesis, no separate boundedness
inputs.

## Notes

* No root import; leaf-level file.
* No edits to committed bridge files.
* No Lane B / Cor 8.32 / Jacobson / T001 / faithful-flatness /
  final-acyclicity content. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Spa-rationalOpen wrapper for the bounded localization lift**.

Given the standard Wedhorn-callsite hypotheses
* `hopen` — localization-topology openness data on `Localization.Away s`
* `hA₀_le : P.A₀ ≤ A⁺` — the pair-of-definition / plus-subring
  containment direction
* `hv_rat : v ∈ rationalOpen T s` — Spa-membership in the rational open

produces the localized Spa point `w` with the comap identity
`comap (algebraMap A _) w = v`, modulo the canonical
`localizationAwayPlusSubring s` plus-subring choice on
`Localization.Away s`.

**Proof**: unpack `hv_rat` to extract `(hv, hv_T, hvs)`. Use `hA₀_le` +
`vle_one_of_mem_spa` to derive `hν_A₀`. Apply
`valuationLocalizationLift_of_bounded`. -/
theorem valuationLocalizationLift_of_spa_rationalOpen
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (hA₀_le : P.A₀ ≤ A⁺)
    {v : Spv A} (hv_rat : v ∈ rationalOpen T s) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    ∃ w : Spv (Localization.Away s),
      w ∈ @Spa (Localization.Away s) _ (locTopology P T s hopen)
        (localizationAwayPlusSubring s).toSubring ∧
      comap (algebraMap A (Localization.Away s)) w = v := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  -- Unpack rationalOpen membership.
  obtain ⟨hv, hv_T, hvs⟩ := hv_rat
  -- Discharge hν_A₀ : ∀ a ∈ A₀, v.vle a 1 via P.A₀ ≤ A⁺ + vle_one_of_mem_spa.
  have hν_A₀ : ∀ a ∈ P.A₀, v.vle a 1 := fun a ha =>
    vle_one_of_mem_spa hv (hA₀_le ha)
  -- Apply the bounded lift theorem.
  exact valuationLocalizationLift_of_bounded P T s hopen hv hν_A₀ hv_T hvs

end ValuationSpectrum
