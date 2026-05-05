/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornBaseSpaFinalBridgeStrong
import «Adic spaces».WedhornC1StrongSupplierBridge

/-!
# Wedhorn 8.34(ii) Supplier Assembly Skeleton

Highest-level caller theorem on the Wedhorn 8.34(ii) supplier route
toward Tate acyclicity. Composes the **unnormalized** abstract strong
C1 supplier `C1SupplierStrong_local C` with the existing chain of
landed bridges, producing the `hZavyalov_per_E` discharge consumed by
the final acyclicity assembly. All remaining dependencies are exposed
as named theorem hypotheses.

## Composition pipeline (each piece committed; see git log)

```
C1SupplierStrong_local C                                 ← residual H₃ (Tertiary lane)
  ↓  (via WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift,
     under H₂: ∀ D ∈ C.covers, D.T.Nonempty)
C1SupplierStrong_local C.insertDenom
  ↓  (via WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier
     under standard Tate hypotheses H₀)
∃ mk_S_D, h_in_D ∧ h_cover_D_nonzero          (per-D Finset, strong coverage)
  ↓  (via WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue
     under H₁: rationalOpen C.base.T C.base.s = Spa A A⁺
     and WedhornOutsideRescue.outside_rescue_pointwise_of_base_eq_Spa)
Ideal.span (biUnion mk_S_D) = ⊤  (h_span)
  ↓  (via StandardCover.hZavyalov_per_E_of_per_D_construction
     under standard rational-open ≠ ∅ premise)
∃ S, refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S
                                                  ← consumed by Tate acyclicity
```

`hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
(commit `b152aa7`) already wires steps 2-5; this file adds step 1
(the `insertDenom` lift) on top, exposing the unnormalized supplier as
a residual.

## What this file provides

* `hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa`
  — the assembly theorem composing all currently-landed pieces. Inputs:
  the standard Tate hypothesis bundle (H₀), the base-equals-Spa
  specialization (H₁), the cover-piece nonempty hypothesis (H₂), and
  the unnormalized abstract strong supplier (H₃). Output: the
  `hZavyalov_per_E` shape consumed by Tate acyclicity. Sorry-free,
  axiom-clean.

## Residual hypothesis list (shortest remaining dependency for closing acyclicity)

* **H₃ — `C1SupplierStrong_local C`**: the Wedhorn 8.34(ii) σ-and-ratio
  construction on the original (un-normalized) cover. Documented as
  the missing target signature `produce_C1SupplierStrong_local_via_Wedhorn_834`
  at `WedhornC1StrongSupplierBridge.lean:66`. Proof would proceed via
  pre-localisation at `C.base.s`, Cor 7.32 inside `Spa(A_loc, A_loc⁺)`,
  denominator clearing, and `f := σ * t * D.s ^ N`. Tertiary's
  `WEDHORN-EXTEND-VALUATION-LOC-TOPOLOGY-CONTINUITY` and Secondary's
  `WEDHORN-DOMINATING-UNIT-INEQUALITY-CORE` lanes are working toward
  this. Once landed, `H₃` is dischargeable directly from the Tate
  hypothesis bundle and the cover.

* **H₁ — `rationalOpen C.base.T C.base.s = Spa A A⁺`**: the base-Spa
  specialization assumed by `WedhornBaseSpaFinalBridgeStrong`. For
  rational coverings of the *full* adic spectrum (`C.base.T = ∅`,
  `C.base.s = 1`), this is automatic; for nested rational subsets the
  user must reduce to this case via a base-restriction step. The
  base-restriction reduction is a separate generalization (not in this
  file's scope).

* **H₂ — `∀ D ∈ C.covers, D.T.Nonempty`**: a mild non-emptiness
  hypothesis on cover-piece test families, required by
  `WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift`.
  Excludes only the degenerate `D.T = ∅` (basic-open-at-`D.s`) subcase.
  Trivially satisfied in any practical Wedhorn-style cover.

## Notes

* No root import; leaf-level file. Imports only the two highest-level
  Wedhorn supplier files (`WedhornBaseSpaFinalBridgeStrong`,
  `WedhornC1StrongSupplierBridge`) plus their transitive closure.
* No edits to other files. No final-acyclicity signature changes,
  no T001 / Lane B / Cor832 / Jacobson / faithful-flatness /
  non-open-prime content.
* Axioms (verified post-build): only `propext`, `Classical.choice`,
  `Quot.sound`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Wedhorn 8.34(ii) supplier assembly — `hZavyalov_per_E` discharge
under the standard Tate hypothesis bundle, base-equals-Spa
specialization, cover-piece nonemptiness, and the abstract unnormalized
strong C1 supplier on the original cover.**

Composes:

1. `WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift`
   — lifts the unnormalized strong supplier (H₃) to the normalized
   cover under H₂.
2. `WedhornBaseSpaFinalBridgeStrong.hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   — closes the chain to `hZavyalov_per_E` under H₀ and H₁.

The output is exactly the
`rationalOpen C.base.T C.base.s ≠ ∅ → ∃ S, refines_cover_per_E ∧
refines_contain ∧ refines_span_top` shape consumed by the final Tate
acyclicity assembly. -/
theorem hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    -- Residual H₁: base-Spa specialization (consumed by the outside-rescue
    -- pointwise-of-base-eq-Spa branch).
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    -- Residual H₂: cover-piece test-family non-emptiness (consumed by the
    -- insertDenom strong-supplier lift).
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    -- Residual H₃: the genuine Wedhorn 8.34(ii) σ-and-ratio supplier on
    -- the original (un-normalized) cover. The current external target.
    (h_C1_unnormalized : C1SupplierStrong_local C) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Step 1: lift the unnormalized supplier to the normalized cover.
  have h_C1_normalized : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty h_C1_unnormalized
  -- Step 2: close to hZavyalov_per_E via the base-Spa final bridge strong.
  exact hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa h_C1_normalized

/-- **Wedhorn 8.34(ii) supplier assembly — `hZavyalov_per_E` discharge
from honest Wedhorn 8.34-style single-`t` structural per-call data**
(T192 sibling of `hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa`).

Replaces the abstract residual `h_C1_unnormalized : C1SupplierStrong_local C`
with the **explicit single-`t` σ/N structural per-call provider**
`h_struct` consumed by T191's
`C1SupplierStrong_local_insertDenom_via_single_t_structural_data`. The
provider supplies, for each `D ∈ C.covers`, `v ∈ rationalOpen D.T D.s`,
and `t ∈ D.T` with `v.vle t D.s ∧ ¬ v.vle D.s 0`, an explicit
`(σ : A) (N : ℕ)` with:

* the base-side factorization `C.base.s = D.s * (σ * t * D.s ^ N)`,
* test-family integrality `∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)`,
* and the `f`-membership `v.vle (σ * t * D.s ^ N) C.base.s`.

These are exactly the honest Wedhorn 8.34(ii) σ/N data delivered by
T188's `rationalOpen_subset_via_single_t_sigma_N_data` and the T185
power-cleared `f`-construction lane.

Composition pipeline:

1. T191 (`C1SupplierStrong_local_insertDenom_via_single_t_structural_data`)
   → `C1SupplierStrong_local C.insertDenom` directly from `h_struct`
   under `h_covers_nonempty`. (T191 internally wraps the lift via
   `C1SupplierStrong_local_insertDenom_lift`, so no separate
   un-normalized lift step is needed here.)
2. `WedhornBaseSpaFinalBridgeStrong.hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   → closes to `hZavyalov_per_E` under H₀ (Tate hypothesis bundle) and
   H₁ (`rationalOpen C.base.T C.base.s = Spa A A⁺`).

This sibling theorem is the **same conclusion** as the unnormalized-
supplier version above, with the `h_C1_unnormalized` residual replaced
by the strictly-stronger explicit single-`t` structural provider. The
output is exactly the `hZavyalov_per_E` shape consumed by the final
Tate acyclicity assembly. Sorry-free, axiom-clean. -/
theorem hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    -- Residual H₁: base-Spa specialization (consumed by the outside-rescue
    -- pointwise-of-base-eq-Spa branch).
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    -- Residual H₂: cover-piece test-family non-emptiness (consumed by the
    -- T191 insertDenom strong-supplier from-structural-data wrapper).
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    -- Residual H₃: explicit single-`t` σ/N structural per-call provider —
    -- the strictly-stronger replacement of the abstract `C1SupplierStrong_local C`,
    -- matching T188's σ/N data shape and T191's structural-data input.
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Step 1: build the normalized strong C1 supplier directly from h_struct
  -- via T191. T191 internally bundles the un-normalized supplier and the
  -- insertDenom lift; we consume its output directly.
  have h_C1_normalized : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_via_single_t_structural_data
      C h_covers_nonempty h_struct
  -- Step 2: close to hZavyalov_per_E via the base-Spa final bridge strong.
  exact hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa h_C1_normalized

end ValuationSpectrum
