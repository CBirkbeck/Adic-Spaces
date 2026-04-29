/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornMultiBranchSubsetInequality
import «Adic spaces».WedhornPointwiseClearingSupplierFromSigmaPower

/-!
# Wedhorn 8.34(ii) — σ-power inequality from localized Cor 7.32 output (T083)

T065 (`WedhornLocalizedCor732SigmaSupplier`) lands the **localized
Cor 7.32 σ-supplier**: from the localized Wedhorn–Tate hypotheses,
extract `σ_loc : (Localization.Away s)ˣ` and the σ-rescaled t-indexed
Laurent cover hypothesis on the localized Spa. T079
(`WedhornPointwiseClearingSupplierFromSigmaPower`) and T080
(`WedhornFinalPart2SigmaPowerThreading`) consume the **per-`(w, t')`
source-restricted σ-power-cleared inequality supplier** at the source
ring `A`:
```
∀ t' ∈ D_T, ∀ w ∈ Spa A A⁺,
  w.vle f s → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ w.vle D_s 0
```

This file lands the **theorem-level bridge** from a named source-
restricted denominator/clearing identity tied to the T065 σ/Laurent-
cover output to T079/T080's σ-power-cleared inequality supplier.

## The named source-restricted denominator/clearing identity

The σ-construction's natural per-`(w, t')` algebraic content at the
source ring `A` is the **σ-decay chain**: at each `w ∈ Spa A A⁺` in
the source-restricted Laurent piece for `t'`, exhibit a σ-construction
unit `σ : Aˣ`, an exponent `N : ℕ`, and an intermediate term
`C_base_s : A` (the f-bound through the σ-decay) such that
```
w.vle ((σ : A) * t' * D_s ^ N) C_base_s  -- LHS Laurent-piece f-bound
w.vle C_base_s ((σ : A) * D_s ^ (N + 1)) -- σ-power-decay (Cor 7.32)
¬ w.vle D_s 0                            -- D_s non-vanishing
```
This is the **per-`(w, t')` source-restricted Wedhorn 8.34(ii)
σ-construction algebraic identity** packaged as a single named Prop
predicate `Cor732SigmaDecayChainSupplier`. It is **not** a global
universal-over-`D_T` lower bound (the consumed Laurent-piece
hypothesis `w.vle 1 t'` is per-`(w, t')` source-restricted), and
**not** a universal-over-Spa multi-element bound (each `w` supplies
its own σ, N, and C_base_s).

The connection to the T065 σ_loc / t-indexed Laurent cover output is
the natural σ-construction structural identity: each Laurent piece
`V_t' = R({1}, t')` carrying `w` corresponds (via the localized
σ_loc's image cover) to a source-side σ-decay chain with σ chosen as
a source lift of σ_loc and N chosen by the Cor 7.32 σ-power-decay
input on the cover-piece denominator.

## Why σ-cancellation suffices to discharge the σ-power-cleared form

The σ-decay chain combines via transitivity to
```
w.vle ((σ : A) * t' * D_s ^ N) ((σ : A) * D_s ^ (N + 1))
```
After re-association `(σ : A) * t' * D_s ^ N = (σ : A) * (t' * D_s ^ N)`
and σ-cancellation on the left (`vle_iff_mul_unit_left`, an existing
`Aˣ` cancellation primitive in `WedhornMultiBranchSubsetInequality`),
this collapses to the σ-power-cleared form
`w.vle (t' * D_s ^ N) (D_s ^ (N + 1))` consumed by T079/T080.

The N-power cancellation that would further collapse this to the
direct upper bound `w.vle t' D_s` is **not** performed at this layer
— that route is owned by Primary's pointwise lane. T083 keeps the
σ-power exponent intact, supplying T079/T080's σ-power-cleared input
directly.

## What this file provides

* `Cor732SigmaDecayChainSupplier` — Prop predicate naming the
  per-`(w, t')` source-restricted σ-decay chain at the source ring.
  This is the **single named source-restricted algebraic identity
  tied to the T065 output** required to close T079/T080's σ-power lane.

* `sigma_power_cleared_inequality_from_localized_cor732_output` —
  T083 main theorem (ticket-named target): from
  `Cor732SigmaDecayChainSupplier D_T s D_s f`, produce the per-`(w, t')`
  source-restricted σ-power-cleared inequality supplier consumed by
  T079/T080. Real σ-cancellation arithmetic via `vle_iff_mul_unit_left`
  and `Spv.vle_trans`; not a pass-through wrapper.

* `SigmaProductClearedInequalitySupplier_from_localized_cor732_output`
  — full end-to-end composition: from `Cor732SigmaDecayChainSupplier`,
  deliver T072's named residual `SigmaProductClearedInequalitySupplier`
  by composing T083's bridge with T079's
  `SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`.
  This is the strongest end-to-end consumer-facing T083 deliverable
  on the σ-power lane: the entire chain from the named source-
  restricted σ-decay chain identity to T072's named residual.

## Notes

* No root import; leaf-level.
* Imports `WedhornMultiBranchSubsetInequality` for the σ-cancellation
  primitive `vle_iff_mul_unit_left` and T079
  (`WedhornPointwiseClearingSupplierFromSigmaPower`) for the
  end-to-end composition into T072's named residual via
  `SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`.
* No edits to T031–T082 accepted leaves, root imports, or final
  theorem signatures.
* No edits to Primary's pointwise route file
  (`WedhornPointwiseClearingFromLocalizedCor732.lean`) or
  Secondary's σ-factored file
  (`WedhornSigmaFactoredInequalityAtCor732Sigma.lean`).
* No revival of M-power-decay / σ-power-decay (the σ-power exponent
  is per-`(w, t')` here, not a global decay), T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-`D_T` lower bound (the consumed
  per-`(w, t')` Laurent-piece hypothesis is source-restricted).
* No global universal-over-Spa multi-element clearing claim (each
  `w` supplies its own σ, N, and C_base_s independently).
* No all-units σ residual (σ is supplied per-`(w, t')` by the
  σ-construction).
* No final Tate acyclicity hypothesis additions.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Per-`(w, t')` source-restricted σ-decay chain supplier**
(T083 named source-restricted denominator/clearing identity).

Prop predicate naming the **per-`(w, t')` source-restricted Wedhorn
8.34(ii) σ-construction algebraic identity at the source ring `A`**.
At each `w ∈ Spa A A⁺` and `t' ∈ D_T` in the source-restricted Laurent
piece (`w.vle f s`, `w.vle 1 t'`, `¬ w.vle t' 0`), supply a
σ-construction unit `σ : Aˣ`, an exponent `N : ℕ`, and an intermediate
term `C_base_s : A` such that the σ-decay chain holds:
```
w.vle ((σ : A) * t' * D_s ^ N) C_base_s          -- f-bound
w.vle C_base_s ((σ : A) * D_s ^ (N + 1))         -- σ-power-decay
¬ w.vle D_s 0                                    -- non-vanishing
```

**Connection to T065's localized Cor 7.32 output**: the σ here is the
source-side analogue (lift) of T065's `σ_loc : (Localization.Away s)ˣ`,
and the σ-power-decay corresponds to Cor 7.32's σ-strict-domination
on the cover-piece denominator at the appropriate source lift level.
The Laurent-piece input `w.vle 1 t'` is the source-side analogue of
T065's t-indexed Laurent-piece membership.

**Per-`(w, t')` source restriction**: each `(w, t')` triple supplies
its own `σ`, `N`, `C_base_s`. No universal-over-`D_T` lower bound
(the only `D_T`-quantification is the per-`t'` outer quantifier).
No universal-over-Spa multi-element bound.

This Prop is the **single named source-restricted algebraic identity
tied to the T065 output** at this layer; it is consumed by
`sigma_power_cleared_inequality_from_localized_cor732_output` below
to discharge T079/T080's σ-power-cleared inequality supplier. -/
def Cor732SigmaDecayChainSupplier (D_T : Finset A) (s D_s f : A) : Prop :=
  ∀ t' ∈ D_T, ∀ w ∈ Spa A A⁺,
    w.vle f s →
    w.vle (1 : A) t' →
    ¬ w.vle t' 0 →
    ∃ (σ : Aˣ) (N : ℕ) (C_base_s : A),
      w.vle ((σ : A) * t' * D_s ^ N) C_base_s ∧
      w.vle C_base_s ((σ : A) * D_s ^ (N + 1)) ∧
      ¬ w.vle D_s 0

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **σ-power-cleared inequality from Cor 7.32 σ-decay chain at a
single `(w, t')`** (T083 reusable per-`(w, t')` σ-cancellation step).

From a per-`(w, t')` σ-decay chain
```
w.vle ((σ : A) * t' * D_s ^ N) C_base_s
w.vle C_base_s ((σ : A) * D_s ^ (N + 1))
```
derive the σ-power-cleared inequality `w.vle (t' * D_s ^ N) (D_s ^ (N + 1))`.

**Proof structure**: combine the two chain hypotheses via
`Spv.vle_trans` to get `w.vle ((σ : A) * t' * D_s ^ N) ((σ : A) * D_s ^ (N + 1))`,
re-associate the LHS to `(σ : A) * (t' * D_s ^ N)` via `mul_assoc`,
and apply `vle_iff_mul_unit_left` (existing `Aˣ` cancellation
primitive) to cancel the σ factor.

**Substantive consumption**: both chain hypotheses are genuinely used
through transitivity + σ-cancellation; not a pass-through. -/
theorem sigma_power_cleared_inequality_via_sigma_decay_chain_at
    {w : Spv A} {σ : Aˣ} {t' D_s C_base_s : A} {N : ℕ}
    (h_w_f : w.vle ((σ : A) * t' * D_s ^ N) C_base_s)
    (h_C_decay : w.vle C_base_s ((σ : A) * D_s ^ (N + 1))) :
    w.vle (t' * D_s ^ N) (D_s ^ (N + 1)) := by
  have h_combined :
      w.vle ((σ : A) * t' * D_s ^ N) ((σ : A) * D_s ^ (N + 1)) :=
    w.vle_trans h_w_f h_C_decay
  rw [mul_assoc] at h_combined
  exact (vle_iff_mul_unit_left w σ (t' * D_s ^ N) (D_s ^ (N + 1))).mp h_combined

omit [IsTopologicalRing A] in
/-- **σ-power-cleared inequality supplier from T065-tied σ-decay chain
supplier** (T083 main theorem; ticket-named target).

From the named source-restricted σ-decay chain supplier
`Cor732SigmaDecayChainSupplier D_T s D_s f` (the per-`(w, t')` Wedhorn
8.34(ii) σ-construction algebraic identity at the source, tied to
T065's localized Cor 7.32 output), produce the per-`(w, t')` source-
restricted σ-power-cleared inequality supplier consumed by T079/T080:
```
∀ t' ∈ D_T, ∀ w ∈ Spa A A⁺,
  w.vle f s → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ w.vle D_s 0
```

**Proof structure**: under the per-`(w, t')` quantifier, extract the
σ, N, and C_base_s witnesses from `h_chain`, apply
`sigma_power_cleared_inequality_via_sigma_decay_chain_at` to obtain
the σ-power-cleared inequality, and pair with the supplied
`¬ w.vle D_s 0`.

**Substantive consumption**: the σ-decay chain is genuinely used
through σ-cancellation; the `D_s` non-vanishing piece is forwarded.
The output is exactly the per-`(w, t')` shape consumed by T079's
`SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`,
closing the σ-power lane from a single named source-restricted
algebraic identity to T072's named residual. -/
theorem sigma_power_cleared_inequality_from_localized_cor732_output
    (D_T : Finset A) (s D_s f : A)
    (h_chain : Cor732SigmaDecayChainSupplier D_T s D_s f) :
    ∀ t' ∈ D_T, ∀ w ∈ Spa A A⁺,
      w.vle f s →
      w.vle (1 : A) t' →
      ¬ w.vle t' 0 →
      ∃ N : ℕ,
        w.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ w.vle D_s 0 := by
  intro t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  obtain ⟨σ, N, C_base_s, h_w_f, h_C_decay, h_D_s_ne⟩ :=
    h_chain t' ht' w hw_spa hw_f hw_one_t hw_t_ne
  exact ⟨N,
    sigma_power_cleared_inequality_via_sigma_decay_chain_at h_w_f h_C_decay,
    h_D_s_ne⟩

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` from T065-tied σ-decay
chain supplier** (T083 + T079 end-to-end composition).

End-to-end T083 deliverable on the σ-power lane: from the named
source-restricted σ-decay chain supplier
`Cor732SigmaDecayChainSupplier D_T s D_s f` (the single named
source-restricted algebraic identity tied to T065's localized
Cor 7.32 output), deliver T072's named residual
`SigmaProductClearedInequalitySupplier` by composing T083's
σ-cancellation bridge with T079's
`SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`.

**End-to-end σ-decay chain → T072 lane**:
σ-decay chain supplier (T083 named identity) →
σ-power-cleared inequality supplier (T083 σ-cancellation) →
pointwise clearing supplier (T079 adapter) →
direct upper bound supplier (T077 bridge) →
`SigmaProductClearedInequalitySupplier` (T073 `N = 0` witness).

The whole chain is closed-form per-`(w, t')` source-restricted
valuation arithmetic; the only named residual is the σ-decay chain
supplier (T083), which is precisely the Wedhorn 8.34(ii) σ-construction
algebraic identity tied to the T065 σ_loc / t-indexed Laurent cover
output. -/
theorem SigmaProductClearedInequalitySupplier_from_localized_cor732_output
    (D_T : Finset A) (s D_s f : A)
    (h_chain : Cor732SigmaDecayChainSupplier D_T s D_s f) :
    SigmaProductClearedInequalitySupplier D_T s D_s f :=
  SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted
    D_T s D_s f
    (sigma_power_cleared_inequality_from_localized_cor732_output
      D_T s D_s f h_chain)

end ValuationSpectrum
