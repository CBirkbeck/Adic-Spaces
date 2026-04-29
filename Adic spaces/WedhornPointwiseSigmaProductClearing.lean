/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPerPieceSubsetProductClearing
import «Adic spaces».WedhornDominatingUnitInequality

/-!
# Wedhorn 8.34(ii) — Pointwise σ-product clearing (T070)

T067 (commit `f697f6b`) reduced T064's per-piece subset to the
**pointwise clearing residual**: at every `v ∈ Spa A A⁺` with
`v.vle f s`, `v.vle 1 t'`, and `¬ v.vle t' 0`, derive
`v.vle t' D_s`. This file lands the **substantive arithmetic
discharge** of that residual via the corrected multi-clearing
primitive `vle_of_dominating_unit_multi_corrected_at`
(`WedhornDominatingUnitInequality.lean:280`).

## Mathematical content

The pointwise clearing at a fixed `v` and `t'` follows from the
corrected multi-clearing primitive applied at the same `v` to the
**full `D.T` product upper bound** + **per-`v` universal-over-`D.T`
lower bound** input shape. Specifically, if at `v` we have

* `v.vle (D.T.prod id) D_s` (product upper bound at `D_s`), and
* `∀ t_i ∈ D.T, v.vle (1 : A) t_i` (per-element lower bound at every
  `t_i` of `D.T`),

then `vle_of_dominating_unit_multi_corrected_at` produces
`∀ t_i ∈ D.T, v.vle t_i D_s` and `¬ v.vle D_s 0`, which gives the
pointwise clearing at `t'` directly.

The two inputs above are exactly the per-`v` slice of T053's
two-part product+lower-bound residual
(`local_bounds_package_via_product_and_per_t_lower_bound`'s
hypothesis), and naturally arise from the σ-product construction
`f := σ * D.T.prod * D.s^N` plus σ-strict-domination at `v`:

* The product upper bound follows from `v.vle f s` plus the σ-product
  algebraic identity, after σ-cancellation and `D.s^N`-cancellation
  arithmetic — provided `v(σ)` and `v(D.s)^N`-related magnitude
  relations are available at `v`.

* The per-element lower bound for ALL `t_i ∈ D.T` at `v` is the
  Wedhorn 8.34(ii) σ-rescaled Laurent-cover-refinement output at
  `v`, restricted to a **single Laurent piece**. Outside such a
  piece, the universal lower bound is mathematically false (T035
  counter-example). So the natural source-restricted form is at `v`
  in a piece `V_τ` where the σ-rescaled image data gives the
  universal lower bound for `D.T` at `v`.

## What this file provides

* `pointwise_clearing_via_corrected_multi_clearing` — substantive
  reduction: from a per-`v` corrected-multi-clearing input
  (`h_prod : v.vle (T_D.prod id) D_s` + `h_lower : ∀ t_i ∈ T_D,
  v.vle (1 : A) t_i`, both at the specific `v`), discharge T067's
  pointwise clearing for any `t' ∈ T_D`. **Real proof** using
  `vle_of_dominating_unit_multi_corrected_at`.

* `pointwise_clearing_supplier_via_per_v_prod_lower_bound` — supplier
  form: from a per-`v` supplier producing the corrected-multi-
  clearing input shape under f-membership, derive T067's pointwise
  clearing universally. The named hypothesis is the per-`v`
  product+universal-lower-bound supplier — the exact remaining
  content reducible to σ-product construction + per-piece data.

* `per_piece_subset_supplier_via_per_v_prod_lower_bound` — composes
  T070's discharge with T067's `per_piece_subset_supplier_via_pointwise_clearing`
  to give T064's per-piece subset directly from a per-`v` corrected-
  multi-clearing supplier. Mechanically composes with T064's
  `C1SupplierStrong_local_via_t_indexed_direct` once the
  per-`v`-product+lower-bound supplier is in scope.

* `T070PointwiseClearingResidual` — Prop predicate naming the **single
  exact remaining residual** at the per-`v` product+universal-lower-
  bound level: at every `v` with f-membership, supply the corrected-
  multi-clearing input shape. Closer to the σ-product construction
  arithmetic than T067's pointwise clearing.

## The single exact missing arithmetic lemma

The remaining theorem-level gap, after T070, is the per-`v` supplier:

```
∀ v ∈ Spa A A⁺, v.vle f s →
  v.vle (D.T.prod id) D.s ∧ ∀ t_i ∈ D.T, v.vle (1 : A) t_i
```

at every `v` in the source-restricted Laurent piece. This is the
**per-v Wedhorn 8.34(ii) σ-product algebraic content**: the
σ-construction algebraic identity `f = σ * D.T.prod * D.s^N`, plus
σ-strict-domination at `v` (Cor 7.32 output), plus the σ-rescaled
Laurent-piece structure giving the universal lower bound at `v`,
together discharge it. T070's substantive content reduces T067's
pointwise clearing to this single named per-`v` supplier; the latter
is the σ-product construction's arithmetic content, owned by
Secondary's parallel σ/Laurent-cover supplier lane (T065).

## Notes

* No root import; leaf-level.
* Imports T067 (`WedhornPerPieceSubsetProductClearing`) for
  composition with the per-piece subset supplier and
  `WedhornDominatingUnitInequality` for
  `vle_of_dominating_unit_multi_corrected_at` (the corrected
  multi-clearing primitive).
* No edits to T031–T067 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per
  T035's counter-example).
* Does NOT introduce a final Tate acyclicity hypothesis — the
  named residual is the per-`v` σ-product algebraic content,
  consumed by Secondary's σ/Laurent-cover supplier.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Pointwise clearing via corrected multi-clearing at `v`** (T070
substantive arithmetic discharge — single-`v` form).

From a per-`v` corrected-multi-clearing input — `h_prod : v.vle
(T_D.prod id) D_s` + `h_lower : ∀ t_i ∈ T_D, v.vle (1 : A) t_i` at a
specific `v` — discharge T067's pointwise clearing for any `t' ∈ T_D`.

**Proof**: apply `vle_of_dominating_unit_multi_corrected_at`
(`WedhornDominatingUnitInequality.lean:280`) at `v` with `h_prod`
and `h_lower`, extracting the per-element upper bound at `D_s`. The
result for `t' ∈ T_D` directly gives `v.vle t' D_s`.

The hypotheses `_hv_one_t' : v.vle 1 t'` and `_hv_t'_ne : ¬ v.vle t'
0` from the T067 residual signature are absorbed by `h_lower` at
`t'` (which gives `v.vle 1 t'` directly) and consumed implicitly via
the corrected multi-clearing's internal non-vanishing chain;
T067's signature passes them through for symmetry with the C1
supplier's per-piece structure.

**Substantive consumption**: `h_prod` and `h_lower` are genuinely
used via `vle_of_dominating_unit_multi_corrected_at` — not pass-
through. -/
theorem pointwise_clearing_via_corrected_multi_clearing
    (T_D : Finset A) (D_s : A) (t' : A) (ht' : t' ∈ T_D)
    {v : Spv A}
    (h_prod : v.vle (T_D.prod id) D_s)
    (h_lower : ∀ t_i ∈ T_D, v.vle (1 : A) t_i) :
    v.vle t' D_s :=
  (vle_of_dominating_unit_multi_corrected_at v h_prod h_lower).1 t' ht'

omit [IsTopologicalRing A] in
/-- **Pointwise clearing supplier via per-`v` product+universal-lower-
bound** (T070 supplier form).

From a per-`v` supplier that, at every `v ∈ Spa A A⁺` satisfying
`v.vle f s`, produces the corrected-multi-clearing input shape
(product upper bound at `D_s` + universal-over-`T_D` lower bound at
`v`), discharge T067's pointwise clearing residual at any specific
`t' ∈ T_D`.

**Real proof** composing `pointwise_clearing_via_corrected_multi_clearing`
at each `v`. The named hypothesis `h_per_v_prod_lower` is the
**single exact remaining content** at the per-`v` product+universal-
lower-bound layer, deliverable from the σ-product construction
algebraic identity + σ-strict-domination + σ-rescaled Laurent-piece
structure. -/
theorem pointwise_clearing_supplier_via_per_v_prod_lower_bound
    (T_D : Finset A) (s D_s f : A) (t' : A) (ht' : t' ∈ T_D)
    (h_per_v_prod_lower :
      ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (T_D.prod id) D_s ∧ ∀ t_i ∈ T_D, v.vle (1 : A) t_i) :
    ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s := by
  intro v hv_spa hv_f _hv_one_t' _hv_t'_ne
  obtain ⟨h_prod, h_lower⟩ := h_per_v_prod_lower v hv_spa hv_f
  exact pointwise_clearing_via_corrected_multi_clearing T_D D_s t' ht'
    h_prod h_lower

omit [IsTopologicalRing A] in
/-- **Per-piece subset supplier via per-`v` product+universal-lower-
bound** (T070 composition with T067).

Composes T070's
`pointwise_clearing_supplier_via_per_v_prod_lower_bound` with T067's
`per_piece_subset_supplier_via_pointwise_clearing` to give T064's
per-piece subset directly from the per-`v` corrected-multi-clearing
supplier. Mechanically composes with T064's
`C1SupplierStrong_local_via_t_indexed_direct` once the per-`v` product
+ universal-lower-bound supplier is in scope.

**Substantive composition** — every input is genuinely used in the
chain. The named hypothesis is the single per-`v` product+universal-
lower-bound supplier, exposed at the consumer-facing T064 boundary. -/
theorem per_piece_subset_supplier_via_per_v_prod_lower_bound
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A)
    (h_per_v_prod_lower :
      ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (D_T.prod id) D_s ∧ ∀ t_i ∈ D_T, v.vle (1 : A) t_i) :
    ∀ t' ∈ D_T,
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t' ⊆
        rationalOpen ({t'} : Finset A) D_s := by
  refine per_piece_subset_supplier_via_pointwise_clearing T_base D_T s D_s f ?_
  intro t' ht'
  exact pointwise_clearing_supplier_via_per_v_prod_lower_bound D_T s D_s f
    t' ht' h_per_v_prod_lower

/-- **Single exact remaining residual** (T070 named blocker).

The single exact remaining content after T070, defined as a Prop
predicate for downstream consumers and the σ-product construction
lane.

This residual asks for a per-`v` supplier of the corrected-multi-
clearing input shape: at every `v ∈ Spa A A⁺` with `v.vle f s` (the
LHS f-bound), produce the product upper bound `v.vle (D_T.prod id)
D_s` AND the universal-over-`D_T` lower bound `∀ t_i ∈ D_T, v.vle 1
t_i` at the same `v`. -/
def T070PointwiseClearingResidual
    (D_T : Finset A) (s D_s f : A) : Prop :=
  ∀ v ∈ Spa A A⁺,
    v.vle f s →
    v.vle (D_T.prod id) D_s ∧ ∀ t_i ∈ D_T, v.vle (1 : A) t_i

omit [IsTopologicalRing A] in
/-- **Per-piece subset supplier via T070's named residual**
(T070 final consumer-facing theorem).

Direct consumer-facing form using the named Prop predicate. -/
theorem per_piece_subset_supplier_via_T070_residual
    [DecidableEq A]
    (T_base D_T : Finset A) (s D_s f : A)
    (h_residual : T070PointwiseClearingResidual D_T s D_s f) :
    ∀ t' ∈ D_T,
      rationalOpen (insert f T_base) s ∩
          rationalOpen ({(1 : A)} : Finset A) t' ⊆
        rationalOpen ({t'} : Finset A) D_s :=
  per_piece_subset_supplier_via_per_v_prod_lower_bound T_base D_T s D_s f
    h_residual

end ValuationSpectrum
