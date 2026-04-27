/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StandardCover

/-!
# Wedhorn Standard-Cover Refinement: single-`t` C1 helpers

Wedhorn §8.34(ii) refinement step (the C1 component documented in
`StandardCover.lean:306-429`): for `D ∈ C.covers` and a single point
`v ∈ rationalOpen D.T D.s`, produce `f : A` such that

* `v ∈ rationalOpen (insert f C.base.T) C.base.s`, and
* `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s`.

This file lands the standard-shape branch and the **σ-equipped
unit-rescaled-denominator branch** of the single-`f` helper, plus a
companion **multi-`F` unit-rescaled algebraic identity** that establishes
the rational-open transfer law underlying the σ-equipped reduction.
The truly general non-standard branch — where `D.s` is **not** a unit
multiple of `C.base.s` — requires the full Cor 7.32 σ-domination
construction over a multi-element test family and is recorded as the
precise missing API; see the docblock at the end of this file.

## What this file provides

1. `exists_single_f_refinement_at_t_of_standardShape` — extends
   `StandardCover.exists_single_f_refinement_of_standardShape`
   (`StandardCover.lean:519`) with an explicit `t : A` and
   `ht : t ∈ D.T`. Proof: takes `f := f₀` from the standard-shape
   witness; the explicit `t` is a no-op marker for downstream callers.

2. `rationalOpen_image_union_base_eq_of_unit_rescaled` — algebraic
   identity: when `(σ : A) * D.s = C.base.s` for a unit `σ : Aˣ` and
   `D ⊆ C.base`, the rational open `R(σ • D.T ∪ C.base.T, C.base.s)`
   equals `R(D.T, D.s)` exactly. This is the *denominator-equalisation*
   identity underlying the σ-equipped C1 reduction.

3. `exists_single_f_refinement_at_t_of_singleton_unit_rescaled` — the
   **strongest single-`f` non-standard-shape C1 conclusion** provable
   from existing rational-open algebra: when `D.T = {t}` and there is a
   unit `σ : Aˣ` with `(σ : A) * D.s = C.base.s`, the single-`f`
   conclusion discharges with `f := (σ : A) * t`.

4. Precise blocker docblock (`exists_single_f_refinement_at_t_via_dominating_unit`)
   for the truly general non-standard branch, where `D.s` and `C.base.s`
   generate distinct principal ideals (no unit rescaling) AND/OR `D.T`
   has multiple elements (single `f` cannot encode multiple constraints).
   This is the Wedhorn / Cor 7.32 σ-domination content, with explicit
   pointers to the missing valuation-inequality API.

## Wedhorn ingredients used

* `StandardCover.exists_single_f_refinement_of_standardShape`
  (`StandardCover.lean:519`) — standard-shape branch dispatch.
* `Spv.mul_vle_mul_left`, `Spv.vle_mul_cancel`
  (`ValuationSpectrum.lean:63-65`) — valuation cancellation at units.
* `not_vle_zero_of_isUnit` (`ValuationSpectrum.lean:224`) — units are
  non-zero in valuation.
* `Cor732.exists_dominating_unit` (`Cor732.lean:206`) — referenced in the
  missing-API docblock for the truly general residual.

No Lane B / Cor 8.32 / Jacobson / faithful-flatness / T001 content.
No new final acyclicity hypotheses.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

/-- **Wedhorn standard-cover refinement at an explicit `t ∈ D.T`,
standard-shape branch**.

Given `D` already in the form `R(insert f₀ C.base.T, C.base.s)` for some
`f₀ : A` (the witnessed standard-shape form), the single-`t` helper
discharges by `f := f₀`; the explicit `t ∈ D.T` is a downstream
bookkeeping witness not used in the standard-shape proof.

Mirror of `StandardCover.exists_single_f_refinement_of_standardShape`
(`StandardCover.lean:519`) with the additional explicit `t` parameter
documenting the manager-target shape. -/
theorem exists_single_f_refinement_at_t_of_standardShape
    [DecidableEq A] (C : RationalCovering A) (D : RationalLocData A)
    (f₀ : A)
    (hD_shape : rationalOpen D.T D.s =
      rationalOpen (insert f₀ C.base.T) C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s)
    (t : A) (_ht : t ∈ D.T) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s :=
  exists_single_f_refinement_of_standardShape C D f₀ hD_shape hv

/-- **Multi-`F` rational-open identity at unit-rescaled denominator
(Wedhorn 8.34(ii) algebraic core)**.

When the cover-piece `D` is contained in the base
(`R(D.T, D.s) ⊆ R(C.base.T, C.base.s)`) AND there is a unit `σ : Aˣ`
rescaling `D.s` to `C.base.s` (`(σ : A) * D.s = C.base.s`), the rational
open at the **σ-rescaled test family** unioned with `C.base.T` and
denominator `C.base.s` equals `R(D.T, D.s)` exactly:

```
R(σ • D.T ∪ C.base.T, C.base.s) = R(D.T, D.s)
```

where `σ • D.T = D.T.image ((σ : A) * ·)`.

**Proof core**: `Spv.mul_vle_mul_left` lifts the per-`t` inequality
`v.vle t D.s ↔ v.vle ((σ : A) * t) C.base.s` (using `(σ : A) * D.s =
C.base.s`); `Spv.vle_mul_cancel` at the unit `σ` provides the inverse
direction. The non-zero clause `¬ v.vle D.s 0 ↔ ¬ v.vle C.base.s 0` is
the `mul_vle_mul_left` of `D.s ↦ 0` against `σ`, again using `hσ`.

**Specialisations**:
* `σ := 1` (with `D.s = C.base.s`) gives the same-denominator multi-`F`
  identity `R(D.T ∪ C.base.T, C.base.s) = R(D.T, D.s)`.
* `D.T = {t}` (with arbitrary unit-rescaled `σ`) feeds into the
  single-`f` consumer
  `exists_single_f_refinement_at_t_of_singleton_unit_rescaled` below. -/
theorem rationalOpen_image_union_base_eq_of_unit_rescaled
    [DecidableEq A] (C : RationalCovering A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s) :
    rationalOpen (D.T.image ((σ : A) * ·) ∪ C.base.T) C.base.s =
      rationalOpen D.T D.s := by
  ext v
  constructor
  · rintro ⟨hv_spa, hvFT, hvCs⟩
    refine ⟨hv_spa, fun t ht => ?_, ?_⟩
    · -- For t ∈ D.T, lift v.vle ((σ : A) * t) C.base.s back to v.vle t D.s.
      have hv_σt : v.vle ((σ : A) * t) C.base.s :=
        hvFT _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
      have hvσ_ne : ¬ v.vle (σ : A) 0 := not_vle_zero_of_isUnit σ.isUnit v
      have h := hv_σt
      rw [← hσ, mul_comm (σ : A) t, mul_comm (σ : A) D.s] at h
      exact v.vle_mul_cancel hvσ_ne h
    · -- ¬ v.vle D.s 0 from ¬ v.vle C.base.s 0 by cancelling σ.
      intro hvDs0
      have h := v.mul_vle_mul_left hvDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hvCs h
  · intro hv
    have hvCbase := hD_sub hv
    obtain ⟨hv_spa, hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    refine ⟨hv_spa, fun b hb => ?_, hvCs⟩
    rcases Finset.mem_union.mp hb with hF | hT_mem
    · -- b ∈ σ • D.T: b = (σ : A) * t for some t ∈ D.T.
      obtain ⟨t, htD, rfl⟩ := Finset.mem_image.mp hF
      have hvt : v.vle t D.s := hvD t htD
      have h1 : v.vle (t * (σ : A)) (D.s * (σ : A)) :=
        v.mul_vle_mul_left hvt (σ : A)
      have h2 : v.vle ((σ : A) * t) ((σ : A) * D.s) := by
        rw [mul_comm (σ : A) t, mul_comm (σ : A) D.s]; exact h1
      rw [hσ] at h2; exact h2
    · exact hvT b hT_mem

/-- **Single-`t` C1 helper for singleton cover piece with unit-rescaled
denominator**.

The strongest **single-`f`** non-standard-shape C1 conclusion provable
from existing rational-open algebra without invoking the full Cor 7.32
σ-domination construction. Hypotheses:

* the cover piece `D` has a singleton test family `D.T = {t}`;
* there is a unit `σ : Aˣ` rescaling the denominator: `(σ : A) * D.s =
  C.base.s` (equivalently, `D.s` and `C.base.s` generate the same
  principal ideal);
* the cover piece is contained in the base
  (`hD_sub : R(D.T, D.s) ⊆ R(C.base.T, C.base.s)`; this is exactly
  `C.hsubset` for `D ∈ C.covers`).

Conclusion: the C1 single-`f` conclusion at any `v ∈ R(D.T, D.s)`
discharges with `f := (σ : A) * t`.

**Why singleton + unit-rescaled**: a single inserted `f` can encode at
most ONE valuation inequality in the new rational open. When `D.T` has
multiple elements, multiple constraints must hold simultaneously on the
plus-piece-at-`f`, which a single `f` cannot enforce algebraically
without the σ-domination over a multi-element test family. When `D.s`
is not a unit multiple of `C.base.s`, the denominator transfer
`v.vle t D.s ↔ v.vle (?) C.base.s` cannot be inverted via simple
multiplication by a unit. The full Wedhorn 8.34(ii) construction
addresses both via Cor 7.32; see the missing-API docblock below.

**Proof**: take `f := (σ : A) * t`. Both clauses reduce to the
multi-`F`-style cancellation `v.vle ((σ : A) * t) C.base.s ↔ v.vle t D.s`
(via `mul_vle_mul_left` and `vle_mul_cancel` at the unit `σ`), with
`(σ : A) * D.s` rewritten as `C.base.s` via `hσ`. Specialisation of
`rationalOpen_image_union_base_eq_of_unit_rescaled` to `D.T = {t}`. -/
theorem exists_single_f_refinement_at_t_of_singleton_unit_rescaled
    [DecidableEq A] (C : RationalCovering A) (D : RationalLocData A)
    (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (t : A) (hT : D.T = {t})
    (σ : Aˣ) (hσ : (σ : A) * D.s = C.base.s)
    {v : Spv A} (hv : v ∈ rationalOpen D.T D.s) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s := by
  refine ⟨(σ : A) * t, ?_, ?_⟩
  · -- Membership: v ∈ R(insert ((σ : A) * t) C.base.T, C.base.s).
    have hvCbase := hD_sub hv
    obtain ⟨hv_spa, hvD, _hvDs⟩ := hv
    obtain ⟨_, hvT, hvCs⟩ := hvCbase
    have hvt : v.vle t D.s := hvD t (hT ▸ Finset.mem_singleton_self t)
    refine ⟨hv_spa, fun b hb => ?_, hvCs⟩
    rcases Finset.mem_insert.mp hb with rfl | hb_base
    · -- b = (σ : A) * t: lift v.vle t D.s to v.vle ((σ : A) * t) C.base.s.
      have h1 : v.vle (t * (σ : A)) (D.s * (σ : A)) :=
        v.mul_vle_mul_left hvt (σ : A)
      have h2 : v.vle ((σ : A) * t) ((σ : A) * D.s) := by
        rw [mul_comm (σ : A) t, mul_comm (σ : A) D.s]; exact h1
      rw [hσ] at h2; exact h2
    · exact hvT b hb_base
  · -- Subset: R(insert ((σ : A) * t) C.base.T, C.base.s) ⊆ R(D.T, D.s).
    intro w hw
    obtain ⟨hw_spa, hwIns, hwCs⟩ := hw
    have hw_σt : w.vle ((σ : A) * t) C.base.s :=
      hwIns ((σ : A) * t) (Finset.mem_insert_self _ _)
    have hwσ_ne : ¬ w.vle (σ : A) 0 := not_vle_zero_of_isUnit σ.isUnit w
    have hw_t : w.vle t D.s := by
      have h := hw_σt
      rw [← hσ, mul_comm (σ : A) t, mul_comm (σ : A) D.s] at h
      exact w.vle_mul_cancel hwσ_ne h
    have hwDs : ¬ w.vle D.s 0 := by
      intro hwDs0
      have h := w.mul_vle_mul_left hwDs0 (σ : A)
      rw [zero_mul, mul_comm D.s (σ : A), hσ] at h
      exact hwCs h
    refine ⟨hw_spa, fun t' ht' => ?_, hwDs⟩
    rw [hT, Finset.mem_singleton] at ht'
    subst ht'
    exact hw_t

/-! ## Wedhorn 8.34(ii) Laurent cover σ-inversion primitives

Wedhorn 8.34(ii) (PDF page 84) refines a rational cover into a Laurent
cover via `Cor732.exists_dominating_unit`: from σ-strict-domination over
a generating family `T = {f_0, ..., f_n}`, form the Laurent cover
generated by the σ-rescaled elements `{σ⁻¹ * f_1, …, σ⁻¹ * f_r}`. At
each `w ∈ Spa A A⁺`, some `t_w ∈ T` has `w(σ⁻¹ * t_w) ≥ 1` (i.e., `w`
is in the Laurent piece where this rescaled element is a unit).

The two lemmas below provide the **per-`w` algebraic core** of this
Laurent refinement: σ-strict-domination at `w` lifts to an
`σ⁻¹`-rescaled "valuation ≥ 1" inequality, whose pointwise existential
form is the Laurent piece membership.

These primitives are the **corrected route** (after T023's blocker on
the false uniform σ-power-decay shape and T024's blocker on the false
direct `vle_of_dominating_unit_multi` signature): instead of trying to
extract a per-`t'` rational-subset bound from σ-strict-dom + f-membership
alone (which is mathematically impossible per the T023/T024 counter-
examples), Wedhorn's actual proof builds a Laurent cover and uses cover-
level acyclicity (Lemma 8.33) to conclude. -/

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **σ-inversion at strict domination**. From σ-strict-domination
`w.vle (σ : A) τ` (which is the conclusion of `Cor732.exists_dominating_unit`
at a given `w`), deduce that the σ-rescaled element `σ⁻¹ * τ` has
valuation at least 1 at `w`: `w.vle 1 (((σ⁻¹ : Aˣ) : A) * τ)`.

This is the **algebraic core** of Wedhorn 8.34(ii)'s Laurent cover
refinement (PDF page 84): the Laurent cover generated by
`{σ⁻¹ * t | t ∈ T}` is exactly the cover where each `σ⁻¹ * t` becomes
a unit on its respective Laurent piece, and at every `w` some `σ⁻¹ * t_w`
indeed satisfies `w(σ⁻¹ * t_w) ≥ 1`.

Proof: multiply both sides of `w.vle (σ : A) τ` by `((σ⁻¹ : Aˣ) : A)`
on the LEFT via `ValuativeRel.mul_vle_mul_right`; the LHS becomes
`((σ⁻¹ : Aˣ) : A) * (σ : A) = 1` by `Units.inv_mul`. -/
theorem one_vle_inv_unit_mul_of_strict_dom_at
    (w : Spv A) {σ : Aˣ} {τ : A} (hστ : w.vle (σ : A) τ) :
    w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) := by
  letI : ValuativeRel A := w.toValuativeRel
  have h_mul :
      w.vle (((σ⁻¹ : Aˣ) : A) * (σ : A)) (((σ⁻¹ : Aˣ) : A) * τ) :=
    ValuativeRel.mul_vle_mul_right hστ ((σ⁻¹ : Aˣ) : A)
  rwa [show ((σ⁻¹ : Aˣ) : A) * (σ : A) = (1 : A) from Units.inv_mul σ]
    at h_mul

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- **Per-`w` Laurent-piece membership from Cor 7.32 σ-strict-domination
existential**.

Combines `one_vle_inv_unit_mul_of_strict_dom_at` with the existential
σ-strict-domination supplier from `Cor732.exists_dominating_unit`: at
each `w`, given `∃ τ ∈ T, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)`
(the per-`w` slice of the Cor 7.32 output), there exists `τ ∈ T` such
that:

* `w.vle 1 (((σ⁻¹ : Aˣ) : A) * τ)` — the σ-rescaled element has
  valuation at least 1 at `w` (so `w` is in the Laurent piece where
  `σ⁻¹ * τ` is a unit), and
* `¬ w.vle τ 0` — `τ` is non-vanishing at `w`.

The collection `{V_τ := {w | w.vle 1 (σ⁻¹ * τ)} | τ ∈ T}` thus forms a
**Laurent cover** of `Spa A A⁺`: at each `w`, some τ wins. This is the
foundational per-`w` step for Wedhorn 8.34(ii)'s Laurent cover
refinement (PDF page 84, second paragraph of the proof of Lemma 8.34
part (ii)). -/
theorem exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom
    {w : Spv A} {σ : Aˣ} {T : Finset A}
    (hστ : ∃ τ ∈ T, w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)) :
    ∃ τ ∈ T,
      w.vle (1 : A) (((σ⁻¹ : Aˣ) : A) * τ) ∧ ¬ w.vle τ 0 := by
  letI : ValuativeRel A := w.toValuativeRel
  obtain ⟨τ, hτ, hστ_left, hστ_right⟩ := hστ
  refine ⟨τ, hτ, one_vle_inv_unit_mul_of_strict_dom_at w hστ_left, ?_⟩
  intro h_τ_zero
  exact hστ_right (w.vle_trans h_τ_zero (ValuativeRel.zero_vle (σ : A)))

/-! ### Cor 7.32-based Laurent cover formation (T026)

Bridges T025's σ-inversion primitives to the existing `rationalOpen` /
Wedhorn rational-subset API: at every `w ∈ Spa A A⁺` with Cor 7.32
σ-strict-domination over a finite generating family `T`, the σ-rescaled
Laurent piece `rationalOpen ({(1 : A)} : Finset A) ((σ⁻¹ : Aˣ) * τ)`
contains `w` for some `τ ∈ T`. The collection
`{rationalOpen {1} (σ⁻¹ * τ) | τ ∈ T}` is a Laurent cover of
`Spa A A⁺` matching Wedhorn 8.34(ii)'s actual proof on PDF page 84:
the rescaled elements `σ⁻¹ * τ` become units on their respective
Laurent pieces, and the cover `{V_τ}` is the natural target of
Wedhorn's Lemma 8.33 (binary Laurent cover acyclicity) for cover-level
acyclicity.

These bridges intentionally avoid the **full `RationalCovering`
packaging**: each per-piece `RationalLocData A` would require a
non-trivial `hopen` verification (the localization at `σ⁻¹ * τ` having
the right openness data — which depends on whether `τ` is a unit,
generally NOT the case for arbitrary `τ ∈ T` in Wedhorn 8.34(ii)).
The lighter cover-membership theorem suffices for downstream
acyclicity arguments. -/

omit [IsTopologicalRing A] in
/-- **Cor 7.32 Laurent piece membership at `w`** (σ-rescaled form).

At any `w ∈ Spa A A⁺`, given Cor 7.32 σ-strict-domination over a
finite family `T` (the existential output of
`Cor732.exists_dominating_unit`), there exists `τ ∈ T` such that `w`
lies in the σ-rescaled Laurent piece
`rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)`.

This Laurent piece corresponds to the "≥ 1" half-space
`{v ∈ Spa A A⁺ | v.vle 1 (σ⁻¹ * τ) ∧ ¬ v.vle (σ⁻¹ * τ) 0}` for the
single rescaled element `σ⁻¹ * τ`. It is exactly the Laurent piece
where `σ⁻¹ * τ` is a "valuation-≥-1" element (and hence becomes a
unit on the localized adic spectrum on this piece). Wedhorn 8.34(ii)
(PDF page 84) uses precisely this piece structure for the Laurent
cover refinement.

Proof: T025's `exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom`
provides `τ ∈ T` with `w.vle 1 (σ⁻¹ * τ)` and `¬ w.vle τ 0`. We then
verify the `rationalOpen` membership: the singleton `{1}` membership
condition unfolds to the first inequality, and the non-vanishing of
`σ⁻¹ * τ` follows from `¬ w.vle τ 0` by left-multiplying by `σ` (which
maps the hypothetical `w.vle (σ⁻¹ * τ) 0` to `w.vle τ 0`). -/
theorem cor732_laurent_piece_membership_at
    {σ : Aˣ} {T : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T, v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A))
    {w : Spv A} (hw : w ∈ Spa A A⁺) :
    ∃ τ ∈ T,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) := by
  letI : ValuativeRel A := w.toValuativeRel
  obtain ⟨τ, hτ, h_one_le, h_τ_ne⟩ :=
    exists_one_vle_inv_unit_mul_at_of_cor732_strict_dom (hσ_dom w hw)
  refine ⟨τ, hτ, hw, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact h_one_le
  · intro h_inv_τ_zero
    apply h_τ_ne
    have h_mul :
        w.vle ((σ : A) * (((σ⁻¹ : Aˣ) : A) * τ)) ((σ : A) * 0) :=
      ValuativeRel.mul_vle_mul_right h_inv_τ_zero (σ : A)
    have h_lhs : (σ : A) * (((σ⁻¹ : Aˣ) : A) * τ) = τ := by
      rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [h_lhs, mul_zero] at h_mul
    exact h_mul

omit [IsTopologicalRing A] in
/-- **Spa is covered by the Cor 7.32 σ-rescaled Laurent pieces**
(set-level cover statement).

Existential per-`w` form of `cor732_laurent_piece_membership_at`,
phrased as a set-level cover-membership: every `w ∈ Spa A A⁺` lies in
some σ-rescaled Laurent piece `rationalOpen {1} (σ⁻¹ * τ)` for `τ ∈ T`.

The set-level statement
`Spa A A⁺ ⊆ ⋃ τ ∈ T, rationalOpen {1} (σ⁻¹ * τ)` follows from this by
`Set.subset_def` + `Set.mem_iUnion₂` unfolding (no extra content). -/
theorem cor732_laurent_cover_covers_spa
    {σ : Aˣ} {T : Finset A}
    (hσ_dom :
      ∀ v ∈ Spa A A⁺, ∃ τ ∈ T, v.vle (σ : A) τ ∧ ¬ v.vle τ (σ : A)) :
    ∀ w ∈ Spa A A⁺, ∃ τ ∈ T,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) :=
  fun _ hw => cor732_laurent_piece_membership_at hσ_dom hw

/-! ## Precise missing API for the truly general non-standard branch

The `_of_singleton_unit_rescaled` helper above covers the **two
algebraically clean** subcases of the non-standard branch:
1. `σ := 1` with `D.s = C.base.s` and `D.T = {t}` (same-denominator
   singleton).
2. Arbitrary unit `σ : Aˣ` with `(σ : A) * D.s = C.base.s` and
   `D.T = {t}` (unit-rescaled-denominator singleton).

The truly general residual case — `|D.T| ≥ 2` AND/OR `D.s` not a unit
multiple of `C.base.s` — requires the explicit Wedhorn / Zavyalov §2.3
**multi-element σ-domination** construction. The exact missing target
signature is documented below.

### Target signature (general non-standard residual)

```
theorem exists_single_f_refinement_at_t_via_dominating_unit
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
      MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (D : RationalLocData A) (hD : D ∈ C.covers)
    (v : Spv A) (hv : v ∈ rationalOpen D.T D.s)
    (t : A) (ht : t ∈ D.T)
    (_hvt : v.vle t D.s) (_hvD_s : ¬ v.vle D.s 0) :
    ∃ f : A,
      v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
      rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T D.s
```

### Proof sketch (Wedhorn 8.34(ii) / not implemented here)

1. Apply `Cor732.exists_dominating_unit` (`Cor732.lean:206`) to a
   carefully chosen finite test family `T_test ⊆ A` (containing
   appropriate combinations of `D.T`, `D.s`, `C.base.T`, `C.base.s`).
   This yields a unit `σ : Aˣ` with `∀ w ∈ Spa A A⁺, ∃ τ ∈ T_test,
   w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A)` (strict domination).

2. Set `f := (σ : A) * t * D.s ^ (N - 1)` for an exponent `N` chosen
   large enough that `σ`'s domination of `T_test` clears the
   denominator across all `w ∈ Spa(A, A⁺)`.

3. Verify membership: `v.vle f C.base.s` from the chain
   `v(f) = v(σ) * v(t) * v(D.s)^(N-1) ≤ v(C.base.s)` using `_hvt`,
   `_hvD_s`, and σ's domination at `v`.

4. Verify subset: `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`. For
   arbitrary `w` in the plus-piece-at-`f`, σ-domination transfers
   `w(f) ≤ w(C.base.s)` into `w(t') ≤ w(D.s)` for **every**
   `t' ∈ D.T` (multi-element transfer; singleton case is the
   `_of_singleton_unit_rescaled` helper above) and `w(D.s) ≠ 0`.

### Precise missing valuation-inequality API

The proof step 4 requires a **multi-element σ-clearing lemma** with
target signature

```
lemma vle_of_dominating_unit_multi
    {σ : Aˣ} {f s D_s : A} (T_D : Finset A) (N : ℕ)
    (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (hσ_dom : ∀ w ∈ Spa A A⁺, ∃ τ ∈ T_D ∪ {D_s},
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    {w : Spv A} (hw : w ∈ Spa A A⁺) (hw_f : w.vle f s) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0
```

Closest existing API:
* `Cor732.exists_dominating_unit` (`Cor732.lean:206`) — produces `σ`
  with the per-Spa-point domination, but does NOT supply the multi-`t'`
  conclusion at a single `w`.
* `RationalSubsets.rationalOpen_inter` (`RationalSubsets.lean:72`) —
  algebraic intersection of two rational opens; useful for the
  multi-element case but does not handle the σ-power product
  `D.s^(N-1)`.
* `ValuativeRel.mul_vle_mul`, `Spv.mul_vle_mul_left`,
  `Spv.vle_mul_cancel` — single-multiplication cancellation at units;
  the multi-element / power-product case requires iterating these along
  with the σ-domination per `t' ∈ D.T`.

### Why this is genuinely Wedhorn-content (not new)

Step 4's transfer is precisely Wedhorn's "dominating unit clears the
denominator" lemma (Wedhorn 8.34(ii) / Hübner 3.7). It is NOT a
faithful-flatness or Cor 8.32 argument; it is purely a valuation-
inequality manipulation using σ's `Cor732`-supplied domination plus
finite-element bookkeeping for the test family.

### Where it slots in

After the truly general non-standard helper lands,
`StandardCover.exists_single_f_refining_point_in_D` (target signature
documented at `StandardCover.lean:365-372`) follows by varying `t` over
the (necessarily finite, in the Spa-quasi-compact sense) family of
inequalities that hold at `v` for some `t ∈ D.T`. Combined with
`SpaCompact.isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`
finite-extraction (C2) and `StandardCover.spanTop_iff_noCommonZero_spa`
(C3) this completes `StandardCover.exists_zavyalov_candidate_family`
(target signature documented at `StandardCover.lean:1043`).

### Repository status

This file currently provides the standard-shape branch and the
σ-equipped unit-rescaled-denominator singleton branch (the two
algebraically clean reductions of the non-standard form), plus the
multi-`F` rational-open identity underlying both. The truly general
non-standard branch — multi-element `D.T` and/or non-unit-rescalable
`D.s` — is the next concrete formalisation target along the Wedhorn
8.34(ii) chain; this file's docblock isolates its precise Lean
signature and the precise valuation-inequality API needed to land it. -/

end ValuationSpectrum
