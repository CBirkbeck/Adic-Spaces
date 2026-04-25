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
