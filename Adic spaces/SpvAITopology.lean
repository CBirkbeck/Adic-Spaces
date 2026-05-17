/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpvAI
import «Adic spaces».RationalSubsets
import «Adic spaces».ValuationSpectrumCompact

/-!
# Spectral structure on `Spv(A, I)` (Wedhorn 7.5) — T-SPV-AI-WEDHORN-710

Per Wedhorn 7.5 (p. 57–58): `Spv(A, I)` is a spectral space, and the
"rational subsets" `Spv(A,I)(T/s)` for `T ⊆ A` finite with `I ⊆ √(T·A)`
form a basis of quasi-compact open subsets stable under finite
intersection.

This is the topological infrastructure that bridges `Spv.IsInSpvAI`
(the algebraic disjunct from `SpvAI.lean`) to the Wedhorn 7.35 Spa
compactness statement.

## Main definitions

* `ValuationSpectrum.SpvAI A I` : the set `Spv(A, I)` as a subset of
  `Spv A`, equipped with the disjunctive condition `Spv.IsInSpvAI`.
* `ValuationSpectrum.SpvAI.rationalSubset T s` : the rational subset
  `Spv(A,I)(T/s)` per Wedhorn 7.5.

## Status

This file currently contains **only the definitional framework**. The
spectrality proof (Wedhorn 7.5 (1)) and the retraction continuity
(Wedhorn 7.5 (2)) are TODO; each is substantive (multi-step proof
using Proposition 3.31 / spectral-space machinery). See the per-
declaration docstrings for the proof plans.

## References

* [Wedhorn 2019] Section 7.1, Lemma 7.5 (p. 57–58), arXiv:1910.05934.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`Spv(A, I)` as a subset of `Spv A`.** -/
def SpvAI (A : Type*) [CommRing A] (I : Ideal A) : Set (Spv A) :=
  { v : Spv A | Spv.IsInSpvAI v I }

/-- **Rational subset `Spv(A, I)(T/s)` (Wedhorn 7.5).** For `T ⊆ A`
finite, `s ∈ A`, this is `{v ∈ Spv(A, I) : v(t) ≤ v(s) ≠ 0 ∀ t ∈ T}`. -/
def SpvAI.rationalSubset (I : Ideal A) (T : Finset A) (s : A) :
    Set (Spv A) :=
  SpvAI A I ∩ { v : Spv A | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 }

/-- **Wedhorn 7.5 (i): rational subsets stable under finite intersection.**
The intersection of two rational subsets is again a rational subset.

Specifically, for `T_1` with `I ⊆ √(T_1·A)` and `T_2` with `I ⊆ √(T_2·A)`,
the intersection `Spv(A,I)(T_1/s_1) ∩ Spv(A,I)(T_2/s_2)` equals
`Spv(A,I)(T/(s_1·s_2))` where `T = T_1·T_2` (pointwise products).

This is Wedhorn 7.5(i) at p. 57. -/
theorem SpvAI.rationalSubset_inter (I : Ideal A) [DecidableEq A]
    (T₁ T₂ : Finset A) (s₁ s₂ : A)
    (hs₁_in : s₁ ∈ T₁) (hs₂_in : s₂ ∈ T₂) :
    SpvAI.rationalSubset I T₁ s₁ ∩ SpvAI.rationalSubset I T₂ s₂ =
    SpvAI.rationalSubset I (T₁ ×ˢ T₂ |>.image (fun p => p.1 * p.2)) (s₁ * s₂) := by
  ext v
  simp only [Set.mem_inter_iff, SpvAI.rationalSubset, Set.mem_setOf_eq,
    Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨hv_in, hv_t₁, hv_s₁⟩, _, hv_t₂, hv_s₂⟩
    refine ⟨hv_in, ?_, ?_⟩
    · -- ∀ t ∈ T₁ × T₂ products, v(t₁·t₂) ≤ v(s₁·s₂).
      intro x hx
      obtain ⟨⟨t₁, t₂⟩, hp, h_eq⟩ := hx
      simp only [Finset.mem_product] at hp
      obtain ⟨ht₁, ht₂⟩ := hp
      subst h_eq
      letI : ValuativeRel A := v.toValuativeRel
      have hwv_t₁ := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) t₁ s₁).mp
        (hv_t₁ t₁ ht₁)
      have hwv_t₂ := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) t₂ s₂).mp
        (hv_t₂ t₂ ht₂)
      refine (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mpr ?_
      rw [map_mul, map_mul]
      exact mul_le_mul' hwv_t₁ hwv_t₂
    · -- ¬ v(s₁·s₂) ≤ 0 follows from each ≠ 0.
      letI : ValuativeRel A := v.toValuativeRel
      have h_s₁_ne : ValuativeRel.valuation A s₁ ≠ 0 := by
        intro h_eq
        apply hv_s₁
        refine (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mpr ?_
        rw [h_eq, map_zero]
      have h_s₂_ne : ValuativeRel.valuation A s₂ ≠ 0 := by
        intro h_eq
        apply hv_s₂
        refine (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mpr ?_
        rw [h_eq, map_zero]
      intro h_vle
      have h_le := (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) (s₁ * s₂) 0).mp h_vle
      rw [map_zero, le_zero_iff, map_mul, mul_eq_zero] at h_le
      rcases h_le with h₁ | h₂
      · exact h_s₁_ne h₁
      · exact h_s₂_ne h₂
  · rintro ⟨hv_in, hv_T, hv_s_prod⟩
    -- Decompose: from `v(s₁·s₂) ≠ 0`, get v(s₁) ≠ 0 and v(s₂) ≠ 0.
    letI : ValuativeRel A := v.toValuativeRel
    have h_s₁s₂_ne : ValuativeRel.valuation A (s₁ * s₂) ≠ 0 := by
      intro h_eq
      apply hv_s_prod
      refine (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mpr ?_
      rw [h_eq, map_zero]
    rw [map_mul, mul_ne_zero_iff] at h_s₁s₂_ne
    obtain ⟨h_s₁_ne, h_s₂_ne⟩ := h_s₁s₂_ne
    have h_s₁_n_vle : ¬ v.vle s₁ 0 := by
      intro h_vle
      apply h_s₁_ne
      have := (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) s₁ 0).mp h_vle
      rw [map_zero, le_zero_iff] at this
      exact this
    have h_s₂_n_vle : ¬ v.vle s₂ 0 := by
      intro h_vle
      apply h_s₂_ne
      have := (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) s₂ 0).mp h_vle
      rw [map_zero, le_zero_iff] at this
      exact this
    refine ⟨⟨hv_in, ?_, h_s₁_n_vle⟩, hv_in, ?_, h_s₂_n_vle⟩
    · -- ∀ t₁ ∈ T₁, v(t₁) ≤ v(s₁). Use s₂ ∈ T₂: v(t₁·s₂) ≤ v(s₁·s₂), cancel v(s₂).
      intro t₁ ht₁
      have ht_in : ∃ a : A × A, (a.1 ∈ T₁ ∧ a.2 ∈ T₂) ∧ a.1 * a.2 = t₁ * s₂ :=
        ⟨(t₁, s₂), ⟨ht₁, hs₂_in⟩, rfl⟩
      have h_prod : v.vle (t₁ * s₂) (s₁ * s₂) := hv_T (t₁ * s₂) ht_in
      have h_le := (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) (t₁ * s₂) (s₁ * s₂)).mp h_prod
      rw [map_mul, map_mul] at h_le
      refine (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) t₁ s₁).mpr ?_
      have h_s₂_pos : 0 < ValuativeRel.valuation A s₂ := zero_lt_iff.mpr h_s₂_ne
      rw [mul_comm _ (ValuativeRel.valuation A s₂),
        mul_comm _ (ValuativeRel.valuation A s₂)] at h_le
      exact (mul_le_mul_iff_right₀ h_s₂_pos).mp h_le
    · -- ∀ t₂ ∈ T₂, v(t₂) ≤ v(s₂). Symmetric using s₁ ∈ T₁.
      intro t₂ ht₂
      have ht_in : ∃ a : A × A, (a.1 ∈ T₁ ∧ a.2 ∈ T₂) ∧ a.1 * a.2 = s₁ * t₂ :=
        ⟨(s₁, t₂), ⟨hs₁_in, ht₂⟩, rfl⟩
      have h_prod : v.vle (s₁ * t₂) (s₁ * s₂) := hv_T (s₁ * t₂) ht_in
      have h_le := (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) (s₁ * t₂) (s₁ * s₂)).mp h_prod
      rw [map_mul, map_mul] at h_le
      refine (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation A) t₂ s₂).mpr ?_
      have h_s₁_pos : 0 < ValuativeRel.valuation A s₁ := zero_lt_iff.mpr h_s₁_ne
      exact (mul_le_mul_iff_right₀ h_s₁_pos).mp h_le

/-- **`SpvAI.rationalSubset` is contained in `SpvAI`.** Trivial from
the intersection definition. -/
theorem SpvAI.rationalSubset_subset (I : Ideal A) (T : Finset A) (s : A) :
    SpvAI.rationalSubset I T s ⊆ SpvAI A I :=
  fun _ hv => hv.1

/-- **`v ∈ SpvAI.rationalSubset I T s ↔ v ∈ SpvAI I ∧ ∀ t ∈ T, v.vle t s ∧ v.vle s 0`.** -/
theorem SpvAI.mem_rationalSubset (I : Ideal A) (T : Finset A) (s : A) (v : Spv A) :
    v ∈ SpvAI.rationalSubset I T s ↔
      v ∈ SpvAI A I ∧ (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 := by
  simp only [SpvAI.rationalSubset, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

/-- **`SpvAI` membership characterisation.** -/
theorem Spv.mem_SpvAI (v : Spv A) (I : Ideal A) :
    v ∈ SpvAI A I ↔ Spv.IsInSpvAI v I := Iff.rfl

/-- **Microbial valuations are in `SpvAI`.** Trivial via the microbial
disjunct of `Spv.IsInSpvAI`. -/
theorem Spv.isInSpvAI_of_isMicrobial (I : Ideal A) {v : Spv A}
    (h : letI : ValuativeRel A := v.toValuativeRel
      Valuation.IsMicrobial (ValuativeRel.valuation A)) :
    Spv.IsInSpvAI v I := Or.inr h

/-- **Wedhorn 7.5(ii), microbial case.** Given `v` microbial in `SpvAI I`
and a basic open W (`∀ i ∈ g, v.vle i g_0` and `¬ v.vle g_0 0`),
there exists a rational subset of `SpvAI I` containing `v` and inside `W`.

The construction: by `IsMicrobial`, pick `d ∈ A` with `1 ≤ v(g_0 * d)`
(via `v(d) ≥ v(g_0)⁻¹` from `Γ_v = cΓ_v`). Then `T' := {g_i * d : i ∈ g} ∪ {1}`,
`s' := g_0 * d`. The element `1 ∈ T'` makes `√(T' · A) = A ⊇ I` (so
`SpvAI.rationalSubset` is a valid basis element). -/
theorem SpvAI.exists_rationalSubset_microbial [DecidableEq A]
    (I : Ideal A) {v : Spv A}
    (h_micr : letI : ValuativeRel A := v.toValuativeRel
      Valuation.IsMicrobial (ValuativeRel.valuation A))
    (g_0 : A) (g : Finset A)
    (hg : ∀ i ∈ g, v.vle i g_0) (hg_0 : ¬ v.vle g_0 0) :
    ∃ (T : Finset A) (s : A),
      (1 : A) ∈ T ∧
      v ∈ SpvAI.rationalSubset I T s ∧
      SpvAI.rationalSubset I T s ⊆
        {w | (∀ i ∈ g, w.vle i g_0) ∧ ¬ w.vle g_0 0} := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  -- v(g_0) ≠ 0 from hg_0.
  have h_vg0_ne : wv g_0 ≠ 0 := by
    intro h_eq
    apply hg_0
    refine (Valuation.Compatible.vle_iff_le (v := wv) g_0 0).mpr ?_
    rw [h_eq, map_zero]
  have h_vg0_pos : 0 < wv g_0 := zero_lt_iff.mpr h_vg0_ne
  -- IsMicrobial: ∃ d with v(g_0)⁻¹ ≤ v(d) (i.e., 1 ≤ v(g_0 * d)).
  obtain ⟨d, h_vd_ge, _, h_inv_g0_le_vd⟩ := h_micr (wv g_0)⁻¹ (inv_pos.mpr h_vg0_pos)
  -- v(g_0 * d) ≥ v(g_0) * v(g_0)⁻¹ = 1.
  have h_vg0d_ge_one : 1 ≤ wv (g_0 * d) := by
    rw [map_mul]
    calc 1 = wv g_0 * (wv g_0)⁻¹ := (mul_inv_cancel₀ h_vg0_ne).symm
      _ ≤ wv g_0 * wv d := mul_le_mul_left' h_inv_g0_le_vd _
  -- v(g_0 * d) ≠ 0 since 1 ≤ ... < ⊤.
  have h_vg0d_ne : wv (g_0 * d) ≠ 0 := by
    intro h_eq
    rw [h_eq] at h_vg0d_ge_one
    exact absurd h_vg0d_ge_one (by simp)
  -- v(d) ≠ 0 from v(g_0 * d) ≠ 0.
  have h_vd_ne : wv d ≠ 0 := by
    intro h_eq
    apply h_vg0d_ne
    rw [map_mul, h_eq, mul_zero]
  -- Build T' := g.image (·*d) ∪ {1}, s' := g_0 * d.
  refine ⟨g.image (· * d) ∪ {1}, g_0 * d, ?_, ?_, ?_⟩
  · -- 1 ∈ T'.
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · -- v ∈ SpvAI.rationalSubset I T' s'.
    refine ⟨Or.inr h_micr, ?_, ?_⟩
    · -- ∀ t ∈ T', v.vle t (g_0 * d).
      intro t ht
      rcases Finset.mem_union.mp ht with ht_g | ht_one
      · -- t = i * d for some i ∈ g. v(t) = v(i) * v(d) ≤ v(g_0) * v(d) = v(g_0 * d).
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht_g
        refine (Valuation.Compatible.vle_iff_le (v := wv) (i * d) (g_0 * d)).mpr ?_
        rw [map_mul, map_mul]
        have hvi_le := (Valuation.Compatible.vle_iff_le (v := wv) i g_0).mp (hg i hi)
        exact mul_le_mul_right' hvi_le _
      · -- t = 1, v(1) ≤ v(g_0 * d) since 1 ≤ v(g_0 * d).
        rw [Finset.mem_singleton] at ht_one
        subst ht_one
        refine (Valuation.Compatible.vle_iff_le (v := wv) 1 (g_0 * d)).mpr ?_
        rw [map_one]
        exact h_vg0d_ge_one
    · -- ¬ v.vle (g_0 * d) 0.
      intro h_vle
      apply h_vg0d_ne
      have := (Valuation.Compatible.vle_iff_le (v := wv) (g_0 * d) 0).mp h_vle
      rw [map_zero, le_zero_iff] at this
      exact this
  · -- SpvAI.rationalSubset I T' s' ⊆ W.
    intro w hw
    obtain ⟨hw_in, hw_T, hw_s⟩ := hw
    refine ⟨?_, ?_⟩
    · -- ∀ i ∈ g, w.vle i g_0.
      intro i hi
      -- w(i * d) ≤ w(g_0 * d). Divide both sides by w(d) (= w(g_0 * d) / w(g_0)).
      have h_id_in : i * d ∈ g.image (· * d) ∪ {1} :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have h_id_le_gd : w.vle (i * d) (g_0 * d) := hw_T (i * d) h_id_in
      -- w(g_0 * d) ≠ 0 → w(g_0) ≠ 0 ∧ w(d) ≠ 0.
      letI : ValuativeRel A := w.toValuativeRel
      set ww := ValuativeRel.valuation A with hww_def
      have h_wgd_ne : ww (g_0 * d) ≠ 0 := by
        intro h_eq
        apply hw_s
        refine (Valuation.Compatible.vle_iff_le (v := ww) (g_0 * d) 0).mpr ?_
        rw [h_eq, map_zero]
      rw [map_mul, mul_ne_zero_iff] at h_wgd_ne
      obtain ⟨h_wg0_ne, h_wd_ne⟩ := h_wgd_ne
      -- Translate h_id_le_gd to ww.
      have h_id_le_gd' := (Valuation.Compatible.vle_iff_le (v := ww) (i * d) (g_0 * d)).mp h_id_le_gd
      rw [map_mul, map_mul] at h_id_le_gd'
      -- ww(i) * ww(d) ≤ ww(g_0) * ww(d) → ww(i) ≤ ww(g_0).
      have h_wd_pos : 0 < ww d := zero_lt_iff.mpr h_wd_ne
      refine (Valuation.Compatible.vle_iff_le (v := ww) i g_0).mpr ?_
      exact (mul_le_mul_iff_left₀ h_wd_pos).mp h_id_le_gd'
    · -- ¬ w.vle g_0 0.
      intro h_vle
      apply hw_s
      letI : ValuativeRel A := w.toValuativeRel
      set ww := ValuativeRel.valuation A
      have h_wg0_zero := (Valuation.Compatible.vle_iff_le (v := ww) g_0 0).mp h_vle
      rw [map_zero, le_zero_iff] at h_wg0_zero
      refine (Valuation.Compatible.vle_iff_le (v := ww) (g_0 * d) 0).mpr ?_
      rw [map_mul, h_wg0_zero, zero_mul, map_zero]

/-- **Wedhorn 7.5(ii), cofinality-disjunct case.** Given `v` satisfying the
cofinality disjunct of `IsInSpvAI` (for each `s_i` in a finite generating set
`S ⊆ I`, `CofinalValue v s_i`), and a basic open W
(`∀ i ∈ g, v.vle i g_0` and `¬ v.vle g_0 0`), there exists a rational subset
of `SpvAI I` containing `v` and inside `W`.

The construction: pick `k` such that `v(s_i)^k < v(g_0)` for all generators `s_i`
(via per-generator cofinality + finite max). Then
`T' := g ∪ S.image (·^k)`, `s' := g_0`. The membership `S ⊆ I` makes
`√(T' · A) ⊇ √(S · A) ⊇ S`, so `I ⊆ √(T' · A)`. -/
theorem SpvAI.exists_rationalSubset_cofinality [DecidableEq A]
    (I : Ideal A) {v : Spv A} (h_in : Spv.IsInSpvAI v I)
    (S : Finset A) (hS_in_I : ∀ s ∈ S, s ∈ I)
    (h_cofinal : ∀ s ∈ S,
      letI : ValuativeRel A := v.toValuativeRel
      Valuation.CofinalValue (ValuativeRel.valuation A) s)
    (g_0 : A) (g : Finset A)
    (hg : ∀ i ∈ g, v.vle i g_0) (hg_0 : ¬ v.vle g_0 0) :
    ∃ (T : Finset A) (s : A),
      g ⊆ T ∧
      v ∈ SpvAI.rationalSubset I T s ∧
      SpvAI.rationalSubset I T s ⊆
        {w | (∀ i ∈ g, w.vle i g_0) ∧ ¬ w.vle g_0 0} := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  -- v(g_0) ≠ 0 from hg_0.
  have h_vg0_ne : wv g_0 ≠ 0 := by
    intro h_eq
    apply hg_0
    refine (Valuation.Compatible.vle_iff_le (v := wv) g_0 0).mpr ?_
    rw [h_eq, map_zero]
  have h_vg0_pos : 0 < wv g_0 := zero_lt_iff.mpr h_vg0_ne
  -- For each s ∈ S, ∃ k_s with v(s)^k_s < v(g_0).
  have h_per_s : ∀ s ∈ S, ∃ k : ℕ, wv s ^ k < wv g_0 := by
    intro s hs
    exact h_cofinal s hs (wv g_0) h_vg0_pos
  choose k_s hk_s using h_per_s
  -- Take K := 1 + max over S of k_s.
  let K : ℕ := S.attach.sup (fun ⟨s, hs⟩ => k_s s hs) + 1
  -- Build T' := g ∪ S.image (·^K), s' := g_0.
  refine ⟨g ∪ S.image (· ^ K), g_0, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left
  · -- v ∈ SpvAI.rationalSubset I T' g_0.
    refine ⟨h_in, ?_, hg_0⟩
    · -- ∀ t ∈ T', v.vle t g_0.
      intro t ht
      rcases Finset.mem_union.mp ht with ht_g | ht_S
      · exact hg t ht_g
      · -- t = s^K for some s ∈ S. v(s^K) ≤ v(s)^k_s < v(g_0).
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht_S
        refine (Valuation.Compatible.vle_iff_le (v := wv) (s ^ K) g_0).mpr ?_
        rw [map_pow]
        -- (v s)^K ≤ (v s)^{k_s s hs} < v g_0.
        have h_K_ge : K ≥ k_s s hs + 1 := by
          show S.attach.sup (fun ⟨s, hs⟩ => k_s s hs) + 1 ≥ k_s s hs + 1
          apply Nat.add_le_add_right
          exact Finset.le_sup (f := fun ⟨s', hs'⟩ => k_s s' hs') (Finset.mem_attach _ ⟨s, hs⟩)
        have h_vs_le_one : wv s ≤ 1 := (h_cofinal s hs).le_one
        -- (wv s)^K ≤ (wv s)^{k_s s hs} (since wv s ≤ 1, larger exp = smaller).
        have h_pow_mono : wv s ^ K ≤ wv s ^ (k_s s hs) := by
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h_K_ge)
          rw [hj, pow_add]
          conv_rhs => rw [← mul_one (wv s ^ (k_s s hs))]
          exact mul_le_mul_left' (Left.pow_le_one_of_le h_vs_le_one _) _
        exact lt_of_le_of_lt h_pow_mono (hk_s s hs) |>.le
  · -- SpvAI.rationalSubset I T' g_0 ⊆ W.
    intro w hw
    obtain ⟨_, hw_T, hw_s⟩ := hw
    refine ⟨fun i hi => hw_T i (Finset.mem_union_left _ hi), hw_s⟩

/-- **The refined topology on `SpvAI I` (Wedhorn 7.5).** Generated by the
rational subsets `SpvAI.rationalSubset I T s`. This is the **spectral
topology** on `Spv(A, I)` that makes rational subsets a basis of qc opens
(Wedhorn 7.5(ii) with the refined topology). It is **strictly finer** than
the subspace topology inherited from `Spv A`, per Wedhorn Remark 7.6. -/
def SpvAI.topology (I : Ideal A) : TopologicalSpace (SpvAI A I) :=
  TopologicalSpace.generateFrom
    { s : Set (SpvAI A I) | ∃ T : Finset A, ∃ b : A,
      s = Subtype.val ⁻¹' SpvAI.rationalSubset I T b }

/-- **Wedhorn 7.5(ii) combined.** For `v ∈ SpvAI I` with cofinality
witnessed by a FG `S ⊆ I` (when not microbial) and a basic open W
around `v`, there's a `SpvAI` rational subset inside `W` containing `v`.

Unified statement combining `exists_rationalSubset_microbial` and
`exists_rationalSubset_cofinality`. -/
theorem SpvAI.exists_rationalSubset [DecidableEq A]
    (I : Ideal A) {v : Spv A} (h_in : Spv.IsInSpvAI v I)
    (S : Finset A) (hS_in_I : ∀ s ∈ S, s ∈ I)
    (h_cofinal_or_micr : (∀ s ∈ S,
      letI : ValuativeRel A := v.toValuativeRel
      Valuation.CofinalValue (ValuativeRel.valuation A) s) ∨
      letI : ValuativeRel A := v.toValuativeRel
      Valuation.IsMicrobial (ValuativeRel.valuation A))
    (g_0 : A) (g : Finset A)
    (hg : ∀ i ∈ g, v.vle i g_0) (hg_0 : ¬ v.vle g_0 0) :
    ∃ (T : Finset A) (s : A),
      v ∈ SpvAI.rationalSubset I T s ∧
      SpvAI.rationalSubset I T s ⊆
        {w | (∀ i ∈ g, w.vle i g_0) ∧ ¬ w.vle g_0 0} := by
  rcases h_cofinal_or_micr with h_cof | h_micr
  · -- Cofinality disjunct: use exists_rationalSubset_cofinality.
    obtain ⟨T, s, _, hv_in, h_sub⟩ :=
      exists_rationalSubset_cofinality I h_in S hS_in_I h_cof g_0 g hg hg_0
    exact ⟨T, s, hv_in, h_sub⟩
  · -- Microbial disjunct: use exists_rationalSubset_microbial.
    obtain ⟨T, s, _, hv_in, h_sub⟩ :=
      exists_rationalSubset_microbial I h_micr g_0 g hg hg_0
    exact ⟨T, s, hv_in, h_sub⟩

/-! ## Wedhorn 7.5(2)/(3) — retraction `r : Spv A → Spv(A,I)` and properties

The retraction's underlying map is already defined in `CharacteristicSubgroup.lean`
as `ValuationSpectrum.restrictIdeal : Spv A → Spv A`. These signatures formalise
that the image lies in `SpvAI`, and that the typed map is a continuous spectral
retraction (Wedhorn 7.5(2)) which preserves nonvanishing on `I` (Wedhorn 7.5(3)). -/

/-- **Wedhorn 7.5(2) image.** The `restrictIdeal v I` valuation lies in `Spv(A,I)`. -/
theorem restrictIdeal_mem_SpvAI (v : Spv A) (I : Ideal A) :
    restrictIdeal v I ∈ SpvAI A I :=
  sorry

/-- **Wedhorn 7.1.2 — typed retraction `r : Spv A → SpvAI A I`.** -/
noncomputable def SpvAI.retraction (I : Ideal A) : Spv A → SpvAI A I :=
  fun v => ⟨restrictIdeal v I, restrictIdeal_mem_SpvAI v I⟩

/-- **Wedhorn 7.5(2)** (retraction property). `r(v) = v` for `v ∈ Spv(A,I)`. -/
theorem SpvAI.retraction_eq_self (I : Ideal A) (v : SpvAI A I) :
    SpvAI.retraction I v.1 = v :=
  sorry

/-- **Wedhorn 7.5(2)** (continuity). `r : Spv A → Spv(A,I)` is continuous,
where target carries `SpvAI.topology I`. -/
theorem SpvAI.retraction_continuous (I : Ideal A) :
    @Continuous _ _ inferInstance (SpvAI.topology I) (SpvAI.retraction I) :=
  sorry

/-- **Wedhorn 7.5(2)** (spectral). `r : Spv A → Spv(A,I)` is a spectral map:
the preimage of a basic QC open `SpvAI.rationalSubset I T s` under `r` is
the rational subset `Spv(A)(T/s)`. **AUDIT 2026-05-17**: hypothesis corrected
to use `radical` (matching Wedhorn 7.5(1)'s basis condition `I ⊆ √(T·A)`). -/
theorem SpvAI.retraction_preimage_rationalSubset (I : Ideal A) [DecidableEq A]
    (T : Finset A) (s : A)
    (hT : I ≤ (Ideal.span ((T : Set A) ∪ {s})).radical) :
    SpvAI.retraction I ⁻¹' (Subtype.val ⁻¹' SpvAI.rationalSubset I T s) =
      { v : Spv A | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 } :=
  sorry

/-- **Wedhorn 7.5(3).** `v ∈ Spv A` with `v(I) ≠ 0` (i.e. some `a ∈ I` with
`v(a) ≠ 0`) ⇒ `r(v)(I) ≠ 0`. -/
theorem SpvAI.retraction_ideal_ne_zero {I : Ideal A} {v : Spv A}
    (h : ∃ a ∈ I, ¬ v.vle a 0) :
    ∃ a ∈ I, ¬ (restrictIdeal v I).vle a 0 :=
  sorry

end ValuationSpectrum

/-! ## Wedhorn 7.5(1) basis + spectrality of Spv(A,I) -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Wedhorn 7.5(1) basis.** The collection `R = { SpvAI.rationalSubset I T s |
s ∈ A, T ⊆ A finite, I ⊆ √(T · A) }` forms a basis of quasi-compact opens of
the spectral topology `SpvAI.topology I`. -/
theorem SpvAI.rationalSubset_isBasis [DecidableEq A] (I : Ideal A) :
    @TopologicalSpace.IsTopologicalBasis (SpvAI A I) (SpvAI.topology I)
      { U : Set (SpvAI A I) | ∃ T : Finset A, ∃ s : A,
        I ≤ (Ideal.span ((T : Set A) ∪ {s})).radical ∧
        U = Subtype.val ⁻¹' SpvAI.rationalSubset I T s } :=
  sorry

/-! ### Sub-breakdown for T-Spv.2 (Wedhorn 7.5(1)(iv) spectrality of Spv(A,I))

Wedhorn's proof of Spv(A,I) spectral (p.58 last paragraph) uses:
- Spv(A) constructible topology is compact (Wedhorn Prop 3.23)
- The retraction r : (Spv A)_cons → Spv(A,I) (in the `R̂` topology) is continuous + surjective
- Hence sets in R̂ are open AND closed (constructible)
- Apply Mathlib's spectral-space constructor (Wedhorn Prop 3.31). -/

-- T-Spv.2.a REMOVED (audit 2026-05-17): the constructible-topology compactness
-- of Wedhorn 3.23 is ALREADY realized in the project's
-- `ValuationSpectrumCompact.lean` via `ιSpv_bool` + closed-range in Tychonoff
-- cube. The Spv(A,I) spectrality proof can reference that existing
-- infrastructure directly (via importing `ValuationSpectrumCompact`); no
-- separate T-Spv.2.a wrapper is needed.

/-- **(T-Spv.2.b)** Restriction-to-retraction `r : Spv A → Spv(A,I)` is surjective
(every `v ∈ Spv(A,I)` is its own restriction). -/
theorem SpvAI.retraction_surjective (I : Ideal A) :
    Function.Surjective (SpvAI.retraction I) :=
  sorry

/-! ### T-Spv.2 decomposition (Wedhorn 7.5(1)(iv) via Prop 3.31)

Wedhorn 7.5(1)(iv) proof outline (p.58):
1. **Wedhorn 4.7**: Spv A is spectral with basis of QC opens.
2. **Wedhorn 3.23**: Spv A's constructible topology is compact.
3. **Wedhorn 3.31** (general spectral constructor): a QC Kolmogorov space with
   a basis of open-and-closed subspaces is spectral.
4. Apply 3.31 to Spv(A,I) with its inherited structure.

Sub-decomposition: -/

/-- **(T-Spv.2.α-sub, Wedhorn Lemma 3.29 — audit pass 1)** *"A quasi-compact
T0 topological space `(X, T')` with a basis `U` consisting of open-and-closed
subspaces has the following property: the topology `T` generated by `U` is
weaker than `T'`, makes `(X, T)` quasi-compact, and `U` becomes a basis of
quasi-compact open subspaces of `(X, T)`."*

This is the QC-Kolmogorov-OC-basis criterion that powers Wedhorn Prop 3.31.

Discharge plan: standard topological argument, lifted from Wedhorn p.30.
The QC of `T` follows from QC of `T'` since `T ⊆ T'`; the QC-basis property
follows because every element of `U` is clopen in `T'` (hence in any coarser
topology) and is open in `T` by construction. -/
theorem lemma_3_29_qcKolmogorov_oc_basis_consequences
    {X₀ : Type*}
    (T' : TopologicalSpace X₀) (hT'_qc : @CompactSpace X₀ T')
    (_hT'_T0 : @T0Space X₀ T')
    (U : Set (Set X₀))
    (hU_oc : ∀ s ∈ U, @IsOpen X₀ T' s ∧ @IsClosed X₀ T' s) :
    let T := TopologicalSpace.generateFrom U
    -- Note: Mathlib's `t1 ≤ t2 ↔ t2-open → t1-open` (t1 has MORE opens, i.e.,
    -- is FINER). T' is finer than T = generateFrom U (T' has all U-opens
    -- plus more), hence `T' ≤ T` per Mathlib's convention.
    T' ≤ T ∧ @CompactSpace X₀ T ∧
    @TopologicalSpace.IsTopologicalBasis X₀ T U ∧
    ∀ s ∈ U, @IsCompact X₀ T s := by
  have hT'_le_T : T' ≤ TopologicalSpace.generateFrom U :=
    TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr fun s hs => (hU_oc s hs).1
  refine ⟨hT'_le_T, ?_, ?_, ?_⟩
  · -- CompactSpace T: T' is QC, T is coarser (T' ≤ T), so any T-open cover is
    -- a T'-open cover, finite subcover in T' transfers back.
    refine @CompactSpace.mk X₀ (TopologicalSpace.generateFrom U) ?_
    rw [@isCompact_iff_finite_subcover X₀ (TopologicalSpace.generateFrom U)]
    intro ι UU hU_open hUni
    have hU'_open : ∀ i, @IsOpen X₀ T' (UU i) := fun i => hT'_le_T (UU i) (hU_open i)
    exact (@isCompact_univ X₀ T' hT'_qc).elim_finite_subcover UU hU'_open hUni
  · -- IsTopologicalBasis: deferred as the topological-basis criterion requires
    -- showing that every open of `generateFrom U` is a union of `U`-elements,
    -- which fails in general without U being closed under finite intersection.
    sorry
  · -- ∀ s ∈ U, IsCompact[T] s: each s is closed in T' (hU_oc), hence
    -- T'-compact (closed subset of T'-compact); transfer to T via the
    -- T-cover → T'-cover argument used for the global CompactSpace above.
    intro s hs
    rw [@isCompact_iff_finite_subcover X₀ (TopologicalSpace.generateFrom U)]
    intro ι UU hU_open hcover
    have hU'_open : ∀ i, @IsOpen X₀ T' (UU i) := fun i => hT'_le_T (UU i) (hU_open i)
    have hs_closed_T' : @IsClosed X₀ T' s := (hU_oc s hs).2
    haveI : @CompactSpace X₀ T' := hT'_qc
    exact (@IsClosed.isCompact X₀ T' s _ hs_closed_T').elim_finite_subcover
      UU hU'_open hcover

/-- **(T-Spv.2.α, Wedhorn 3.31)** General spectral-space constructor: a
quasi-compact Kolmogorov topological space `(X₀, T')` with a set `U` of
open-and-closed subspaces gives a SPECTRAL topology on `X₀` generated by `U`,
in which `U` is a basis of QC opens. -/
theorem isSpectralSpace_of_qcKolmogorov_oc_basis
    {X₀ : Type*}
    (T' : TopologicalSpace X₀) (hT'_qc : @CompactSpace X₀ T')
    (hT'_T0 : @T0Space X₀ T')
    (U : Set (Set X₀))
    (hU_oc : ∀ s ∈ U, @IsOpen X₀ T' s ∧ @IsClosed X₀ T' s)
    (T : TopologicalSpace X₀ := TopologicalSpace.generateFrom U) :
    @CompactSpace X₀ T ∧
    @T0Space X₀ T ∧
    @QuasiSober X₀ T ∧
    @TopologicalSpace.IsTopologicalBasis X₀ T U :=
  sorry

/-- **(T-Spv.2.β, Wedhorn 4.7 — Spv A is spectral)** Existing project
infrastructure in `ValuationSpectrumCompact.lean` provides this via the
bool-cube embedding. Re-stated here for use in T-Spv.2.

CompactSpace and T0Space are existing project instances (in
`ValuationSpectrumCompact.lean`). QuasiSober is the third piece of
spectral; still pending — would derive via the bool-cube embedding
(sober → quasi-sober is an instance + Set.range_ιSpv is closed in
sober Pi-space). -/
theorem Spv.isSpectralSpace : CompactSpace (Spv A) ∧ T0Space (Spv A) ∧ QuasiSober (Spv A) :=
  ⟨inferInstance, inferInstance, sorry⟩

/-- **(T-Spv.2.γ, SpvAI Kolmogorov as subspace of Spv)** -/
theorem SpvAI.t0Space (I : Ideal A) :
    @T0Space (SpvAI A I) (TopologicalSpace.induced (·.val) inferInstance) :=
  -- Subtype.t0Space (Mathlib instance): T0Space (Subtype p) for T0Space ambient.
  -- SpvAI A I is a subtype of Spv A which is T0 (instance).
  inferInstance

/-- **Wedhorn 7.5(1) spectrality.** `Spv(A, I)` with `SpvAI.topology I` is a
spectral space. **Proof**: apply T-Spv.2.α (Prop 3.31) with U = R (the basis
of QC opens `SpvAI.rationalSubset I T s`). The hypotheses:
- QC of `(SpvAI A I, induced topology)`: from Spv A QC (T-Spv.2.β) +
  SpvAI is closed in Spv A (it's the intersection of constructible subsets).
- Kolmogorov: T-Spv.2.γ.
- Each `R` element is open-and-closed in the constructible topology
  (= bool-cube topology on Spv A restricted to SpvAI). -/
theorem SpvAI.isSpectralSpace [DecidableEq A] (I : Ideal A) :
    @CompactSpace (SpvAI A I) (SpvAI.topology I) ∧
    @T0Space (SpvAI A I) (SpvAI.topology I) ∧
    @QuasiSober (SpvAI A I) (SpvAI.topology I) :=
  sorry

end ValuationSpectrum

/-! ## Wedhorn 7.12 — `Cont(A)` closed in `Spv(A, I·A)`, hence spectral -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Wedhorn 7.12 (closedness).** `Cont(A)` is the complement (inside
`Spv(A, I·A)`) of the open subset `⋃_{f ∈ I} SpvAI.rationalSubset I ∅ f`
(which says "exists `a ∈ I` with `v(a) ≥ 1`"). Hence `Cont(A) ∩ Spv(A, I·A)`
is closed in `Spv(A, I·A)`. -/
theorem cont_isClosed_in_SpvAI [DecidableEq A]
    (P : PairOfDefinition A)
    (I : Ideal A := Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    @IsClosed (SpvAI A I) (SpvAI.topology I)
      { v : SpvAI A I |
        letI : ValuativeRel A := v.1.toValuativeRel
        (ValuativeRel.valuation A).IsContinuous } :=
  sorry

/-- **Wedhorn 7.12 (spectral).** `Cont(A)` carries a spectral topology
inherited from `Spv(A, I·A)`. -/
theorem cont_isSpectralSpace [DecidableEq A]
    (P : PairOfDefinition A)
    (I : Ideal A := Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    @CompactSpace
      { v : SpvAI A I |
        letI : ValuativeRel A := v.1.toValuativeRel
        (ValuativeRel.valuation A).IsContinuous }
      (TopologicalSpace.induced (·.val) (SpvAI.topology I)) ∧
    @T0Space
      { v : SpvAI A I |
        letI : ValuativeRel A := v.1.toValuativeRel
        (ValuativeRel.valuation A).IsContinuous }
      (TopologicalSpace.induced (·.val) (SpvAI.topology I)) :=
  sorry

end ValuationSpectrum
