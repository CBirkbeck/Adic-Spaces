/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpvAI
import «Adic spaces».RationalSubsets

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

end ValuationSpectrum
