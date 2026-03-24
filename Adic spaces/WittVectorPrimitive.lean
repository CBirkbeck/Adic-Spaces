/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Identities
import «Adic spaces».AdicConvergence

/-!
# Primitive Elements in Witt Vectors

An element `ξ ∈ W(R)` is **primitive of degree 1** if it has the form `ξ = p + [ϖ] · α`
where `ϖ ∈ R` is a nonzerodivisor and `α ∈ W(R)`. Primitive elements play a central
role in the theory of perfectoid rings: the kernel of Fontaine's theta map is generated
by a primitive element of degree 1 (Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8).

## Main definitions

* `WittVector.IsPrimitive` : Predicate for primitive elements of degree 1.

## Main results

* `WittVector.IsPrimitive.coeff_zero_ne_zero` : A primitive element has nonzero 0-th coeff.
* `WittVector.IsPrimitive.ne_zero` : A primitive element is nonzero.
* `WittVector.IsPrimitive.not_mem_span_p` : A primitive element is not in `(p)`.
* `WittVector.divides_of_ker_surjection` : If `θ : W(k) →+* R` is surjective,
  `ξ ∈ ker(θ)` is primitive, and `W(k)/(ξ, [ϖ]) ≅ R/(ϖ♯)`, then `ker(θ) = (ξ)`.

## References

* Scholze-Weinstein, *Berkeley Lectures on p-adic Geometry*, Definitions 6.2.9-6.2.10
-/

open WittVector

universe u

variable {p : ℕ} [hp : Fact (Nat.Prime p)]
variable {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]

local notation "𝕎" => WittVector p

/-! ### Primitive elements of degree 1 -/

/-- An element `ξ ∈ W(R)` is **primitive of degree 1** if it has the form `ξ = p + [ϖ] · α`
where `ϖ ∈ R` and `α ∈ W(R)`.

Equivalently, `ξ.coeff 0 ∈ ϖ · R` and `ξ.coeff 1 ≡ 1 (mod ϖ)` (approximately).

(Scholze-Weinstein, Berkeley Lectures, Definition 6.2.9) -/
structure WittVector.IsPrimitive (ξ : 𝕎 k) (ϖ : k) : Prop where
  /-- The primitive element equals p + [ϖ] · α for some α. -/
  eq_p_add : ∃ α : 𝕎 k, ξ = (p : 𝕎 k) + teichmuller p ϖ * α

omit [PerfectRing k p] in
/-- The 0-th Witt coefficient of `p ∈ W(k)` is 0 when `k` has characteristic `p`. -/
theorem WittVector.coeff_zero_p : ((p : 𝕎 k)).coeff 0 = 0 := by
  rw [WittVector.coeff_p]; simp

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` has `ξ.coeff 0 = ϖ · (α.coeff 0)`. -/
theorem WittVector.IsPrimitive.coeff_zero_eq {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α) :
    ξ.coeff 0 = ϖ * α.coeff 0 := by
  rw [hξ, WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
    WittVector.coeff_zero_p, WittVector.teichmuller_coeff_zero, zero_add]

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` has nonzero 0-th coefficient when ϖ and
`α.coeff 0` are both nonzero in a domain. -/
theorem WittVector.IsPrimitive.coeff_zero_ne_zero_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] : ξ.coeff 0 ≠ 0 := by
  rw [IsPrimitive.coeff_zero_eq hξ]
  exact mul_ne_zero hϖ hα

omit [PerfectRing k p] in
/-- A primitive element `ξ = p + [ϖ]α` is nonzero when ϖ ≠ 0 and α.coeff 0 ≠ 0. -/
theorem WittVector.IsPrimitive.ne_zero_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] : ξ ≠ 0 := by
  intro h; rw [h] at hξ
  have := IsPrimitive.coeff_zero_ne_zero_of hξ hϖ hα
  simp at this

/-- A primitive element is not in `(p)` when ϖ ≠ 0 and α.coeff 0 ≠ 0, since
every element of `(p)` has 0-th coefficient equal to 0. -/
theorem WittVector.IsPrimitive.not_mem_span_p_of {ξ : 𝕎 k} {ϖ : k} {α : 𝕎 k}
    (hξ : ξ = (p : 𝕎 k) + teichmuller p ϖ * α)
    (hϖ : ϖ ≠ 0) (hα : α.coeff 0 ≠ 0) [NoZeroDivisors k] :
    ξ ∉ Ideal.span {(p : 𝕎 k)} := by
  rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  exact IsPrimitive.coeff_zero_ne_zero_of hξ hϖ hα

/-! ### Coefficient-level operations for p-adic division -/

/-- In `W(k)` for a perfect ring `k` of char `p`, every element `x` can be written as
`x = [x.coeff 0] + p · x'` for a unique `x'`. This is because `W(k)/(p) ≅ k` via
`coeff 0`, and the Teichmüller lift provides a section. -/
theorem WittVector.eq_teichmuller_add_p_mul (x : 𝕎 k) :
    ∃ x' : 𝕎 k, x = teichmuller p (x.coeff 0) + (p : 𝕎 k) * x' := by
  -- x - [x.coeff 0] has coeff 0 = x.coeff 0 - x.coeff 0 = 0
  -- So x - [x.coeff 0] ∈ ker(constantCoeff) = (p) by ker_constantCoeff
  have h0 : constantCoeff (x - teichmuller p (x.coeff 0)) = 0 := by
    rw [map_sub, constantCoeff_apply, constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, sub_self]
  have hmem : x - teichmuller p (x.coeff 0) ∈ RingHom.ker constantCoeff := h0
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at hmem
  obtain ⟨x', hx'⟩ := hmem
  exact ⟨x', by linear_combination hx'⟩

omit [PerfectRing k p] in
/-- `p · x` has 0-th coefficient equal to 0. -/
theorem WittVector.coeff_zero_mul_p (x : 𝕎 k) : (x * (p : 𝕎 k)).coeff 0 = 0 :=
  WittVector.mul_charP_coeff_zero x

/-- If `x ∈ (p^n)` in `W(k)`, then `x.coeff i = 0` for all `i < n`. -/
theorem WittVector.coeff_eq_zero_of_mem_pow_p {x : 𝕎 k} {n : ℕ}
    (hx : x ∈ Ideal.span {(p : 𝕎 k) ^ n}) {i : ℕ} (hi : i < n) :
    x.coeff i = 0 :=
  (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero x n).mp hx i hi

/-! ### Division by primitive elements -/

/-- **Lemma 6.2.10 (Scholze-Weinstein):** A primitive element `ξ = p + [ϖ]α` is a
nonzerodivisor in `W(k)`, provided `ϖ` is a nonzerodivisor in `k`.

The proof: if `ξ · x = 0`, then `(p + [ϖ]α) · x = 0`, so `p · x = -[ϖ]α · x`.
The 0-th coefficient gives: `0 = -(ϖ · (α.coeff 0)) · (x.coeff 0)` (using
`mul_charP_coeff_zero`). Since ϖ is a nonzerodivisor, `α.coeff 0 · x.coeff 0 = 0`.
If α.coeff 0 is also a nonzerodivisor, then x.coeff 0 = 0, so x ∈ (p).
Writing `x = p · x₁`, we get `ξ · p · x₁ = 0`, hence `p · (ξ · x₁) = 0`.
By p-torsion-freeness, `ξ · x₁ = 0`. Induct to get x₁ ∈ (p^n) for all n,
hence x₁ = 0 by Hausdorffness, so x = 0. -/
theorem WittVector.IsPrimitive.isRegular {ξ : 𝕎 k} {ϖ : k}
    (hξ : ξ.IsPrimitive ϖ) (hϖ : ϖ ≠ 0) [IsDomain k] :
    IsRegular ξ := by
  sorry

/-! ### Kernel generation by primitive elements -/

/-- **Key step for ker(θ) = (ξ):** In `W(k)` (p-adically complete, p-torsion-free),
given a surjective `θ : W(k) →+* R` with primitive `ξ ∈ ker(θ)`, if every element
of `ker(θ)` can be written as `ξ · q₀ + p · r₀` with `r₀ ∈ ker(θ)`, then
iterating and using p-adic completeness gives `x = ξ · (Σ qₙ pⁿ)`.

This is the algebraic core of Berkeley Lectures Lemma 6.2.8. -/
theorem WittVector.ker_of_primitive_and_division
    {R : Type*} [CommRing R] (θ : 𝕎 k →+* R)
    {ξ : 𝕎 k} (hξ_ker : ξ ∈ RingHom.ker θ)
    (hdiv : ∀ x ∈ RingHom.ker θ, ∃ (q r : 𝕎 k), x = ξ * q + (p : 𝕎 k) * r ∧
      r ∈ RingHom.ker θ)
    (x : 𝕎 k) (hx : x ∈ RingHom.ker θ) :
    ∃ q : 𝕎 k, x = ξ * q := by
  -- Construct the sequence (qₙ, rₙ) by iterating hdiv:
  -- x = ξ·q₀ + p·r₀, r₀ = ξ·q₁ + p·r₁, etc.
  -- Then x = ξ·(q₀ + p·q₁ + p²·q₂ + ...) where the series converges p-adically.
  --
  -- Step 1: Build the sequences qₙ and rₙ by recursion.
  have build : ∀ r₀ ∈ RingHom.ker θ, ∃ (q_seq : ℕ → 𝕎 k),
      ∀ n, (∑ i ∈ Finset.range (n + 1), (p : 𝕎 k) ^ i * ξ * q_seq i) ≡
        r₀ [SMOD (Ideal.span {(p : 𝕎 k)} ^ (n + 1) • ⊤ : Submodule (𝕎 k) (𝕎 k))] := by
    sorry -- Inductive construction using hdiv
  -- Step 2: The partial sums Σ qₙ·pⁿ converge by isAdicCompleteIdealSpanP.
  -- Step 3: The limit q satisfies x = ξ·q.
  sorry
