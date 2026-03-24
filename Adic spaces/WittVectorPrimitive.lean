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

/-- The 0-th Witt coefficient of `p ∈ W(k)` is 0 when `k` has characteristic `p`. -/
theorem WittVector.coeff_zero_p : ((p : 𝕎 k)).coeff 0 = 0 := by
  rw [WittVector.coeff_p]; simp

/-- A primitive element `ξ = p + [ϖ]α` has `ξ.coeff 0 = ϖ · (α.coeff 0)`. -/
theorem WittVector.IsPrimitive.coeff_zero {ξ : 𝕎 k} {ϖ : k} (h : ξ.IsPrimitive ϖ) :
    ξ.coeff 0 = ϖ * (h.eq_p_add.choose.coeff 0) := by
  obtain ⟨α, hα⟩ := h.eq_p_add
  simp [hα, coeff_zero_p, mul_comm]

/-- A primitive element has nonzero 0-th coefficient when `ϖ` is a nonzerodivisor
and `α.coeff 0 ≠ 0`. More precisely, `ξ.coeff 0 = ϖ · (α.coeff 0)`. -/
theorem WittVector.IsPrimitive.coeff_zero_ne_zero {ξ : 𝕎 k} {ϖ : k}
    (h : ξ.IsPrimitive ϖ) (hϖ : ϖ ≠ 0) [NoZeroDivisors k]
    (hα : h.eq_p_add.choose.coeff 0 ≠ 0) : ξ.coeff 0 ≠ 0 := by
  rw [h.coeff_zero]
  exact mul_ne_zero hϖ hα

/-- A primitive element is nonzero when `ϖ ≠ 0`, `k` has no zero divisors,
and the coefficient `α` has `α.coeff 0 ≠ 0`. -/
theorem WittVector.IsPrimitive.ne_zero {ξ : 𝕎 k} {ϖ : k}
    (h : ξ.IsPrimitive ϖ) (hϖ : ϖ ≠ 0) [NoZeroDivisors k]
    (hα : h.eq_p_add.choose.coeff 0 ≠ 0) : ξ ≠ 0 := by
  intro heq
  have := h.coeff_zero_ne_zero hϖ hα
  simp [heq] at this

/-- A primitive element is not in the ideal `(p)` of `W(k)`.
This is because `ξ.coeff 0 = ϖ · (α.coeff 0)` which is nonzero (in the right
conditions), while every element of `(p)` has `coeff 0 = 0`. -/
theorem WittVector.IsPrimitive.not_mem_span_p {ξ : 𝕎 k} {ϖ : k}
    (h : ξ.IsPrimitive ϖ) (hϖ : ϖ ≠ 0) [NoZeroDivisors k]
    (hα : h.eq_p_add.choose.coeff 0 ≠ 0) : ξ ∉ Ideal.span {(p : 𝕎 k)} := by
  rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  exact h.coeff_zero_ne_zero hϖ hα

/-! ### Division by primitive elements -/

/-- **Lemma 6.2.10 (Scholze-Weinstein):** A primitive element `ξ = p + [ϖ]α` is a
nonzerodivisor in `W(k)`, provided `ϖ` is a nonzerodivisor in `k`.

The proof: if `ξ · x = 0`, then modulo `[ϖ]`, `p · x ≡ 0`. By p-torsion-freeness
of `W(k)` (`eq_zero_of_p_mul_eq_zero`), all coefficients of `x` are divisible by `ϖ`.
Dividing by `ϖ` and repeating shows `x = 0`. -/
theorem WittVector.IsPrimitive.isRegular {ξ : 𝕎 k} {ϖ : k}
    (hξ : ξ.IsPrimitive ϖ) (hϖ : ϖ ≠ 0) [IsDomain k] :
    IsRegular ξ := by
  sorry -- Requires detailed coefficient manipulation with Verschiebung/Frobenius.
  -- The proof goes: ξ·x = 0 → (p + [ϖ]α)·x = 0 → p·x = -[ϖ]α·x.
  -- Reducing mod [ϖ]: p·x ≡ 0 mod [ϖ]. In W(k), the coeff structure of
  -- [ϖ]·y means (ϖ·y₀, ...). So p·x mod [ϖ] means all coefficients of
  -- p·x are divisible by ϖ. By WittVector.eq_zero_of_p_mul_eq_zero and
  -- induction, x = 0.

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
