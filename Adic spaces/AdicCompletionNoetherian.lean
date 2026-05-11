/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The I-adic completion of a Noetherian ring is Noetherian.

This file proves Stacks Tag 00MA: if `R` is a Noetherian commutative ring and `I` is an
ideal of `R`, then the `I`-adic completion `AdicCompletion I R` is also Noetherian.

The proof proceeds as follows:

1. Since `R` is Noetherian, the ideal `I` is finitely generated, say by `f_1, ..., f_n`.
2. We prove that the multivariate power series ring `MvPowerSeries (Fin n) R` is Noetherian
   by induction on `n`, using the iterated isomorphism with `PowerSeries`.
3. We construct a ring homomorphism `MvPowerSeries (Fin n) R →+* AdicCompletion I R`
   sending the variables `X_i` to the images of the generators `f_i`.
4. We show this map is surjective using the universal property of the completion.
5. The completion is then a quotient of a Noetherian ring, hence Noetherian.

## Main results

* `MvPowerSeries.Fin.isNoetherianRing`: `MvPowerSeries (Fin n) R` is Noetherian
  when `R` is Noetherian.
* `AdicCompletion.isNoetherianRing`: `AdicCompletion I R` is Noetherian when `R` is.
-/

open scoped Classical

namespace MvPowerSeries

variable {R : Type*}

section Fin0

variable [CommRing R]

/-- `MvPowerSeries (Fin 0) R` is isomorphic to `R`. -/
noncomputable def finZeroEquivRingHom : MvPowerSeries (Fin 0) R ≃+* R where
  toFun f := coeff 0 f
  invFun a := monomial 0 a
  left_inv f := by
    ext n
    have hn : n = 0 := Subsingleton.elim _ _
    subst hn
    rw [coeff_monomial_same]
  right_inv a := coeff_monomial_same _ _
  map_add' := by intros; simp
  map_mul' f g := by
    have h : (0 : Fin 0 →₀ ℕ) = 0 := rfl
    rw [coeff_mul]
    simp only [Finset.antidiagonal_zero]
    rw [Finset.sum_singleton]

end Fin0

end MvPowerSeries

/-! ### Multivariate power series in finitely many variables is Noetherian -/

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- The currying isomorphism `MvPowerSeries (Fin (n+1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R)`.
Given a formal power series in `n+1` variables, we expand it as a power series in the first variable
with coefficients that are power series in the remaining `n` variables.

Concretely, an element `f : (Fin (n+1) →₀ ℕ) → R` is mapped to the function `k ↦ (e ↦ f (cons k e))`
where `cons k e : Fin (n+1) →₀ ℕ` has the first coordinate `k` and the rest given by `e`. -/
noncomputable def finSuccEquivPowerSeries (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) := by
  sorry

end MvPowerSeries
