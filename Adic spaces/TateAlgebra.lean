/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RestrictedPowerSeries
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# Tate and Laurent Algebras

This file defines the univariate Tate algebra `A⟨X⟩` and the Laurent Tate algebra
`A⟨ζ, ζ⁻¹⟩`, following Wedhorn's *Adic Spaces*, §6.9 and §8.29–8.33.

These are the central reusable objects for the Tate acyclicity proof (Theorem 8.28(b)).

## Main definitions

* `TateAlgebra A` : The univariate restricted power series ring `A⟨X⟩`.
* `TateAlgebra₂ A` : The bivariate restricted power series ring `A⟨X, Y⟩`.
* `LaurentTateAlgebra A` : The Laurent restricted power series ring `A⟨ζ, ζ⁻¹⟩`,
  defined as the quotient `A⟨X, Y⟩ / (XY - 1)`.

## Main results

* `TateAlgebra.evalZeroHom` : The evaluation-at-zero ring hom `A⟨X⟩ →+* A`.
* `TateAlgebra.evalZeroHom_surjective` : Surjectivity of evaluation at zero.
* `LaurentTateAlgebra.zeta_mul_zetaInv` : The defining relation `ζ · ζ⁻¹ = 1`.
* `LaurentTateAlgebra.zetaUnit` : `ζ` is a unit in `A⟨ζ, ζ⁻¹⟩`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6.9, §8.29–8.33
-/

open Filter MvPowerSeries

universe u

/-! ### Restricted power series: variables are restricted -/

/-- Any variable `MvPowerSeries.X i` is a restricted power series: it has exactly one
nonzero coefficient (at `Finsupp.single i 1`). -/
theorem MvPowerSeries.X_isRestricted {k : ℕ} {A : Type u} [CommRing A] [TopologicalSpace A]
    (i : Fin k) : MvPowerSeries.IsRestricted (MvPowerSeries.X i : MvPowerSeries (Fin k) A) := by
  change Tendsto _ cofinite (nhds 0)
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (Finsupp.single i 1)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by rw [MvPowerSeries.coeff_X, if_neg h]; exact h0U)

/-! ### Univariate Tate algebra -/

/-- The univariate Tate algebra `A⟨X⟩`, the ring of restricted power series in one variable.
This is `restrictedMvPowerSeriesSubring 1 A`, specialized to the univariate case.
See Wedhorn, Definition 6.9. -/
abbrev TateAlgebra (A : Type u) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Subring (MvPowerSeries (Fin 1) A) :=
  restrictedMvPowerSeriesSubring 1 A

namespace TateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Convert a natural number to the corresponding univariate multi-index `Fin 1 →₀ ℕ`. -/
noncomputable def toIndex (n : ℕ) : Fin 1 →₀ ℕ := Finsupp.single 0 n

@[simp]
theorem toIndex_zero : toIndex (0 : ℕ) = (0 : Fin 1 →₀ ℕ) :=
  Finsupp.single_zero (a := (0 : Fin 1))

/-- Every multi-index `s : Fin 1 →₀ ℕ` equals `toIndex (s 0)`. -/
theorem eq_toIndex (s : Fin 1 →₀ ℕ) : s = toIndex (s 0) := by
  apply Finsupp.ext; intro j
  rw [show j = 0 from Fin.eq_zero j]
  simp [toIndex]

/-- The n-th coefficient of a univariate restricted power series `f ∈ A⟨X⟩`. -/
noncomputable def coeff (n : ℕ) (f : ↥(TateAlgebra A)) : A :=
  (MvPowerSeries.coeff (R := A) (toIndex n)) f.val

/-- The variable `X` as an element of `A⟨X⟩`. -/
noncomputable def X : ↥(TateAlgebra A) :=
  ⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩

/-- Two elements of `A⟨X⟩` are equal iff they have the same coefficients. -/
@[ext]
theorem ext {f g : ↥(TateAlgebra A)} (h : ∀ n : ℕ, coeff n f = coeff n g) : f = g := by
  ext1
  exact MvPowerSeries.ext fun s => by rw [eq_toIndex s]; exact h (s 0)

/-- The constant term (evaluation at zero) is a ring homomorphism `A⟨X⟩ →+* A`. -/
noncomputable def evalZeroHom : ↥(TateAlgebra A) →+* A where
  toFun f := coeff 0 f
  map_one' := by simp [coeff, toIndex_zero, MvPowerSeries.coeff_one]
  map_mul' f g := by
    simp only [coeff, toIndex_zero, Subring.coe_mul]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_zero]
    simp
  map_zero' := by simp [coeff, map_zero]
  map_add' f g := by simp [coeff, map_add, Subring.coe_add]

/-- The evaluation-at-zero map is surjective: every `a : A` is the constant term of the
constant power series `algebraMap A _ a`. -/
theorem evalZeroHom_surjective : Function.Surjective (evalZeroHom (A := A)) := by
  intro a
  exact ⟨⟨algebraMap A _ a, MvPowerSeries.IsRestricted_algebraMap a⟩, by
    simp [evalZeroHom, coeff, toIndex_zero, MvPowerSeries.algebraMap_apply]⟩

end TateAlgebra

/-! ### Bivariate Tate algebra -/

/-- The bivariate Tate algebra `A⟨X, Y⟩`, the ring of restricted power series in two variables.
See Wedhorn, Definition 6.9. -/
abbrev TateAlgebra₂ (A : Type u) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Subring (MvPowerSeries (Fin 2) A) :=
  restrictedMvPowerSeriesSubring 2 A

namespace TateAlgebra₂

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The variable `X` as an element of `A⟨X, Y⟩`. -/
noncomputable def X : ↥(TateAlgebra₂ A) :=
  ⟨MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X_isRestricted 0⟩

/-- The variable `Y` as an element of `A⟨X, Y⟩`. -/
noncomputable def Y : ↥(TateAlgebra₂ A) :=
  ⟨MvPowerSeries.X (1 : Fin 2), MvPowerSeries.X_isRestricted 1⟩

/-- The element `XY - 1` in `A⟨X, Y⟩`. -/
noncomputable def XY_sub_one : ↥(TateAlgebra₂ A) := X * Y - 1

end TateAlgebra₂

/-! ### Laurent Tate algebra (quotient model) -/

/-- The ideal generated by `XY - 1` in `A⟨X, Y⟩`. -/
noncomputable def laurentIdeal (A : Type u) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Ideal ↥(TateAlgebra₂ A) :=
  Ideal.span {TateAlgebra₂.XY_sub_one}

/-- The Laurent Tate algebra `A⟨ζ, ζ⁻¹⟩`, defined as the quotient of the bivariate
restricted power series ring `A⟨X, Y⟩` by the ideal `(XY - 1)`.

This models the ring of bilateral restricted power series
`∑_{n ∈ ℤ} aₙ ζⁿ` with `aₙ → 0` as `|n| → ∞`.

See Wedhorn, §8.29–8.33 (Definition 8.27). -/
noncomputable def LaurentTateAlgebra (A : Type u) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] :=
  ↥(TateAlgebra₂ A) ⧸ laurentIdeal A

namespace LaurentTateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

noncomputable instance : CommRing (LaurentTateAlgebra A) :=
  Ideal.Quotient.commRing (laurentIdeal A)

/-- The quotient map `A⟨X, Y⟩ →+* A⟨ζ, ζ⁻¹⟩`. -/
noncomputable def mkHom : ↥(TateAlgebra₂ A) →+* LaurentTateAlgebra A :=
  Ideal.Quotient.mk (laurentIdeal A)

/-- The image of `X` in the Laurent algebra, representing `ζ`. -/
noncomputable def zeta : LaurentTateAlgebra A := mkHom TateAlgebra₂.X

/-- The image of `Y` in the Laurent algebra, representing `ζ⁻¹`. -/
noncomputable def zetaInv : LaurentTateAlgebra A := mkHom TateAlgebra₂.Y

/-- The defining relation: `ζ · ζ⁻¹ = 1` in `A⟨ζ, ζ⁻¹⟩`. -/
theorem zeta_mul_zetaInv : zeta * zetaInv = (1 : LaurentTateAlgebra A) := by
  change mkHom TateAlgebra₂.X * mkHom TateAlgebra₂.Y = 1
  rw [← map_mul, ← map_one mkHom]
  apply Ideal.Quotient.eq.mpr
  change TateAlgebra₂.X * TateAlgebra₂.Y - 1 ∈ laurentIdeal A
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The defining relation: `ζ⁻¹ · ζ = 1` in `A⟨ζ, ζ⁻¹⟩`. -/
theorem zetaInv_mul_zeta : zetaInv * zeta = (1 : LaurentTateAlgebra A) := by
  rw [mul_comm, zeta_mul_zetaInv]

/-- `ζ` is a unit in `A⟨ζ, ζ⁻¹⟩`. -/
noncomputable def zetaUnit : (LaurentTateAlgebra A)ˣ where
  val := zeta
  inv := zetaInv
  val_inv := zeta_mul_zetaInv
  inv_val := zetaInv_mul_zeta

/-- The `A`-algebra structure on `A⟨ζ, ζ⁻¹⟩`, via the composition
`A → A⟨X, Y⟩ → A⟨ζ, ζ⁻¹⟩`. -/
noncomputable instance : Algebra A (LaurentTateAlgebra A) :=
  (mkHom.comp (algebraMap A ↥(TateAlgebra₂ A))).toAlgebra

end LaurentTateAlgebra
