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

/-! ### Embeddings into the Laurent algebra -/

/-- The underlying function for the variable inclusion: sends a univariate power series to
a `k`-variate one by mapping the single variable to variable `j`. -/
noncomputable def varInclFun {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A) :
    MvPowerSeries (Fin k) A :=
  fun e => if e = Finsupp.single j (e j)
    then (MvPowerSeries.coeff (Finsupp.single 0 (e j))) f else 0

omit [TopologicalSpace A] [NonarchimedeanRing A] in
@[simp]
theorem varInclFun_apply {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A)
    (e : Fin k →₀ ℕ) : varInclFun j f e =
    if e = Finsupp.single j (e j)
    then (MvPowerSeries.coeff (Finsupp.single 0 (e j))) f else 0 := rfl

omit [TopologicalSpace A] [NonarchimedeanRing A] in
@[simp]
theorem varInclFun_coeff_single {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A) (n : ℕ) :
    varInclFun j f (Finsupp.single j n) =
    (MvPowerSeries.coeff (Finsupp.single 0 n)) f := by
  simp [varInclFun]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_zero {k : ℕ} (j : Fin k) :
    varInclFun j (0 : MvPowerSeries (Fin 1) A) = 0 := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j 0 e = (MvPowerSeries.coeff e) 0
  rw [varInclFun_apply, map_zero]; split_ifs <;> rfl

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_one {k : ℕ} (j : Fin k) :
    varInclFun j (1 : MvPowerSeries (Fin 1) A) = 1 := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j 1 e = (MvPowerSeries.coeff e) 1
  rw [varInclFun_apply, MvPowerSeries.coeff_one]
  split_ifs with h1 h2
  · rw [MvPowerSeries.coeff_one, if_pos]
    rw [h1]; simp [Finsupp.single_eq_zero.mp h2]
  · rw [MvPowerSeries.coeff_one, if_neg]
    intro h0; exact h2 (Finsupp.single_eq_zero.mpr (by rw [h1] at h0; simpa using h0))
  · rw [MvPowerSeries.coeff_one, if_neg]
    intro h0; exact h1 (by rw [h0]; simp)

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_add {k : ℕ} (j : Fin k) (f g : MvPowerSeries (Fin 1) A) :
    varInclFun j (f + g) = varInclFun j f + varInclFun j g := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j (f + g) e = varInclFun j f e + varInclFun j g e
  simp only [varInclFun_apply, map_add]; split_ifs <;> ring

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_mul {k : ℕ} (j : Fin k) (f g : MvPowerSeries (Fin 1) A) :
    varInclFun j (f * g) = varInclFun j f * varInclFun j g := by
  apply MvPowerSeries.ext; intro e
  by_cases h : e = Finsupp.single j (e j)
  · -- e supported on {j}: reduce to univariate multiplication via varInclFun_coeff_single
    change varInclFun j (f * g) e = (MvPowerSeries.coeff e) (varInclFun j f * varInclFun j g)
    rw [h]; simp only [varInclFun_coeff_single]
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    rw [Finsupp.antidiagonal_single, Finsupp.antidiagonal_single]
    simp only [Finset.sum_map]
    apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
    change _ = varInclFun j f (Finsupp.single j a) * varInclFun j g (Finsupp.single j b)
    simp
  · -- e not supported on {j}: both sides are 0
    change varInclFun j (f * g) e = (MvPowerSeries.coeff e) (varInclFun j f * varInclFun j g)
    rw [varInclFun_apply, if_neg h, MvPowerSeries.coeff_mul]
    symm; apply Finset.sum_eq_zero; intro p hp
    rw [Finset.mem_antidiagonal] at hp
    change varInclFun j f p.1 * varInclFun j g p.2 = 0
    rw [varInclFun_apply, varInclFun_apply]
    by_cases h1 : p.1 = Finsupp.single j (p.1 j)
    · have h2 : p.2 ≠ Finsupp.single j (p.2 j) := by
        intro h2; apply h; rw [← hp, h1, h2]
        ext i; simp [Finsupp.single_apply]
      rw [if_neg h2]; ring
    · rw [if_neg h1]; ring

/-- The variable inclusion as a ring homomorphism. -/
noncomputable def varInclHom {k : ℕ} (j : Fin k) :
    MvPowerSeries (Fin 1) A →+* MvPowerSeries (Fin k) A where
  toFun := varInclFun j
  map_zero' := varInclFun_zero j
  map_one' := varInclFun_one j
  map_add' := varInclFun_add j
  map_mul' := varInclFun_mul j

omit [NonarchimedeanRing A] in
/-- The variable inclusion preserves the restricted property. -/
theorem varInclHom_isRestricted {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A)
    (hf : MvPowerSeries.IsRestricted f) :
    MvPowerSeries.IsRestricted (varInclHom j f) := by
  change Tendsto _ cofinite (nhds 0)
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  have hfU : {s | (MvPowerSeries.coeff s) f ∉ U}.Finite := by
    have := tendsto_nhds.mp hf U hU h0U
    rwa [Filter.mem_cofinite] at this
  apply (hfU.image (fun d => Finsupp.mapDomain (fun _ => j) d)).subset
  intro e he
  simp only [Set.mem_compl_iff, Set.mem_preimage] at he
  show e ∈ _
  have he2 : varInclFun j f e ∉ U := by
    change (MvPowerSeries.coeff e) (varInclHom j f) ∉ U at he
    convert he using 1
  rw [varInclFun_apply] at he2
  split_ifs at he2 with h
  · refine ⟨Finsupp.single 0 (e j), he2, ?_⟩
    change Finsupp.mapDomain (fun _ => j) (Finsupp.single 0 (e j)) = e
    rw [Finsupp.mapDomain_single]; exact h.symm
  · exact absurd h0U he2

/-- The positive inclusion `A⟨X⟩ →+* A⟨X, Y⟩` sending `f(X) ↦ f(X)`, defined by mapping
the single variable to the first variable `X` of the bivariate ring. -/
noncomputable def posIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A) where
  toFun f := ⟨varInclHom 0 f.val, varInclHom_isRestricted 0 f.val f.prop⟩
  map_one' := by ext1; exact map_one (varInclHom (0 : Fin 2))
  map_mul' f g := by ext1; exact map_mul (varInclHom (0 : Fin 2)) f.val g.val
  map_zero' := by ext1; exact map_zero (varInclHom (0 : Fin 2))
  map_add' f g := by ext1; exact map_add (varInclHom (0 : Fin 2)) f.val g.val

/-- The negative inclusion `A⟨X⟩ →+* A⟨X, Y⟩` sending `f(X) ↦ f(Y)`, defined by mapping
the single variable to the second variable `Y` of the bivariate ring. -/
noncomputable def negIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A) where
  toFun f := ⟨varInclHom 1 f.val, varInclHom_isRestricted 1 f.val f.prop⟩
  map_one' := by ext1; exact map_one (varInclHom (1 : Fin 2))
  map_mul' f g := by ext1; exact map_mul (varInclHom (1 : Fin 2)) f.val g.val
  map_zero' := by ext1; exact map_zero (varInclHom (1 : Fin 2))
  map_add' f g := by ext1; exact map_add (varInclHom (1 : Fin 2)) f.val g.val

/-- The positive embedding `A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩` sending `X ↦ ζ`.
Embeds restricted power series in positive powers of `ζ`. -/
noncomputable def posEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A :=
  mkHom.comp posIncl

/-- The negative embedding `A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩` sending `X ↦ ζ⁻¹`.
Embeds restricted power series in negative powers of `ζ`. -/
noncomputable def negEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A :=
  mkHom.comp negIncl

end LaurentTateAlgebra
