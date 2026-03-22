/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RestrictedPowerSeries
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Localization

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

/-! ### TICKET-2B: Remark 8.29 + Lemma 8.31

The algebraic engine for Tate acyclicity: the quotient `A⟨X⟩/(X) ≅ A`,
faithful flatness of `A⟨X⟩` over `A`, and quotient flatness results.

References: Wedhorn, Remark 8.29, Lemma 8.31.
-/

namespace TateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! #### The splitting: evalZeroHom ∘ algebraMap = id -/

/-- Evaluating the constant coefficient of `algebraMap a` gives back `a`. -/
theorem evalZeroHom_algebraMap (a : A) :
    evalZeroHom (algebraMap A ↥(TateAlgebra A) a) = a := by
  simp only [evalZeroHom, coeff, toIndex_zero]
  norm_cast

/-- The composition `evalZeroHom ∘ algebraMap` is the identity on `A`.
This means `algebraMap` is a section of `evalZeroHom`. -/
theorem evalZeroHom_comp_algebraMap :
    evalZeroHom.comp (algebraMap A ↥(TateAlgebra A)) = RingHom.id A := by
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  exact evalZeroHom_algebraMap a

/-! #### The shift operation and kernel of evalZeroHom -/

/-- The "shift" of a univariate power series: `(shiftFun f)(s) = f(s + single 0 1)`.
This extracts the quotient `f / X` when `f(0) = 0`. -/
noncomputable def shiftFun (f : MvPowerSeries (Fin 1) A) : MvPowerSeries (Fin 1) A :=
  fun s => f (s + Finsupp.single 0 1)

omit [NonarchimedeanRing A] in
/-- The shift of a restricted power series is restricted. The map `s ↦ s + single 0 1`
is injective, so composing with it preserves the cofinite-filter condition. -/
theorem shiftFun_isRestricted {f : MvPowerSeries (Fin 1) A}
    (hf : MvPowerSeries.IsRestricted f) : MvPowerSeries.IsRestricted (shiftFun f) := by
  change Tendsto _ cofinite (nhds 0)
  change Tendsto _ cofinite (nhds 0) at hf
  -- The shift map is s ↦ s + single 0 1, which is injective
  have inj : Function.Injective fun s : Fin 1 →₀ ℕ => s + Finsupp.single 0 1 :=
    fun s t => by simp [Finsupp.ext_iff]
  -- Composing with an injective function preserves the cofinite filter property
  exact hf.comp inj.tendsto_cofinite

/-- The shift as an element of `A⟨X⟩`: given `f ∈ A⟨X⟩`, `shift f` is the shifted
element, also in `A⟨X⟩`. -/
noncomputable def shift (f : ↥(TateAlgebra A)) : ↥(TateAlgebra A) :=
  ⟨shiftFun f.val, shiftFun_isRestricted f.prop⟩

-- Helper: coefficient identity for the splitting f = C(f(0)) + X * shift(f)
omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem mvps_coeff_eq (g : MvPowerSeries (Fin 1) A) (n : ℕ) :
    MvPowerSeries.coeff (toIndex n) g =
    MvPowerSeries.coeff (toIndex n) (MvPowerSeries.C (g 0)) +
    MvPowerSeries.coeff (toIndex n) (MvPowerSeries.X 0 * shiftFun g) := by
  induction n with
  | zero =>
    simp only [toIndex_zero]
    rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_X_mul, add_zero,
        MvPowerSeries.coeff_apply]
  | succ n =>
    rw [MvPowerSeries.coeff_C]
    rw [if_neg (by simp [toIndex, Finsupp.single_eq_zero] : toIndex (n + 1) ≠ 0)]
    rw [zero_add]
    -- Goal: coeff (toIndex (n+1)) g = coeff (toIndex (n+1)) (X 0 * shiftFun g)
    -- X 0 = monomial (single 0 1) 1
    rw [show (MvPowerSeries.X (R := A) (0 : Fin 1)) =
        MvPowerSeries.monomial (Finsupp.single 0 1) (1 : A) from rfl]
    rw [MvPowerSeries.coeff_monomial_mul]
    have hle : Finsupp.single (0 : Fin 1) 1 ≤ toIndex (n + 1) := by
      simp [toIndex]
    rw [if_pos hle, one_mul]
    -- Goal: coeff (toIndex (n+1)) g = shiftFun g (toIndex (n+1) - single 0 1)
    -- shiftFun g s = g (s + single 0 1)
    -- toIndex (n+1) - single 0 1 = single 0 (n+1) - single 0 1 = single 0 n
    -- So RHS = g (single 0 n + single 0 1) = g (single 0 (n+1)) = g (toIndex (n+1))
    simp [shiftFun, toIndex, Finsupp.single_add, MvPowerSeries.coeff_apply]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem mvps_eq_const_add_X_mul_shift (g : MvPowerSeries (Fin 1) A) :
    g = MvPowerSeries.C (g 0) + MvPowerSeries.X 0 * shiftFun g := by
  ext s
  rw [map_add, eq_toIndex s]
  exact mvps_coeff_eq g (s 0)

/-- Key identity: `f = const(f(0)) + X * shift(f)` as power series. -/
theorem eq_const_add_X_mul_shift (f : ↥(TateAlgebra A)) :
    f = algebraMap A _ (evalZeroHom f) + X * shift f := by
  -- Use the ext lemma to reduce to coefficient comparison
  ext n
  -- coeff n f = coeff n (algebraMap ... + X * shift f)
  -- Use mvps_coeff_eq to handle the underlying MvPowerSeries
  unfold coeff
  have hval : (algebraMap A ↥(TateAlgebra A) (evalZeroHom f) +
      X * shift f).val = (algebraMap A ↥(TateAlgebra A) (evalZeroHom f)).val +
      ((X : ↥(TateAlgebra A)).val * (shift f).val) := by
    rfl
  rw [hval]
  -- Now goal: MvPowerSeries.coeff (toIndex n) f.val =
  --   MvPowerSeries.coeff (toIndex n) (algebraMap(..).val + X.val * (shift f).val)
  rw [map_add]
  -- Rewrite the algebraMap val to C (f.val 0)
  have halg : (algebraMap A ↥(TateAlgebra A) (evalZeroHom f)).val =
      MvPowerSeries.C (σ := Fin 1) (f.val 0) := by
    change algebraMap A (MvPowerSeries (Fin 1) A) (evalZeroHom f) = _
    rw [MvPowerSeries.algebraMap_apply]
    simp [evalZeroHom, coeff, toIndex_zero, MvPowerSeries.coeff_apply]
  rw [halg]
  exact mvps_coeff_eq f.val n

/-- An element of `A⟨X⟩` with zero constant term is divisible by `X`. -/
theorem mem_ideal_X_of_evalZeroHom_eq_zero {f : ↥(TateAlgebra A)}
    (hf : evalZeroHom f = 0) : f ∈ Ideal.span ({X} : Set ↥(TateAlgebra A)) := by
  have key : f = X * shift f := by
    have h := eq_const_add_X_mul_shift f
    rw [hf, map_zero, zero_add] at h
    exact h
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- The constant term of `X * g` is zero. -/
theorem evalZeroHom_X_mul (g : ↥(TateAlgebra A)) : evalZeroHom (X * g) = 0 := by
  simp only [evalZeroHom, coeff, toIndex_zero, map_mul, TateAlgebra.X]
  norm_cast
  simp

/-- Every element of `Ideal.span {X}` has zero constant term. -/
theorem evalZeroHom_eq_zero_of_mem_ideal_X {f : ↥(TateAlgebra A)}
    (hf : f ∈ Ideal.span ({X} : Set ↥(TateAlgebra A))) : evalZeroHom f = 0 := by
  -- X ∈ ker evalZeroHom, so Ideal.span {X} ≤ ker evalZeroHom
  have hX : (X : ↥(TateAlgebra A)) ∈ RingHom.ker evalZeroHom := by
    rw [RingHom.mem_ker]
    simp [evalZeroHom, coeff, toIndex_zero, TateAlgebra.X]
  exact RingHom.mem_ker.mp (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX) hf)

/-- The kernel of `evalZeroHom` equals the ideal generated by `X`. -/
theorem ker_evalZeroHom :
    RingHom.ker evalZeroHom = Ideal.span ({X} : Set ↥(TateAlgebra A)) := by
  ext f
  constructor
  · intro hf
    exact mem_ideal_X_of_evalZeroHom_eq_zero (RingHom.mem_ker.mp hf)
  · intro hf
    exact RingHom.mem_ker.mpr (evalZeroHom_eq_zero_of_mem_ideal_X hf)

/-- The ideal generated by `X` in `A⟨X⟩`. -/
noncomputable def idealX : Ideal ↥(TateAlgebra A) :=
  Ideal.span {X}

/-! #### Coefficient arithmetic helpers -/

/-- Coefficient of a difference of power series. -/
theorem coeff_sub (f g : ↥(TateAlgebra A)) (n : ℕ) :
    coeff n (f - g) = coeff n f - coeff n g := by
  simp [coeff, map_sub]

/-- Coefficient of `algebraMap a * u`: the `algebraMap` acts as scalar multiplication. -/
theorem coeff_algebraMap_mul (a : A) (u : ↥(TateAlgebra A)) (n : ℕ) :
    coeff n (algebraMap A _ a * u) = a * coeff n u := by
  simp only [coeff, toIndex]
  change (MvPowerSeries.coeff (Finsupp.single 0 n))
    ((algebraMap A (MvPowerSeries (Fin 1) A) a) * u.val) = _
  rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]; simp

/-- The `(n+1)`-th coefficient of `X * u` equals the `n`-th coefficient of `u`. -/
theorem coeff_succ_X_mul (u : ↥(TateAlgebra A)) (n : ℕ) :
    coeff (n + 1) (X * u) = coeff n u := by
  simp only [coeff, X, toIndex]
  change (MvPowerSeries.coeff (Finsupp.single 0 (n + 1)))
    (MvPowerSeries.X (0 : Fin 1) * u.val) = _
  rw [show (MvPowerSeries.X (R := A) (0 : Fin 1)) =
      MvPowerSeries.monomial (Finsupp.single 0 1) (1 : A) from rfl]
  rw [MvPowerSeries.coeff_monomial_mul,
    if_pos (show Finsupp.single (0 : Fin 1) 1 ≤ Finsupp.single 0 (n + 1) by simp), one_mul]
  simp [Finsupp.single_add, MvPowerSeries.coeff_apply]

/-- The constant coefficient of `X * u` is zero. -/
theorem coeff_zero_X_mul (u : ↥(TateAlgebra A)) :
    coeff 0 (X * u) = 0 := by
  have := evalZeroHom_X_mul u; simp only [evalZeroHom] at this; exact this

/-! #### Noetherian ascending chain lemma -/

omit [TopologicalSpace A] [NonarchimedeanRing A] in
/-- In a noetherian ring, if `a * x 0 = 0` and `x k = a * x (k + 1)` for all `k`,
then `x 0 = 0`. The proof uses the ascending chain of annihilator ideals
`{b | a^n * b = 0}` and its stabilization. -/
private theorem noeth_zero_of_mul_shift [IsNoetherianRing A] (a : A) (x : ℕ → A)
    (h0 : a * x 0 = 0) (hstep : ∀ k, x k = a * x (k + 1)) : x 0 = 0 := by
  have hpow : ∀ k, x 0 = a ^ k * x k := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [ih, hstep k, pow_succ, mul_assoc]
  have hann : ∀ k, a ^ (k + 1) * x k = 0 := by
    intro k
    have : a ^ (k + 1) * x k = a * (a ^ k * x k) := by ring
    rw [this, ← hpow k, h0]
  have chain_monotone : Monotone (fun n => (⟨⟨⟨{b | a ^ n * b = 0},
    fun {x y} (hx : a ^ n * x = 0) (hy : a ^ n * y = 0) => by
      change a ^ n * (x + y) = 0; rw [mul_add, hx, hy, add_zero]⟩,
    by change a ^ n * 0 = 0; simp⟩,
    fun c {x} (hx : a ^ n * x = 0) => by
      change a ^ n * (c • x) = 0; rw [smul_eq_mul, mul_left_comm, hx, mul_zero]⟩
    : Submodule A A)) := by
    intro m n hmn b (hb : a ^ m * b = 0)
    change a ^ n * b = 0
    calc a ^ n * b = a ^ (n - m) * (a ^ m * b) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
      _ = 0 := by rw [hb, mul_zero]
  let chain : ℕ →o Submodule A A := ⟨_, chain_monotone⟩
  obtain ⟨K, hK⟩ :=
    (monotone_stabilizes_iff_noetherian (R := A) (M := A)).mpr inferInstance chain
  have hxK_mem : x K ∈ chain (K + 1) := by
    change a ^ (K + 1) * x K = 0; exact hann K
  have hxK : a ^ K * x K = 0 :=
    (hK (K + 1) (by omega) ▸ hxK_mem : x K ∈ chain K)
  rw [hpow K, hxK]

/-! #### Faithful flatness of A⟨X⟩ over A (Lemma 8.31(1)) -/

/-- `PrimeSpectrum.comap (algebraMap A A⟨X⟩)` is surjective.
This follows because `evalZeroHom` provides a section: the composition
`algebraMap` then `evalZeroHom` is the identity, so `comap evalZeroHom`
is a right inverse of `comap algebraMap`. -/
theorem PrimeSpectrum_comap_algebraMap_surjective :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A ↥(TateAlgebra A))) := by
  intro p
  refine ⟨PrimeSpectrum.comap evalZeroHom p, ?_⟩
  ext x; simp [PrimeSpectrum.comap, evalZeroHom_algebraMap]

/-! #### Discrete-case equivalence: TateAlgebra A ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A

Under `[DiscreteTopology A]`, a power series is restricted iff it has finite support
(because `nhds 0 = pure 0`, so `Tendsto f cofinite (nhds 0)` means `f` is eventually 0).
This yields a linear equivalence with `(Fin 1 →₀ ℕ) →₀ A`, which is free hence flat. -/

omit [NonarchimedeanRing A] in
/-- Under discrete topology, `IsRestricted` is equivalent to having finite support:
the coefficient function `s ↦ coeff s f` is eventually zero along the cofinite filter. -/
theorem isRestricted_iff_finite_support [DiscreteTopology A]
    (f : MvPowerSeries (Fin 1) A) :
    MvPowerSeries.IsRestricted f ↔
      {s : Fin 1 →₀ ℕ | MvPowerSeries.coeff s f ≠ 0}.Finite := by
  unfold MvPowerSeries.IsRestricted
  rw [nhds_discrete, tendsto_pure, Filter.Eventually, Filter.mem_cofinite]
  constructor
  · intro h
    exact h.subset (fun s hs => by simp only [Set.mem_compl_iff] at hs ⊢; exact hs)
  · intro h
    exact h.subset (fun s hs => by simp only [Set.mem_compl_iff] at hs ⊢; exact hs)

omit [NonarchimedeanRing A] in
/-- A finitely supported function gives a restricted power series (discrete case). -/
theorem finsupp_isRestricted [DiscreteTopology A]
    (g : (Fin 1 →₀ ℕ) →₀ A) :
    MvPowerSeries.IsRestricted
      (fun s => g s : MvPowerSeries (Fin 1) A) := by
  rw [isRestricted_iff_finite_support]
  apply g.support.finite_toSet.subset
  intro s hs
  simp only [Set.mem_setOf_eq, MvPowerSeries.coeff_apply] at hs
  exact Finsupp.mem_support_iff.mpr hs

/-- The forward map: `TateAlgebra A → (Fin 1 →₀ ℕ) →₀ A` sending a restricted power
series to the `Finsupp` of its coefficients (discrete case). -/
noncomputable def toFinsupp [DiscreteTopology A]
    (f : ↥(TateAlgebra A)) : (Fin 1 →₀ ℕ) →₀ A :=
  Finsupp.onFinset
    ((isRestricted_iff_finite_support f.val).mp f.prop).toFinset
    (fun s => MvPowerSeries.coeff s f.val)
    (fun s hs => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact hs)

/-- The backward map: `(Fin 1 →₀ ℕ) →₀ A → TateAlgebra A` (discrete case). -/
noncomputable def ofFinsupp [DiscreteTopology A]
    (g : (Fin 1 →₀ ℕ) →₀ A) : ↥(TateAlgebra A) :=
  ⟨fun s => g s, finsupp_isRestricted g⟩

/-- The `A`-linear equivalence `TateAlgebra A ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A` (discrete case).
This exhibits `TateAlgebra A` as a free `A`-module. -/
noncomputable def linearEquivFinsupp [DiscreteTopology A] :
    ↥(TateAlgebra A) ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A where
  toFun f := toFinsupp f
  invFun g := ofFinsupp g
  left_inv f := by
    apply Subtype.ext
    apply MvPowerSeries.ext; intro s
    simp only [ofFinsupp, toFinsupp, Finsupp.onFinset_apply]
    rfl
  right_inv g := by
    ext s
    simp only [toFinsupp, ofFinsupp, Finsupp.onFinset_apply]
    rfl
  map_add' f g := by
    ext s
    simp [toFinsupp, Finsupp.onFinset_apply, Finsupp.add_apply, map_add]
  map_smul' a f := by
    ext s
    simp only [toFinsupp, Finsupp.onFinset_apply, Finsupp.smul_apply, RingHom.id_apply,
      smul_eq_mul, Algebra.smul_def]
    change MvPowerSeries.coeff s (algebraMap A _ a * f.val) = a * MvPowerSeries.coeff s f.val
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]
    simp

/-! #### Ring equivalence with MvPolynomial (discrete case)

Under `[DiscreteTopology A]`, `TateAlgebra A` (restricted power series) consists of
power series with finitely many nonzero coefficients, which are exactly the polynomials.
We build a ring isomorphism `TateAlgebra A ≃+* MvPolynomial (Fin 1) A`. -/

/-- Convert an element of `TateAlgebra A` to `MvPolynomial (Fin 1) A` (discrete case).
This is `toFinsupp` with the correct type annotation for `MvPolynomial`. -/
noncomputable def toMvPolynomial [DiscreteTopology A]
    (f : ↥(TateAlgebra A)) : MvPolynomial (Fin 1) A :=
  toFinsupp f

/-- Convert an `MvPolynomial (Fin 1) A` to `TateAlgebra A` (discrete case).
This is `ofFinsupp` with the correct type annotation for `MvPolynomial`. -/
noncomputable def fromMvPolynomial [DiscreteTopology A]
    (p : MvPolynomial (Fin 1) A) : ↥(TateAlgebra A) :=
  ofFinsupp p

theorem fromMvPolynomial_toMvPolynomial [DiscreteTopology A] (f : ↥(TateAlgebra A)) :
    fromMvPolynomial (toMvPolynomial f) = f :=
  (linearEquivFinsupp (A := A)).left_inv f

theorem toMvPolynomial_fromMvPolynomial [DiscreteTopology A] (p : MvPolynomial (Fin 1) A) :
    toMvPolynomial (fromMvPolynomial p) = p :=
  (linearEquivFinsupp (A := A)).right_inv p

/-- `fromMvPolynomial` preserves multiplication: it is the restriction of the
coercion `MvPolynomial → MvPowerSeries`, which is a ring homomorphism. -/
theorem fromMvPolynomial_mul [DiscreteTopology A] (p q : MvPolynomial (Fin 1) A) :
    fromMvPolynomial (p * q) = fromMvPolynomial p * fromMvPolynomial q := by
  apply Subtype.ext
  show (↑(p * q) : MvPowerSeries (Fin 1) A) =
    (↑p : MvPowerSeries (Fin 1) A) * (↑q : MvPowerSeries (Fin 1) A)
  exact (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1) (R := A)).map_mul p q

theorem fromMvPolynomial_one [DiscreteTopology A] :
    fromMvPolynomial (1 : MvPolynomial (Fin 1) A) = (1 : ↥(TateAlgebra A)) := by
  apply Subtype.ext
  show (↑(1 : MvPolynomial (Fin 1) A) : MvPowerSeries (Fin 1) A) = 1
  exact (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1) (R := A)).map_one

theorem toMvPolynomial_mul [DiscreteTopology A] (f g : ↥(TateAlgebra A)) :
    toMvPolynomial (f * g) = toMvPolynomial f * toMvPolynomial g := by
  apply_fun fromMvPolynomial using fun a b h => by
    have := congr_arg toMvPolynomial h
    rwa [toMvPolynomial_fromMvPolynomial, toMvPolynomial_fromMvPolynomial] at this
  rw [fromMvPolynomial_mul, fromMvPolynomial_toMvPolynomial,
      fromMvPolynomial_toMvPolynomial, fromMvPolynomial_toMvPolynomial]

theorem toMvPolynomial_add [DiscreteTopology A] (f g : ↥(TateAlgebra A)) :
    toMvPolynomial (f + g) = toMvPolynomial f + toMvPolynomial g :=
  (linearEquivFinsupp (A := A)).map_add' f g

/-- The ring equivalence `TateAlgebra A ≃+* MvPolynomial (Fin 1) A` (discrete case).
Under `[DiscreteTopology A]`, the restricted power series ring coincides with the
polynomial ring, and this isomorphism respects both the additive and multiplicative
structure. -/
noncomputable def ringEquivMvPolynomial [DiscreteTopology A] :
    ↥(TateAlgebra A) ≃+* MvPolynomial (Fin 1) A where
  toFun := toMvPolynomial
  invFun := fromMvPolynomial
  left_inv := fromMvPolynomial_toMvPolynomial
  right_inv := toMvPolynomial_fromMvPolynomial
  map_mul' := toMvPolynomial_mul
  map_add' := toMvPolynomial_add

/-! #### Evaluation at f (discrete case)

Under `[DiscreteTopology A]`, the evaluation map `A⟨X⟩ → A` sending `X ↦ f`
is a well-defined ring homomorphism, since elements have finite support. -/

/-- Evaluation of `TateAlgebra A` at `f : A`, defined as the composition
`TateAlgebra A ≃+* MvPolynomial (Fin 1) A →[eval] A` (discrete case). -/
noncomputable def evalFHom [DiscreteTopology A] (f : A) : ↥(TateAlgebra A) →+* A :=
  (MvPolynomial.eval (fun _ => f)).comp ringEquivMvPolynomial.toRingHom

theorem ringEquivMvPolynomial_algebraMap [DiscreteTopology A] (a : A) :
    ringEquivMvPolynomial (algebraMap A (↥(TateAlgebra A)) a) = MvPolynomial.C a := by
  ext s
  simp only [ringEquivMvPolynomial, MvPolynomial.C_apply]
  change MvPowerSeries.coeff s (algebraMap A (MvPowerSeries (Fin 1) A) a) = _
  rw [MvPowerSeries.algebraMap_apply]
  simp [MvPowerSeries.coeff_C, eq_comm]

theorem ringEquivMvPolynomial_X [DiscreteTopology A] :
    ringEquivMvPolynomial (X : ↥(TateAlgebra A)) = MvPolynomial.X (0 : Fin 1) := by
  -- Both sides have the same coefficients: single (single 0 1) 1
  suffices h : ∀ s, MvPolynomial.coeff s (ringEquivMvPolynomial (X : ↥(TateAlgebra A))) =
      MvPolynomial.coeff s (MvPolynomial.X (0 : Fin 1)) by
    ext s; exact h s
  intro s
  -- LHS coefficient
  show @DFunLike.coe _ _ _ Finsupp.instFunLike (toMvPolynomial (X : ↥(TateAlgebra A))) s = _
  simp only [toMvPolynomial, toFinsupp, Finsupp.onFinset_apply]
  change MvPowerSeries.coeff s (MvPowerSeries.X (0 : Fin 1)) = _
  rw [MvPowerSeries.coeff_X]
  -- RHS coefficient
  rw [MvPolynomial.coeff_X']
  simp [eq_comm]

theorem evalFHom_algebraMap [DiscreteTopology A] (f a : A) :
    evalFHom f (algebraMap A _ a) = a := by
  simp only [evalFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [ringEquivMvPolynomial_algebraMap, MvPolynomial.eval_C]

theorem evalFHom_X [DiscreteTopology A] (f : A) :
    evalFHom f X = f := by
  simp only [evalFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [ringEquivMvPolynomial_X, MvPolynomial.eval_X]

theorem evalFHom_surjective [DiscreteTopology A] (f : A) :
    Function.Surjective (evalFHom f) := by
  intro a
  exact ⟨algebraMap A _ a, evalFHom_algebraMap f a⟩

theorem evalFHom_fSubX [DiscreteTopology A] (f : A) :
    evalFHom f (algebraMap A _ f - X) = 0 := by
  rw [map_sub, evalFHom_algebraMap, evalFHom_X, sub_self]

/-- `A⟨X⟩` is flat over `A` (Lemma 8.31(1), flatness part, discrete case).

Under `[DiscreteTopology A]`, `A⟨X⟩ ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A`, which is free
(hence flat) as an `A`-module. -/
instance flat [DiscreteTopology A] : Module.Flat A ↥(TateAlgebra A) :=
  Module.Flat.of_linearEquiv (linearEquivFinsupp (A := A))

/-- `A⟨X⟩` is faithfully flat over `A` (Lemma 8.31(1), discrete case).
Faithful flatness follows from flatness + surjectivity on spectra. -/
instance faithfullyFlat [DiscreteTopology A] : Module.FaithfullyFlat A ↥(TateAlgebra A) :=
  Module.FaithfullyFlat.of_comap_surjective PrimeSpectrum_comap_algebraMap_surjective

/-! #### Quotient flatness via isomorphisms (Lemma 8.31(2), discrete case)

Under `[DiscreteTopology A]`, we prove flatness of the quotients `A⟨X⟩/(f-X)` and
`A⟨X⟩/(1-fX)` directly by constructing isomorphisms:
- `A⟨X⟩/(f-X) ≅ A` via evaluation at `f` (factor theorem)
- `A⟨X⟩/(1-fX) ≅ Localization.Away f` (localization is flat)

**Note:** The general statement "if `g` is a non-zero-divisor in `B` and `B` is flat over `A`,
then `B/(g)` is flat over `A`" is FALSE (counterexample: `g = 2` in `Z[X]`, quotient
`(Z/2Z)[X]` is not flat over `Z`). The correct general statement requires *universal*
regularity: `g·` injective on `M ⊗_A B` for all finitely generated `A`-modules `M`.
For the specific elements `f-X` and `1-fX`, this universal regularity holds,
but we avoid it by using explicit isomorphisms instead. -/

/-- The ideal `Ideal.span {algebraMap f - X}` is contained in `ker evalFHom`.
This is the easy direction of the kernel computation. -/
theorem ideal_fSubX_le_ker_evalFHom [DiscreteTopology A] (f : A) :
    Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} ≤ RingHom.ker (evalFHom f) := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker, hx, evalFHom_fSubX]

/-- The factor theorem for `TateAlgebra A` (discrete case): for every element `p`,
`p - algebraMap(evalFHom f p) ∈ Ideal.span {algebraMap f - X}`.

Proof by induction on an upper bound for the coefficient indices, using
the recursive decomposition `p = algebraMap(coeff 0 p) + X * shift(p)`. -/
theorem sub_algebraMap_evalFHom_mem_ideal_fSubX [DiscreteTopology A] (f : A)
    (p : ↥(TateAlgebra A)) :
    p - algebraMap A _ (evalFHom f p) ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} := by
  -- Helper: coeff of shift
  have coeff_shift : ∀ (q : ↥(TateAlgebra A)) (k : ℕ),
      coeff k (shift q) = coeff (k + 1) q := by
    intro q k
    show MvPowerSeries.coeff (Finsupp.single 0 k) (shiftFun q.val) =
      MvPowerSeries.coeff (Finsupp.single 0 (k + 1)) q.val
    simp [shiftFun, MvPowerSeries.coeff_apply, Finsupp.single_add]
  -- Helper: evalFHom decomposes
  have eval_decomp : ∀ (q : ↥(TateAlgebra A)),
      evalFHom f q = coeff 0 q + f * evalFHom f (shift q) := by
    intro q
    have hd := eq_const_add_X_mul_shift q
    calc evalFHom f q
        = evalFHom f (algebraMap A _ (evalZeroHom q) + X * shift q) := by rw [← hd]
      _ = evalFHom f (algebraMap A _ (evalZeroHom q)) +
          evalFHom f X * evalFHom f (shift q) := by rw [map_add, map_mul]
      _ = coeff 0 q + f * evalFHom f (shift q) := by
          rw [evalFHom_algebraMap, evalFHom_X]; rfl
  -- evalZeroHom = coeff 0
  have eval_zero_eq : ∀ (q : ↥(TateAlgebra A)), evalZeroHom q = coeff 0 q := fun _ => rfl
  -- Key algebraic identity
  have key_identity : ∀ (q : ↥(TateAlgebra A)),
      q - algebraMap A _ (evalFHom f q) =
      X * (shift q - algebraMap A _ (evalFHom f (shift q))) +
      (X - algebraMap A _ f) * algebraMap A _ (evalFHom f (shift q)) := by
    intro q
    rw [eval_decomp q]
    nth_rw 1 [eq_const_add_X_mul_shift q]
    rw [map_add, map_mul, eval_zero_eq]; ring
  -- Induction on upper bound for coefficient indices
  have hmain : ∀ (n : ℕ) (q : ↥(TateAlgebra A)),
      (∀ k, n < k → coeff k q = 0) →
      q - algebraMap A _ (evalFHom f q) ∈
        Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} := by
    intro n; induction n with
    | zero =>
      intro q hq
      -- q has coeff k q = 0 for all k > 0
      -- So shift q = 0 and q = algebraMap(coeff 0 q)
      have hshift_zero : shift q = 0 := by
        apply ext; intro k
        rw [coeff_shift, hq (k + 1) (Nat.succ_pos k)]
        simp [coeff, map_zero]
      -- evalFHom f q = coeff 0 q + f * 0 = coeff 0 q
      have hev : evalFHom f q = coeff 0 q := by
        rw [eval_decomp, hshift_zero, map_zero, mul_zero, add_zero]
      -- q = algebraMap(coeff 0 q) + X * shift q = algebraMap(coeff 0 q)
      have hq0 : q = algebraMap A _ (coeff 0 q) := by
        have := eq_const_add_X_mul_shift q
        rw [hshift_zero, mul_zero, add_zero, eval_zero_eq] at this
        exact this
      -- q - algebraMap(evalFHom f q) = 0 because evalFHom f q = coeff 0 q and q = algebraMap(coeff 0 q)
      have h1 : algebraMap A _ (evalFHom f q) = q := by
        rw [hev]; exact hq0.symm
      rw [h1, sub_self]
      exact Ideal.zero_mem _
    | succ n ih =>
      intro q hq
      rw [key_identity]
      apply Ideal.add_mem
      · apply Ideal.mul_mem_left
        exact ih (shift q) (fun k hk => by rw [coeff_shift]; exact hq _ (by omega))
      · apply Ideal.mul_mem_right
        have hmem : (X : ↥(TateAlgebra A)) - algebraMap A ↥(TateAlgebra A) f =
            -(algebraMap A ↥(TateAlgebra A) f - X) := by ring
        rw [hmem]
        exact neg_mem (Ideal.subset_span rfl)
  -- Apply hmain with a suitable bound derived from finite support
  have hfin : Set.Finite {s : Fin 1 →₀ ℕ | p.val s ≠ 0} :=
    (isRestricted_iff_finite_support p.val).mp p.prop
  by_cases hp : ∀ k, coeff k p = 0
  · rw [(ext hp : p = 0), map_zero, map_zero, sub_self]; exact Ideal.zero_mem _
  · push_neg at hp
    have hne : hfin.toFinset.Nonempty := by
      obtain ⟨k, hk⟩ := hp
      refine ⟨toIndex k, ?_⟩
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, coeff, toIndex] at hk ⊢
      exact hk
    refine hmain (hfin.toFinset.sup' hne (fun s => s 0)) p (fun k hk => ?_)
    by_contra hne2
    have hmem : toIndex k ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, coeff, toIndex] at hne2 ⊢
      exact hne2
    have hle := Finset.le_sup' (fun s : Fin 1 →₀ ℕ => s 0) hmem
    simp only [toIndex, Finsupp.single_apply, ite_true] at hle
    omega

/-- The quotient ring hom from `TateAlgebra A ⧸ (f-X)` to `A`. -/
noncomputable def quotientFSubXToA [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) →+* A :=
  Ideal.Quotient.lift _ (evalFHom f) (fun x hx => by
    exact ideal_fSubX_le_ker_evalFHom f hx)

/-- The ring hom from `A` to `TateAlgebra A ⧸ (f-X)`. -/
noncomputable def AToQuotientFSubX [DiscreteTopology A] (f : A) :
    A →+* (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) :=
  (Ideal.Quotient.mk _).comp (algebraMap A _)

theorem quotientFSubXToA_comp_AToQuotientFSubX [DiscreteTopology A] (f : A) :
    (quotientFSubXToA f).comp (AToQuotientFSubX f) = RingHom.id A := by
  ext a
  simp only [RingHom.comp_apply, AToQuotientFSubX,
    quotientFSubXToA, Ideal.Quotient.lift_mk, evalFHom_algebraMap, RingHom.id_apply]

theorem AToQuotientFSubX_comp_quotientFSubXToA [DiscreteTopology A] (f : A) :
    (AToQuotientFSubX f).comp (quotientFSubXToA f) = RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext p
  simp only [RingHom.comp_apply, RingHom.id_apply, AToQuotientFSubX,
    quotientFSubXToA, Ideal.Quotient.lift_mk]
  -- Need to show: mk(algebraMap(evalFHom f p)) = mk(p)
  -- i.e., p - algebraMap(evalFHom f p) ∈ Ideal.span {f - X}
  symm
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact sub_algebraMap_evalFHom_mem_ideal_fSubX f p

/-- The isomorphism `TateAlgebra A ⧸ (f - X) ≃+* A` (discrete case). -/
noncomputable def quotientFSubXEquiv [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) ≃+* A where
  toFun := quotientFSubXToA f
  invFun := AToQuotientFSubX f
  left_inv x := by
    have h := congr_fun (congr_arg DFunLike.coe
      (AToQuotientFSubX_comp_quotientFSubXToA f)) x
    simp [RingHom.id_apply] at h
    exact h
  right_inv a := by
    have h := congr_fun (congr_arg DFunLike.coe
      (quotientFSubXToA_comp_AToQuotientFSubX f)) a
    simp [RingHom.id_apply] at h
    exact h
  map_mul' := map_mul _
  map_add' := map_add _

/-- Multiplication by `f - X` is injective on `A⟨X⟩` when `A` is noetherian.

The coefficient equations from `(f - X) * u = 0` give `f * coeff n u = coeff n (X * u)`,
which yields `f * coeff 0 u = 0` and `coeff n u = f * coeff (n + 1) u`. The noetherian
ascending chain argument on annihilator ideals forces all coefficients to vanish. -/
theorem mul_fSubX_regular [IsNoetherianRing A] (f : A) :
    ∀ (x : ↥(TateAlgebra A)),
      (algebraMap A _ f - X) * x = 0 → x = 0 := by
  intro u hu
  have hcoeff : ∀ n, f * coeff n u = coeff n (X * u) := by
    intro n
    have h1 : coeff n ((algebraMap A _ f - X) * u) = 0 := by
      rw [hu]; simp [coeff, map_zero]
    rw [sub_mul, coeff_sub, coeff_algebraMap_mul] at h1
    exact sub_eq_zero.mp h1
  have h0 : f * coeff 0 u = 0 := by rw [hcoeff 0, coeff_zero_X_mul]
  have hstep : ∀ n, coeff n u = f * coeff (n + 1) u := by
    intro n; have h := hcoeff (n + 1); rw [coeff_succ_X_mul] at h; exact h.symm
  have hall : ∀ n, coeff n u = 0 := by
    intro n; induction n using Nat.strongRecOn with
    | ind n ih =>
      refine noeth_zero_of_mul_shift f (fun k => coeff (n + k) u) ?_ (fun k => hstep (n + k))
      simp only [Nat.add_zero]
      cases n with
      | zero => exact h0
      | succ m =>
        have hm : coeff m u = 0 := ih m (by omega)
        rw [← hstep m, hm]
  exact ext hall

/-- Multiplication by `1 - f·X` is injective on `A⟨X⟩` when `A` is noetherian.

The coefficient equations from `(1 - fX) * u = 0` give `coeff n u = f * coeff n (X * u)`,
which yields `coeff 0 u = 0` and `coeff (n+1) u = f * coeff n u`. By induction,
all coefficients vanish (no noetherian argument needed in this case). -/
theorem mul_oneSubfX_regular [IsNoetherianRing A] (f : A) :
    ∀ (x : ↥(TateAlgebra A)),
      (1 - algebraMap A _ f * X) * x = 0 → x = 0 := by
  intro u hu
  have hcoeff : ∀ n, coeff n u = f * coeff n (X * u) := by
    intro n
    have h1 : coeff n ((1 - algebraMap A _ f * X) * u) = 0 := by
      rw [hu]; simp [coeff, map_zero]
    rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_algebraMap_mul] at h1
    exact sub_eq_zero.mp h1
  have h0 : coeff 0 u = 0 := by rw [hcoeff 0, coeff_zero_X_mul, mul_zero]
  have hstep : ∀ n, coeff (n + 1) u = f * coeff n u := by
    intro n; rw [hcoeff (n + 1), coeff_succ_X_mul]
  have hall : ∀ n, coeff n u = 0 := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih => rw [hstep n, ih, mul_zero]
  exact ext hall

/-- `A⟨X⟩/(f - X)` is flat over a noetherian `A` (Lemma 8.31(2), first case).
Under discrete topology, `A⟨X⟩/(f-X) ≅ A` via evaluation at `f`, and `A` is flat
over itself. Identifies with `O_X(R(f/1))` in the presheaf. -/
theorem flat_quotient_fSubX [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) := by
  -- The quotient is isomorphic to A as a ring (hence as an A-module),
  -- via quotientFSubXEquiv. A is flat over itself (Module.Flat.self).
  -- Build an A-linear equivalence from the ring equivalence.
  let e := quotientFSubXEquiv f
  have hsmul : ∀ (a : A)
      (x : ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}),
      e (a • x) = a • e x := by
    intro a x
    -- smul by a is the same as multiplication by algebraMap a
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    -- Show e(algebraMap a) = a
    -- Use the fact that quotientFSubXToA_comp_AToQuotientFSubX = id
    have h := congr_fun (congr_arg DFunLike.coe (quotientFSubXToA_comp_AToQuotientFSubX f)) a
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    convert h using 1
  exact Module.Flat.of_linearEquiv
    { e.toAddEquiv with
      map_smul' := hsmul }

/-- `A⟨X⟩/(1 - f·X)` is flat over a noetherian `A` (Lemma 8.31(2), second case).
Under discrete topology, `A⟨X⟩/(1-fX) ≅ Localization.Away f` via the universal
property of localization, and localization is flat.
Identifies with `O_X(R(1/f))` in the presheaf.

**TODO:** Build the explicit isomorphism `A⟨X⟩/(1-fX) ≃ₐ[A] Localization.Away f`
using the MvPolynomial localization equivalence
`IsLocalization.Away.mvPolynomialQuotientEquiv`. -/
theorem flat_quotient_oneSubfX [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) := by
  sorry

end TateAlgebra

/-! ### Quotient equivalence (moved outside namespace for typeclass inference) -/

/-- The isomorphism `A⟨X⟩/(X) ≃+* A`. -/
noncomputable def TateAlgebra.quotientXEquiv {A : Type u}
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    (TateAlgebra A : Type u) ⧸
    (Ideal.span {TateAlgebra.X (A := A)} :
      Ideal (TateAlgebra A)) ≃+* A :=
  (Ideal.quotEquivOfEq TateAlgebra.ker_evalZeroHom.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      TateAlgebra.evalZeroHom_surjective)
