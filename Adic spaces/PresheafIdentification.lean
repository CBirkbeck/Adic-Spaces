/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».TateAlgebra

/-!
# Presheaf Value Identifications (Wedhorn Remark 7.55)

For the 2-element Laurent cover of `Spa(A)`:
- `U₁ = R(f/1) = {v : v(f) ≤ 1}`: presheaf value is `Â` (completion of `A`)
- `U₂ = R(1/f) = {v : v(f) ≥ 1}`: presheaf value is `Â_f` (completion of `A_f`)

We prove the algebraic identifications:
1. When `s` is a unit, `Localization.Away s ≃+* A`, giving `presheafValue D ≃+* A`
   for discrete rings (where completion is trivial).
2. `A⟨X⟩/(f - X) ≃+* A` (from `TateAlgebra.quotientFSubXEquiv`).
3. `A⟨X⟩/(1 - fX) ≃+* Localization.Away f` (from `TateAlgebra.quotientOneSubfXEquiv`).
4. The kernel of the evaluation map `A⟨X⟩ → A_f` equals the ideal `(1 - fX)`.
5. Flatness re-exports connecting presheaf values to Tate algebra quotients.
6. **General (non-discrete) algebraic infrastructure**: `algebraMap f` is a unit
   in `A⟨X⟩/(1-fX)`, the ring hom `Localization.Away f → A⟨X⟩/(1-fX)` from the
   universal property, coefficient analysis forcing `f^k * a → 0` when
   `(1-fX) * q = algebraMap(a) * X^n`, and regularity of `1 - fX`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 7.55, Lemma 8.31, Proposition 8.30
-/

open ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Section 1: Presheaf value when `s` is a unit

When `D.s` is a unit, `Localization.Away D.s ≃ₐ[A] A` by `IsLocalization.atUnit`.
The presheaf value `presheafValue D = Completion (Localization.Away D.s)` is then
isomorphic (as a ring) to `Completion A` via the transferred uniform structure.

For discrete `A`, the completion is trivial, so `presheafValue D ≃+* A`. -/

section UnitS

/-- When `s` is a unit, the `AlgEquiv` from `A` to `Localization.Away s`. -/
noncomputable def localizationAwayUnitEquiv (s : A) (hs : IsUnit s) :
    A ≃ₐ[A] Localization.Away s :=
  IsLocalization.atUnit A (Localization.Away s) s hs

/-- The underlying `RingEquiv` from `Localization.Away s` to `A` when `s` is a unit. -/
noncomputable def localizationAwayUnitRingEquiv (s : A) (hs : IsUnit s) :
    Localization.Away s ≃+* A :=
  (localizationAwayUnitEquiv s hs).toRingEquiv.symm

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- When `s` is a unit, `algebraMap A (Localization.Away s)` composed with the
equivalence back to `A` is the identity. -/
theorem localizationAwayUnit_left_inv (s : A) (hs : IsUnit s) (a : A) :
    (localizationAwayUnitRingEquiv s hs) (algebraMap A (Localization.Away s) a) = a := by
  simp only [localizationAwayUnitRingEquiv, localizationAwayUnitEquiv,
    RingEquiv.symm_apply_eq]
  exact (AlgEquiv.commutes (IsLocalization.atUnit A (Localization.Away s) s hs) a).symm

/-- For discrete `A` with unit `s`, the presheaf value `presheafValue D` is
isomorphic to `A` as a ring, via the completion bijection and the localization
equivalence. -/
noncomputable def presheafValueRingEquivOfUnitS [DiscreteTopology A]
    (D : RationalLocData A) (hs : IsUnit D.s) :
    presheafValue D ≃+* A :=
  (RingEquiv.ofBijective D.coeRingHom (coeRingHom_bijective_of_discrete D)).symm.trans
    (localizationAwayUnitRingEquiv D.s hs)

/-- For discrete `A` with unit `s`, the canonical map `A → presheafValue D` composed
with `presheafValueRingEquivOfUnitS` is the identity. -/
theorem presheafValueRingEquivOfUnitS_canonicalMap [DiscreteTopology A]
    (D : RationalLocData A) (hs : IsUnit D.s) (a : A) :
    presheafValueRingEquivOfUnitS D hs (D.canonicalMap a) = a := by
  simp only [presheafValueRingEquivOfUnitS, RingEquiv.trans_apply]
  have hcoe : (RingEquiv.ofBijective D.coeRingHom
      (coeRingHom_bijective_of_discrete D)).symm (D.canonicalMap a) =
      algebraMap A (Localization.Away D.s) a := by
    rw [RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply]
    rfl
  rw [hcoe]
  exact localizationAwayUnit_left_inv D.s hs a

end UnitS

/-! ### Section 2: Tate algebra quotient identifications (discrete case)

The existing `TateAlgebra.quotientFSubXEquiv` and `TateAlgebra.quotientOneSubfXEquiv`
give the algebraic identifications:
- `A⟨X⟩/(f - X) ≃+* A` (evaluation at `f`)
- `A⟨X⟩/(1 - fX) ≃+* Localization.Away f` (evaluation at `1/f`)

We package these into the presheaf framework. -/

section TateQuotients

variable [NonarchimedeanRing A] [DiscreteTopology A]

/-- For discrete `A`, `A⟨X⟩/(f - X) ≃+* A` (Wedhorn Remark 7.55, first case).
This identifies the presheaf value at `R(f/1)` with `A` algebraically. -/
noncomputable def tateQuotientFSubXEquiv (f : A) :
    (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) ≃+* A :=
  TateAlgebra.quotientFSubXEquiv f

/-- For discrete `A`, `A⟨X⟩/(1 - fX) ≃+* Localization.Away f` (Wedhorn Remark 7.55,
second case). This identifies the presheaf value at `R(1/f)` with the localization. -/
noncomputable def tateQuotientOneSubfXEquiv (f : A) :
    (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) ≃+*
      Localization.Away f :=
  TateAlgebra.quotientOneSubfXEquiv f

/-- The Tate quotient `A⟨X⟩/(f - X)` is isomorphic to the presheaf value for
a rational localization datum with unit `s`, in the discrete case.

The chain: `A⟨X⟩/(f - X) ≃ A ≃ Localization.Away s ≃ presheafValue D`. -/
noncomputable def tateQuotientFSubX_presheafValue_equiv
    (D : RationalLocData A) (hs : IsUnit D.s) (f : A) :
    (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) ≃+*
      presheafValue D :=
  (tateQuotientFSubXEquiv f).trans
    ((localizationAwayUnitRingEquiv D.s hs).symm.trans
      (RingEquiv.ofBijective D.coeRingHom (coeRingHom_bijective_of_discrete D)))

/-- The Tate quotient `A⟨X⟩/(1 - fX)` is isomorphic to the presheaf value for
a rational localization datum with `s = f`, in the discrete case.

The chain: `A⟨X⟩/(1 - fX) ≃ Localization.Away f ≃ presheafValue D`. -/
noncomputable def tateQuotientOneSubfX_presheafValue_equiv
    (D : RationalLocData A) (f : A) (hf : D.s = f) :
    (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) ≃+*
      presheafValue D := by
  subst hf
  exact (tateQuotientOneSubfXEquiv D.s).trans
    (RingEquiv.ofBijective D.coeRingHom (coeRingHom_bijective_of_discrete D))

end TateQuotients

/-! ### Section 3: Flatness re-exports

For discrete noetherian `A`:
- `A⟨X⟩/(f - X)` is flat over `A` (it is isomorphic to `A`).
- `A⟨X⟩/(1 - fX)` is flat over `A` (it is isomorphic to `Localization.Away f`).
- `presheafValue D` is flat over `A` (it is isomorphic to `Localization.Away D.s`).

The first two are proved in `TateAlgebra.lean`; we re-export them and connect to presheaf
values. The third is proved in `FlatnessResults.lean`. -/

section Flatness

variable [NonarchimedeanRing A] [DiscreteTopology A]

omit [IsTopologicalRing A] in
/-- `A⟨X⟩/(f - X)` is flat over `A` (re-export from `TateAlgebra.flat_quotient_fSubX`). -/
theorem tateQuotient_fSubX_flat [IsNoetherianRing A] (f : A) :
    Module.Flat A
      (↥(TateAlgebra A) ⧸
        Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X}) :=
  TateAlgebra.flat_quotient_fSubX f

omit [IsTopologicalRing A] in
/-- `A⟨X⟩/(1 - fX)` is flat over `A` (re-export from `TateAlgebra.flat_quotient_oneSubfX`). -/
theorem tateQuotient_oneSubfX_flat [IsNoetherianRing A] (f : A) :
    Module.Flat A
      (↥(TateAlgebra A) ⧸
        Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}) :=
  TateAlgebra.flat_quotient_oneSubfX f

omit [NonarchimedeanRing A] in
/-- For discrete `A` with unit `s`, the ring isomorphism
`presheafValue D ≃+* A` respects the `A`-algebra structure:
the canonical map followed by the equivalence is the identity.

This makes explicit that flatness of `A` over itself transfers to flatness
of `presheafValue D` over `A` when `s` is a unit. -/
theorem presheafValueRingEquivOfUnitS_algebraMap
    (D : RationalLocData A) (hs : IsUnit D.s) :
    ∀ a : A, (presheafValueRingEquivOfUnitS D hs) (D.canonicalMap a) = a :=
  presheafValueRingEquivOfUnitS_canonicalMap D hs

end Flatness

/-! ### Section 4: Laurent cover identification bridge

For the Laurent cover `{R(f/1), R(1/f)}`:
- The presheaf at `R(f/1)` identifies with `Â` (completion of `A`).
- The presheaf at `R(1/f)` identifies with `Â_f` (completion of `A_f`).

For discrete `A`:
- `O_X(R(f/1)) ≅ A` and `O_X(R(1/f)) ≅ Localization.Away f`.
- Both are flat over `A`, and the product is faithfully flat.

We prove the key bridge lemma: the evaluation homomorphism
`TateAlgebra A → Localization.Away f` has kernel equal to `(1 - fX)`,
connecting the Tate algebra quotient to the localization. -/

section LaurentBridge

variable [NonarchimedeanRing A] [DiscreteTopology A]

omit [IsTopologicalRing A] in
/-- The evaluation map `evalInvFHom f : A⟨X⟩ →+* Localization.Away f` sends `X ↦ 1/f`.
Its kernel is `(1 - fX)`, and the induced quotient map is the ring equivalence
`quotientOneSubfXEquiv`. This is the algebraic core of the R(1/f) identification. -/
theorem evalInvF_kernel_eq_oneSubfX (f : A) :
    RingHom.ker (TateAlgebra.evalInvFHom f) =
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X} := by
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    have h := TateAlgebra.locToQuotientOneSubfX_comp_quotientOneSubfXToLoc f
    have hmk : (TateAlgebra.locToQuotientOneSubfX f)
        (TateAlgebra.quotientOneSubfXToLoc f ((Ideal.Quotient.mk _) x)) =
        (Ideal.Quotient.mk _) x := by
      have := congr_fun (congr_arg DFunLike.coe h) ((Ideal.Quotient.mk _) x)
      simp only [RingHom.comp_apply, RingHom.id_apply] at this
      exact this
    rw [show TateAlgebra.quotientOneSubfXToLoc f ((Ideal.Quotient.mk _) x) =
        TateAlgebra.evalInvFHom f x from by
      simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk]] at hmk
    rw [hx, map_zero] at hmk
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk.symm
  · intro hx
    rw [RingHom.mem_ker]
    have : TateAlgebra.quotientOneSubfXToLoc f ((Ideal.Quotient.mk _) x) =
        TateAlgebra.evalInvFHom f x := by
      simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk]
    rw [← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

omit [IsTopologicalRing A] in
/-- The composition `algebraMap A (Localization.Away f)` factors through the
Tate quotient: `A → A⟨X⟩/(1-fX) → Localization.Away f`, and the second map
is an isomorphism. -/
theorem algebraMap_factors_through_tateQuotient (f : A) (a : A) :
    (TateAlgebra.quotientOneSubfXEquiv f)
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) =
    algebraMap A (Localization.Away f) a := by
  change TateAlgebra.quotientOneSubfXToLoc f
    ((Ideal.Quotient.mk _) (algebraMap A _ a)) = algebraMap A _ a
  simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
    TateAlgebra.evalInvFHom_algebraMap]

omit [IsTopologicalRing A] in
/-- The composition `algebraMap A A` factors through the Tate quotient `A⟨X⟩/(f-X)`:
`A → A⟨X⟩/(f-X) → A`, and the second map is an isomorphism (the identity). -/
theorem algebraMap_factors_through_tateQuotientFSubX (f : A) (a : A) :
    (TateAlgebra.quotientFSubXEquiv f)
      ((Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) a)) = a := by
  change TateAlgebra.quotientFSubXToA f
    ((Ideal.Quotient.mk _) (algebraMap A _ a)) = a
  have := congr_fun (congr_arg DFunLike.coe
    (TateAlgebra.quotientFSubXToA_comp_AToQuotientFSubX f)) a
  simp only [RingHom.comp_apply, RingHom.id_apply] at this
  exact this

end LaurentBridge

/-! ### Section 5: General (non-discrete) Tate quotient algebraic infrastructure

The algebraic core of the `R(1/f)` identification for general nonarchimedean
rings, without any discrete topology assumption. We prove:

1. `algebraMap A f` is a unit in `A⟨X⟩/(1-fX)` (purely algebraic).
2. The ring hom `Localization.Away f → A⟨X⟩/(1-fX)` from the universal
   property of localization.
3. The coefficient recurrence for `(1-fX) * q = algebraMap(a) * X^n`:
   `coeff(n+k)(q) = f^k * a`, forcing `f^k * a → 0` since `q` is restricted.
4. Regularity of `1 - fX` in `A⟨X⟩` (re-export of `mul_oneSubfX_regular`).
5. The composition `quotientOneSubfXToLoc ∘ locToQuotientOneSubfX_gen = id`
   (one direction, connecting to the discrete case).

These results are used in the presheaf identification of `R(1/f)` with the
completion of `Localization.Away f` (Wedhorn Remark 7.55, Proposition 8.30).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, Proposition 8.30
-/

section GeneralTateQuotient

variable [NonarchimedeanRing A]

/-- The ideal `(1 - fX)` in `A⟨X⟩`. No discrete topology needed. -/
noncomputable def oneSubfXIdeal (f : A) : Ideal ↥(TateAlgebra A) :=
  Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X}

omit [IsTopologicalRing A] in
/-- In the quotient `A⟨X⟩/(1-fX)`, the product `fX = 1`.
Purely algebraic (Wedhorn Proposition 8.30). -/
theorem fX_eq_one_in_quotient (f : A) :
    (Ideal.Quotient.mk (oneSubfXIdeal f))
      (algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) = 1 := by
  rw [← sub_eq_zero]
  change (Ideal.Quotient.mk _) (algebraMap A _ f * TateAlgebra.X) -
    (Ideal.Quotient.mk _) 1 = 0
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [show algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X - 1 =
    -(1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X) from by ring]
  exact neg_mem (Ideal.subset_span rfl)

omit [IsTopologicalRing A] in
/-- `X` is the two-sided inverse of `algebraMap f` in `A⟨X⟩/(1-fX)`. -/
theorem X_mul_f_eq_one_in_quotient (f : A) :
    (Ideal.Quotient.mk (oneSubfXIdeal f)) TateAlgebra.X *
    (Ideal.Quotient.mk (oneSubfXIdeal f))
      (algebraMap A ↥(TateAlgebra A) f) = 1 := by
  rw [← map_mul, mul_comm]; exact fX_eq_one_in_quotient f

omit [IsTopologicalRing A] in
/-- The image of `f` under `A → A⟨X⟩/(1-fX)` is a unit with inverse
`mk(X)`. No discrete topology needed (Wedhorn Proposition 8.30). -/
theorem isUnit_algebraMap_f_in_quotient_gen (f : A) :
    IsUnit (((Ideal.Quotient.mk (oneSubfXIdeal f)).comp
        (algebraMap A _)) f) := by
  rw [RingHom.comp_apply, isUnit_iff_exists_inv]
  exact ⟨(Ideal.Quotient.mk _) TateAlgebra.X,
    by rw [← map_mul]; exact fX_eq_one_in_quotient f⟩

/-- Ring hom `Localization.Away f → A⟨X⟩/(1-fX)` from the universal
property of localization. Sends `algebraMap(a) ↦ mk(algebraMap a)` and
`1/f ↦ mk(X)`. No discrete topology needed. -/
noncomputable def locToQuotientOneSubfX_gen (f : A) :
    Localization.Away f →+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  IsLocalization.Away.lift (x := f)
    (isUnit_algebraMap_f_in_quotient_gen f)

omit [IsTopologicalRing A] in
/-- `locToQuotientOneSubfX_gen` commutes with `algebraMap`. -/
theorem locToQuotientOneSubfX_gen_algebraMap (f a : A) :
    locToQuotientOneSubfX_gen f (algebraMap A _ a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  simp only [locToQuotientOneSubfX_gen,
    IsLocalization.Away.lift_eq]
  rfl

omit [IsTopologicalRing A] in
/-- `locToQuotientOneSubfX_gen` sends `1/f` to `mk(X)`. -/
theorem locToQuotientOneSubfX_gen_invSelf (f : A) :
    locToQuotientOneSubfX_gen f
      (IsLocalization.Away.invSelf
        (S := Localization.Away f) f) =
      (Ideal.Quotient.mk (oneSubfXIdeal f))
        TateAlgebra.X := by
  have hunit : IsUnit ((Ideal.Quotient.mk (oneSubfXIdeal f))
      (algebraMap A _ f)) :=
    ⟨⟨_, _,
      by rw [← map_mul]; exact fX_eq_one_in_quotient f,
      by rw [← map_mul, mul_comm]
         exact fX_eq_one_in_quotient f⟩,
     rfl⟩
  have h1 : (Ideal.Quotient.mk (oneSubfXIdeal f))
      (algebraMap A _ f) *
      locToQuotientOneSubfX_gen f
        (IsLocalization.Away.invSelf
          (S := Localization.Away f) f) = 1 := by
    rw [← locToQuotientOneSubfX_gen_algebraMap, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have h2 : (Ideal.Quotient.mk (oneSubfXIdeal f))
      (algebraMap A _ f) *
      (Ideal.Quotient.mk (oneSubfXIdeal f))
        TateAlgebra.X = 1 := by
    rw [← map_mul]; exact fX_eq_one_in_quotient f
  exact hunit.mul_left_cancel (h1.trans h2.symm)

omit [IsTopologicalRing A] in
/-- The composition `quotientOneSubfXToLoc ∘ locToQuotientOneSubfX_gen`
equals the identity on `Localization.Away f` (discrete case bridge). -/
theorem quotientOneSubfXToLoc_comp_gen
    [DiscreteTopology A] (f : A) :
    (TateAlgebra.quotientOneSubfXToLoc f).comp
      (locToQuotientOneSubfX_gen f) =
      RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  change (TateAlgebra.quotientOneSubfXToLoc f)
    (locToQuotientOneSubfX_gen f (algebraMap A _ a)) =
    algebraMap A _ a
  unfold locToQuotientOneSubfX_gen oneSubfXIdeal
  rw [IsLocalization.Away.lift_eq]
  simp only [RingHom.comp_apply]
  change TateAlgebra.quotientOneSubfXToLoc f
    ((Ideal.Quotient.mk _) (algebraMap A _ a)) = _
  simp only [TateAlgebra.quotientOneSubfXToLoc,
    Ideal.Quotient.lift_mk,
    TateAlgebra.evalInvFHom_algebraMap]

omit [IsTopologicalRing A] in
/-- Multiplication by `1 - fX` is injective on `A⟨X⟩` for noetherian
`A`. No discrete topology needed.
Re-export of `TateAlgebra.mul_oneSubfX_regular`. -/
theorem oneSubfX_regular [IsNoetherianRing A] (f : A)
    (x : ↥(TateAlgebra A))
    (hx : (1 - algebraMap A _ f * TateAlgebra.X) * x = 0) :
    x = 0 :=
  TateAlgebra.mul_oneSubfX_regular f x hx

omit [IsTopologicalRing A] in
/-- The ideal `(1 - fX)` is contained in the kernel of any ring hom
`φ : A⟨X⟩ → R` satisfying `φ(algebraMap f) * φ(X) = 1`. -/
theorem oneSubfX_le_ker_of_eval {R : Type*} [CommRing R]
    (f : A) (φ : ↥(TateAlgebra A) →+* R)
    (hφ : φ (algebraMap A _ f) * φ TateAlgebra.X = 1) :
    oneSubfXIdeal f ≤ RingHom.ker φ := by
  rw [oneSubfXIdeal, Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, RingHom.mem_ker, hx, map_sub,
    map_one, map_mul, sub_eq_zero]
  exact hφ.symm

/-! #### Coefficient analysis for `(1-fX)` membership -/

omit [IsTopologicalRing A] in
private theorem coeff_X_pow_eq' (n : ℕ) :
    TateAlgebra.coeff n
      (TateAlgebra.X ^ n : ↥(TateAlgebra A)) = 1 := by
  induction n with
  | zero =>
    simp only [pow_zero, TateAlgebra.coeff, TateAlgebra.toIndex_zero]
    norm_cast
  | succ n ih =>
    rw [pow_succ, mul_comm, TateAlgebra.coeff_succ_X_mul]
    exact ih

omit [IsTopologicalRing A] in
private theorem coeff_X_pow_ne' {k n : ℕ} (h : k ≠ n) :
    TateAlgebra.coeff k
      (TateAlgebra.X ^ n : ↥(TateAlgebra A)) = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd rfl h
    | succ k =>
      simp only [pow_zero, TateAlgebra.coeff, TateAlgebra.toIndex]
      norm_cast
      rw [MvPowerSeries.coeff_one,
        if_neg (Finsupp.single_ne_zero.mpr (by omega))]
  | succ n ih =>
    rw [pow_succ, mul_comm]; cases k with
    | zero => exact TateAlgebra.coeff_zero_X_mul _
    | succ k =>
      rw [TateAlgebra.coeff_succ_X_mul]; exact ih (by omega)

omit [IsTopologicalRing A] in
/-- If `(1 - fX) * q = algebraMap(a) * X^n` in `A⟨X⟩`, then
`coeff k q = 0` for `k < n` and `coeff (n+k) q = f^k * a` for
`k ≥ 0`.

Since `q` is a restricted power series (`coeff k q → 0`), this
forces `f^k * a → 0`. In the noetherian Hausdorff case, this
implies `f^m * a = 0` for some `m`, hence `a/f^n = 0` in
`Localization.Away f`.

This is the coefficient-level core of the kernel identification
`ker(eval) = (1-fX)`. No discrete topology needed
(Wedhorn Proposition 8.30). -/
theorem coeff_of_oneSubfX_eq_aXn (f a : A) (n : ℕ)
    (q : ↥(TateAlgebra A))
    (h : (1 - algebraMap A _ f * TateAlgebra.X) * q =
      algebraMap A _ a * TateAlgebra.X ^ n) :
    (∀ k, k < n → TateAlgebra.coeff k q = 0) ∧
    (∀ k, TateAlgebra.coeff (n + k) q = f ^ k * a) := by
  have h_base : TateAlgebra.coeff 0 q =
      if (0 : ℕ) = n then a else 0 := by
    have hc : TateAlgebra.coeff 0
        ((1 - algebraMap A _ f * TateAlgebra.X) * q) =
        TateAlgebra.coeff 0 q := by
      rw [sub_mul, one_mul, mul_assoc, TateAlgebra.coeff_sub,
        TateAlgebra.coeff_algebraMap_mul,
        TateAlgebra.coeff_zero_X_mul, mul_zero, sub_zero]
    rw [h] at hc; rw [← hc, TateAlgebra.coeff_algebraMap_mul]
    split
    · next heq => subst heq; rw [coeff_X_pow_eq', mul_one]
    · next hne => rw [coeff_X_pow_ne' hne, mul_zero]
  have h_step : ∀ m, TateAlgebra.coeff (m + 1) q =
      f * TateAlgebra.coeff m q +
        (if m + 1 = n then a else 0) := by
    intro m
    have hc : TateAlgebra.coeff (m + 1) q -
        f * TateAlgebra.coeff m q =
        TateAlgebra.coeff (m + 1)
          (algebraMap A _ a * TateAlgebra.X ^ n) := by
      have : TateAlgebra.coeff (m + 1)
          ((1 - algebraMap A _ f * TateAlgebra.X) * q) =
          TateAlgebra.coeff (m + 1) q -
            f * TateAlgebra.coeff m q := by
        rw [sub_mul, one_mul, mul_assoc,
          TateAlgebra.coeff_sub, TateAlgebra.coeff_algebraMap_mul,
          TateAlgebra.coeff_succ_X_mul]
      rw [← h, this]
    rw [TateAlgebra.coeff_algebraMap_mul] at hc
    by_cases hmn : m + 1 = n
    · subst hmn; rw [coeff_X_pow_eq', mul_one] at hc
      rw [if_pos rfl, sub_eq_iff_eq_add.mp hc]; ring
    · rw [coeff_X_pow_ne' hmn, mul_zero] at hc
      rw [if_neg hmn, sub_eq_zero.mp hc, add_zero]
  have hlt : ∀ k, k < n → TateAlgebra.coeff k q = 0 := by
    intro k hk; induction k with
    | zero => rw [h_base, if_neg (by omega)]
    | succ k ih =>
      rw [h_step k, ih (by omega), mul_zero, zero_add,
        if_neg (by omega)]
  constructor
  · exact hlt
  · intro k; induction k with
    | zero =>
      simp only [Nat.add_zero, pow_zero, one_mul]
      cases n with
      | zero => rw [h_base, if_pos rfl]
      | succ n =>
        rw [h_step n, hlt n (by omega), mul_zero,
          zero_add, if_pos rfl]
    | succ k ih =>
      rw [show n + (k + 1) = n + k + 1 from by omega,
        h_step (n + k), ih, if_neg (by omega), add_zero,
        pow_succ]; ring

end GeneralTateQuotient

/-! ### Section 6: Completion extension — Tate algebra to presheaf value (non-discrete)

For a rational localization datum `D`, we establish the algebraic infrastructure connecting
the Tate algebra `A⟨X⟩` to the presheaf value `presheafValue D` (completion of
`Localization.Away D.s`).

The key results:
1. `D.s` maps to a unit in `presheafValue D` via the canonical map.
2. The lift `Localization.Away D.s →+* presheafValue D` from `IsLocalization.Away.lift`
   agrees with the completion embedding `D.coeRingHom`.
3. The ring hom `Localization.Away D.s → A⟨X⟩/(1-sX)` from `locToQuotientOneSubfX_gen`
   composes with the completion embedding to give a map from `A⟨X⟩/(1-sX)` to
   `presheafValue D` (in the discrete case).
4. The ideal `(1-sX)` is in the kernel of any evaluation-type ring hom
   `A⟨X⟩ → presheafValue D` (from `oneSubfX_le_ker_of_eval`).

These results do not require `DiscreteTopology A` (except where noted) and are used in
the Tate acyclicity proof (Wedhorn Proposition 8.30, Remark 7.55).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 5.32, 5.49, 8.30
-/

section CompletionExtension

variable [NonarchimedeanRing A]

/-! #### The canonical map `A → presheafValue D` and unit of `s` -/

omit [NonarchimedeanRing A] in
/-- The image of `D.s` under `algebraMap A (Localization.Away D.s)` is a unit.
This is a direct consequence of the universal property of localization. -/
theorem isUnit_algebraMap_s (D : RationalLocData A) :
    IsUnit (algebraMap A (Localization.Away D.s) D.s) :=
  IsLocalization.Away.algebraMap_isUnit D.s

omit [NonarchimedeanRing A] in
/-- The image of `D.s` under `D.coeRingHom ∘ algebraMap` (i.e., in `presheafValue D`)
is a unit. The unit in the localization transfers through the completion embedding. -/
theorem isUnit_s_in_presheafValue (D : RationalLocData A) :
    IsUnit (D.canonicalMap D.s) :=
  (isUnit_algebraMap_s D).map D.coeRingHom

/-- The unit of `D.s` in `presheafValue D`, extracted from `isUnit_s_in_presheafValue`. -/
noncomputable def sUnit (D : RationalLocData A) : (presheafValue D)ˣ :=
  (isUnit_s_in_presheafValue D).unit

/-- The inverse of `D.s` in `presheafValue D`. -/
noncomputable def invS (D : RationalLocData A) : presheafValue D :=
  ↑(sUnit D)⁻¹

omit [NonarchimedeanRing A] in
/-- `canonicalMap(s) * invS = 1` in `presheafValue D`. -/
theorem canonicalMap_s_mul_invS (D : RationalLocData A) :
    D.canonicalMap D.s * invS D = 1 := by
  change D.canonicalMap D.s * ↑(isUnit_s_in_presheafValue D).unit⁻¹ = 1
  exact (isUnit_s_in_presheafValue D).mul_val_inv

omit [NonarchimedeanRing A] in
/-- `invS * canonicalMap(s) = 1` in `presheafValue D`. -/
theorem invS_mul_canonicalMap_s (D : RationalLocData A) :
    invS D * D.canonicalMap D.s = 1 := by
  rw [mul_comm]; exact canonicalMap_s_mul_invS D

/-! #### The lift from Localization.Away to presheafValue via IsLocalization.Away.lift -/

/-- The ring hom `Localization.Away D.s →+* presheafValue D` obtained from the
universal property of localization, using the fact that `D.s` maps to a unit
in `presheafValue D`.

This agrees with `D.coeRingHom` (the completion embedding) by uniqueness of the
localization lift. -/
noncomputable def locLiftToPresheaf (D : RationalLocData A) :
    Localization.Away D.s →+* presheafValue D :=
  IsLocalization.Away.lift D.s (isUnit_s_in_presheafValue D)

omit [NonarchimedeanRing A] in
/-- `locLiftToPresheaf` agrees with `canonicalMap` on elements of `A`. -/
theorem locLiftToPresheaf_algebraMap (D : RationalLocData A) (a : A) :
    locLiftToPresheaf D (algebraMap A _ a) = D.canonicalMap a := by
  simp only [locLiftToPresheaf, IsLocalization.Away.lift_eq, RationalLocData.canonicalMap]

omit [NonarchimedeanRing A] in
/-- `locLiftToPresheaf` equals `D.coeRingHom` (uniqueness of localization lift). -/
theorem locLiftToPresheaf_eq_coeRingHom (D : RationalLocData A) :
    locLiftToPresheaf D = D.coeRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext a
  simp only [RingHom.comp_apply, locLiftToPresheaf_algebraMap,
    RationalLocData.canonicalMap, RationalLocData.coeRingHom]

/-! #### The evaluation map in the discrete case -/

/-- In the discrete case, the evaluation ring hom `A⟨X⟩ →+* presheafValue D` that
sends `X` to `s⁻¹` in the completion. This is the composition:
`A⟨X⟩ →[evalInvFHom] Localization.Away s →[coeRingHom] presheafValue D`.

Since `evalInvFHom` evaluates at `1/s` in the localization, and `coeRingHom` embeds
into the completion, the composition evaluates at `s⁻¹` in the presheaf value. -/
noncomputable def evalPresheafHom [DiscreteTopology A]
    (D : RationalLocData A) :
    ↥(TateAlgebra A) →+* presheafValue D :=
  D.coeRingHom.comp (TateAlgebra.evalInvFHom D.s)

/-- `evalPresheafHom` sends `algebraMap(a)` to `canonicalMap(a)`. -/
theorem evalPresheafHom_algebraMap [DiscreteTopology A]
    (D : RationalLocData A) (a : A) :
    evalPresheafHom D (algebraMap A _ a) = D.canonicalMap a := by
  simp only [evalPresheafHom, RingHom.comp_apply, TateAlgebra.evalInvFHom_algebraMap,
    RationalLocData.canonicalMap]

/-- `evalPresheafHom` sends `X` to `invS D` (the inverse of `s` in `presheafValue D`).
In the discrete case, `coeRingHom` is bijective, so the image of `invSelf` under
`coeRingHom` equals `invS D`. -/
theorem evalPresheafHom_X [DiscreteTopology A]
    (D : RationalLocData A) :
    evalPresheafHom D TateAlgebra.X =
      D.coeRingHom (IsLocalization.Away.invSelf
        (S := Localization.Away D.s) D.s) := by
  simp only [evalPresheafHom, RingHom.comp_apply, TateAlgebra.evalInvFHom_X]

/-- `evalPresheafHom` sends `1 - sX` to `0`. -/
theorem evalPresheafHom_oneSubsX [DiscreteTopology A]
    (D : RationalLocData A) :
    evalPresheafHom D (1 - algebraMap A _ D.s * TateAlgebra.X) = 0 := by
  simp only [evalPresheafHom, RingHom.comp_apply, TateAlgebra.evalInvFHom_oneSubfX,
    map_zero]

/-- The ideal `(1 - sX)` is contained in the kernel of `evalPresheafHom`. -/
theorem oneSubsX_le_ker_evalPresheafHom [DiscreteTopology A]
    (D : RationalLocData A) :
    oneSubfXIdeal D.s ≤ RingHom.ker (evalPresheafHom D) := by
  rw [oneSubfXIdeal, Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, RingHom.mem_ker, hx]
  exact evalPresheafHom_oneSubsX D

/-- The kernel of `evalPresheafHom` equals the ideal `(1 - sX)`, in the discrete case. -/
theorem ker_evalPresheafHom [DiscreteTopology A]
    (D : RationalLocData A) :
    RingHom.ker (evalPresheafHom D) = oneSubfXIdeal D.s := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    simp only [evalPresheafHom, RingHom.comp_apply] at hx
    have hinj := (coeRingHom_bijective_of_discrete D).1
    have hker : TateAlgebra.evalInvFHom D.s x = 0 :=
      hinj (hx.trans (map_zero D.coeRingHom).symm)
    have hker' : x ∈ RingHom.ker (TateAlgebra.evalInvFHom D.s) :=
      RingHom.mem_ker.mpr hker
    rwa [evalInvF_kernel_eq_oneSubfX] at hker'
  · exact oneSubsX_le_ker_evalPresheafHom D

/-- The quotient ring hom `A⟨X⟩/(1-sX) →+* presheafValue D` induced by `evalPresheafHom`,
in the discrete case. Since `ker(evalPresheafHom) = (1-sX)`, this is injective. -/
noncomputable def quotientEvalPresheafHom [DiscreteTopology A]
    (D : RationalLocData A) :
    (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) →+* presheafValue D :=
  Ideal.Quotient.lift (oneSubfXIdeal D.s) (evalPresheafHom D)
    (fun _ hx ↦ oneSubsX_le_ker_evalPresheafHom D hx)

/-- `quotientEvalPresheafHom` is injective (the kernel of `evalPresheafHom` is
exactly `(1-sX)`). -/
theorem quotientEvalPresheafHom_injective [DiscreteTopology A]
    (D : RationalLocData A) :
    Function.Injective (quotientEvalPresheafHom D) :=
  RingHom.lift_injective_of_ker_le_ideal _ _
    (ker_evalPresheafHom D).le

/-! #### General (non-discrete) presheaf value ring hom from quotient

For general nonarchimedean `A`, we construct a ring hom from the Tate quotient
`A⟨X⟩/(1-sX)` to `presheafValue D` by composing the localization map
`locToQuotientOneSubfX_gen` (which goes `Loc → Quotient`) with the completion
embedding going in the other direction. Specifically, we use the composition:

`A⟨X⟩/(1-sX) →[locToQuotientOneSubfX_gen composed with coeRingHom]→ presheafValue D`

The map `locToQuotientOneSubfX_gen : Localization.Away s → A⟨X⟩/(1-sX)` is a ring hom.
The composition `D.coeRingHom ∘ some_inverse` would require the inverse of
`locToQuotientOneSubfX_gen`, which we have in the discrete case.

Instead, we define the quotient-to-presheaf map via `Ideal.Quotient.lift`, using the
fact that any ring hom `A⟨X⟩ → R` with `φ(algebraMap s) * φ(X) = 1` has `(1-sX)` in
its kernel. -/

/-- The ring hom `A⟨X⟩/(1-sX) →+* presheafValue D` in the discrete case,
via the chain `A⟨X⟩/(1-sX) ≃ Localization.Away s →[coeRingHom] presheafValue D`.
This is an alternative construction equivalent to `quotientEvalPresheafHom`. -/
noncomputable def quotientToPresheaf [DiscreteTopology A]
    (D : RationalLocData A) :
    (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) →+* presheafValue D :=
  D.coeRingHom.comp (TateAlgebra.quotientOneSubfXToLoc D.s)

/-- `quotientToPresheaf` sends `mk(algebraMap a)` to `canonicalMap a`. -/
theorem quotientToPresheaf_algebraMap [DiscreteTopology A]
    (D : RationalLocData A) (a : A) :
    quotientToPresheaf D ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  unfold quotientToPresheaf
  rw [RingHom.comp_apply]
  change D.coeRingHom (TateAlgebra.quotientOneSubfXToLoc D.s
    ((Ideal.Quotient.mk _) (algebraMap A _ a))) = _
  simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
    TateAlgebra.evalInvFHom_algebraMap, RationalLocData.canonicalMap,
    RingHom.comp_apply]

/-- `quotientToPresheaf` agrees with `quotientEvalPresheafHom`. Both send
`mk(p)` to `coeRingHom(evalInvFHom(p))`. -/
theorem quotientToPresheaf_eq_quotientEvalPresheafHom [DiscreteTopology A]
    (D : RationalLocData A) :
    quotientToPresheaf D = quotientEvalPresheafHom D := by
  ext ⟨p⟩
  unfold quotientToPresheaf quotientEvalPresheafHom evalPresheafHom
  simp only [RingHom.comp_apply]
  change D.coeRingHom (TateAlgebra.quotientOneSubfXToLoc D.s
    ((Ideal.Quotient.mk _) ⟨p, _⟩)) = _
  simp only [TateAlgebra.quotientOneSubfXToLoc, Ideal.Quotient.lift_mk,
    RingHom.comp_apply]

end CompletionExtension

end ValuationSpectrum
