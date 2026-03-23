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

end ValuationSpectrum
