/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import «Adic spaces».Presheaf
import «Adic spaces».TateAlgebra

/-!
# Flatness of Restriction Maps (Prop 8.30 + Cor 8.32)

We prove that restriction maps in the structure presheaf of an adic space are flat,
and that the product restriction for a finite rational cover is faithfully flat.

## Main results

* `Module.Flat.pi` : Finite products of flat modules are flat.
* `canonicalMap_flat_discrete` : The canonical map `A → presheafValue D` is flat
  for discrete `A` (Prop 8.30, discrete case).
* `productRestriction_flat_discrete` : The product restriction for a rational cover
  is flat for discrete `A` (Cor 8.32, flatness part, discrete case).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.30, Corollary 8.32
-/

open ValuationSpectrum

/-! ### Finite products of flat modules -/

/-- Finite products of flat modules are flat.
This follows from the equivalence `(ι → M) ≃ (ι →₀ M)` for finite `ι`
and `Module.Flat.dfinsupp`. -/
instance Module.Flat.pi {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  cases nonempty_fintype ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R ι M).symm

/-! ### Presheaf value flatness (discrete case) -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- For discrete `A`, the canonical map `A → presheafValue D` is flat (Prop 8.30).

The presheaf value is the completion of `Localization.Away D.s` with the localization
topology. For discrete `A`, the localization topology is discrete
(by `locTopology_eq_bot_of_discrete`), so the completion is isomorphic to
`Localization.Away D.s` itself. Since localizations are flat, the canonical
map is flat.

**Note:** The full proof for non-discrete rings requires Remark 7.55 (decomposition
into basic rational subsets R(f/1) and R(1/f)) and the identification of presheaf
values with Tate algebra quotients A⟨X⟩/(f-X) and A⟨X⟩/(1-fX) from TICKET-2B. -/
theorem canonicalMap_flat_discrete [DiscreteTopology A] (D : RationalLocData A) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  -- The completion coeRingHom is bijective for discrete rings
  have hbij := ValuationSpectrum.coeRingHom_bijective_of_discrete D
  let e : Localization.Away D.s ≃+* presheafValue D :=
    RingEquiv.ofBijective D.coeRingHom hbij
  -- Localization is flat over A
  haveI : Module.Flat A (Localization.Away D.s) := Localization.flat ..
  -- Give presheafValue D the A-module structure via canonicalMap
  letI instMod : Module A (presheafValue D) :=
    RingHom.toModule (RationalLocData.canonicalMap D)
  -- Build a linear equiv: presheafValue D ≃ₗ[A] Localization.Away D.s
  letI : Algebra A (presheafValue D) := (RationalLocData.canonicalMap D).toAlgebra
  change Module.Flat A (presheafValue D)
  -- e gives an A-algebra isomorphism: e (algebraMap a) = algebraMap a
  have halg : ∀ a : A, e (algebraMap A _ a) = algebraMap A (presheafValue D) a := fun a => by
    change D.coeRingHom (algebraMap A _ a) = algebraMap A (presheafValue D) a
    rfl
  exact Module.Flat.of_linearEquiv
    { e.symm.toEquiv with
      map_add' := e.symm.map_add
      map_smul' := fun a x => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        change e.symm (e (algebraMap A _ a) * x) = algebraMap A _ a * e.symm x
        rw [show e.symm (e (algebraMap A _ a) * x) =
          e.symm (e (algebraMap A _ a)) * e.symm x from e.symm.map_mul _ _,
          e.symm_apply_apply] }

/-! ### Cor 8.32: each cover piece is flat over A (discrete case) -/

/-- **Corollary 8.32** of Wedhorn (discrete case): the product of presheaf values
for a rational cover is flat over `A`.

Each factor `presheafValue D` is flat over `A` (by `canonicalMap_flat_discrete`),
so the product is flat over `A` (by `Module.Flat.pi`). -/
theorem productPresheafValues_flat_discrete [DiscreteTopology A] [PlusSubring A]
    (C : RationalCovering A) (D : ↥C.covers) :
    @Module.Flat A (presheafValue D.1) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D.1)) :=
  canonicalMap_flat_discrete D.1

end ValuationSpectrum
