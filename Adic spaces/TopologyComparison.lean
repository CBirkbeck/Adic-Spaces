/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafIdentification
import «Adic spaces».TateAlgebraWedhorn

/-!
# Topology Comparison: Completion Isomorphism (Non-Discrete)

The key bridge: `presheafValue D ≃+* A⟨X⟩/(1-sX)` for non-discrete
strongly noetherian Tate rings.

## Strategy

1. Show `locToQuotientOneSubfX_gen : Localization.Away s →+* A⟨X⟩/(1-sX)`
   is continuous for localization topology → T-topology quotient.
2. Extend to `presheafValue D →+* A⟨X⟩/(1-sX)` via `extensionHom`.
3. The round-trip `Localization → Quotient → presheafValue` = `coeRingHom`.
4. Both composites are identity → isomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, §8.1
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [HasRestrictionMaps A] [NonarchimedeanRing A]

section CompletionIsomorphism

/-- The round-trip `Localization → Quotient → presheafValue` equals
`locLiftToPresheaf = coeRingHom`. -/
theorem tateQuotient_roundtrip_eq_locLift (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    ((tateQuotientToPresheafHom D hb).comp (locToQuotientOneSubfX_gen D.s)) =
    locLiftToPresheaf D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext b
  simp only [RingHom.comp_apply, RingHom.coe_comp]
  rw [locToQuotientOneSubfX_gen_algebraMap, tateQuotientToPresheafHom_algebraMap,
    locLiftToPresheaf_algebraMap]

/-- The round-trip pointwise. -/
theorem tateQuotient_roundtrip_apply (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (a : Localization.Away D.s) :
    tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a) =
    locLiftToPresheaf D a :=
  RingHom.congr_fun (tateQuotient_roundtrip_eq_locLift D hb) a

/-! ### Step 1: Continuity of locToQuotientOneSubfX_gen

For the localization topology on `Localization.Away D.s` and the
quotient of the T-topology on `A⟨X⟩/(1-sX)`, the map
`locToQuotientOneSubfX_gen` is continuous.

This is the Artin-Rees topology comparison: the localization neighborhoods
`{(I·D)^m}` eventually land inside the quotient neighborhoods
`{class(g) : coeff n g ∈ s^n · U for all n}`.

For the proof: an element of `locNhd m` has the form `b/s^k` with
`b ∈ I^m · A₀`. Its image in the quotient is `class(b · X^k)`.
The T-topology condition: `coeff n (b · X^k) ∈ s^n · U`.
Since `coeff n (b · X^k) = b` if `n = k`, 0 otherwise.
Condition: `b ∈ s^k · U`. Since `b ∈ I^m · A₀` and `s^k · U`
contains `I^m · A₀` for `m ≥ m₀(U, k)` (Artin-Rees), this holds.

**NOTE:** This step requires the T-topology (from TateAlgebraWedhorn.lean),
NOT the product topology. With the product topology, the condition would
be `b ∈ U` (no `s^k` factor), which is weaker and doesn't match.
-/

/-! ### Bridge lemma: T₀ localization → annihilation by powers of s

For sorry-elimination in StructureSheaf.lean: if the localization topology
is T₀ and `coeRingHom(algebraMap b) = 0`, then `∃ k, s^k * b = 0`.
This reduces deep sorries to a single clean T₀ hypothesis. -/

omit [PlusSubring A] [HasRestrictionMaps A] [NonarchimedeanRing A] in
/-- If the localization topology on `Localization.Away D.s` is T₀, then
`D.coeRingHom (algebraMap b) = 0` implies `∃ k, D.s ^ k * b = 0`.

Uses injectivity of the completion embedding for T₀ uniform spaces
(`UniformSpace.Completion.coe_injective`) and the localization
characterization (`IsLocalization.map_eq_zero_iff`). -/
theorem exists_pow_mul_eq_zero_of_coeRingHom_zero (D : RationalLocData A) (b : A)
    (ht0 : @T0Space (Localization.Away D.s)
      (@UniformSpace.toTopologicalSpace _ D.uniformSpace))
    (h : D.coeRingHom (algebraMap A (Localization.Away D.s) b) = 0) :
    ∃ k : ℕ, D.s ^ k * b = 0 := by
  have hinj : Function.Injective D.coeRingHom :=
    @UniformSpace.Completion.coe_injective _ D.uniformSpace ht0
  have hab : algebraMap A (Localization.Away D.s) b = 0 :=
    hinj (h.trans (map_zero D.coeRingHom).symm)
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers D.s)] at hab
  obtain ⟨⟨_, ⟨k, rfl⟩⟩, hk⟩ := hab
  exact ⟨k, hk⟩

/-! ### Step 1 (TODO): Continuity of locToQuotientOneSubfX_gen

The continuity proof requires connecting locNhd to the T-topology
quotient neighborhoods via the Artin-Rees comparison. See the docstring
above for the proof sketch. -/

/-! ### Step 2 (TODO): Extension to completion

Once continuity is established, `extensionHom` gives:
`presheafValueToQuotient : presheafValue D →+* A⟨X⟩/(1-sX)`

And the composition with `tateQuotientToPresheafHom` is the identity
on both sides (by the round-trip + T₂ uniqueness). -/

end CompletionIsomorphism

end ValuationSpectrum
