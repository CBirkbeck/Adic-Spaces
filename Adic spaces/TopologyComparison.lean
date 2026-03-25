/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PresheafIdentification
import «Adic spaces».TateAlgebraWedhorn

/-!
# Topology Comparison: Completion Isomorphism

For a Huber ring `A` with pair of definition `(A₀, I)` and a rational
localization datum `D`, we show that `presheafValue D` (the completion
of `Localization.Away D.s` with the localization topology) is isomorphic
to `A⟨X⟩/(1-sX)` (the Tate algebra quotient).

Both are completions of the same dense ring `Localization.Away D.s`, but
a priori with different topologies. The comparison uses the Artin-Rees
lemma to show the topologies agree on the dense subring.

## Strategy

Rather than comparing topologies directly, we use the universal property
of `UniformSpace.Completion`: both `presheafValue D` and `A⟨X⟩/(1-sX)`
are complete T₂ rings receiving `Localization.Away D.s` as a dense subring.
We construct continuous maps in both directions and show they compose to
the identity.

### Map 1: presheafValue D → A⟨X⟩/(1-sX)
Via `locToQuotientOneSubfX_gen` (from PresheafIdentification.lean),
the localization maps into the quotient. If this map is continuous for
the localization topology on the source and the quotient topology on
the target, it extends to the completion by the universal property.

### Map 2: A⟨X⟩/(1-sX) → presheafValue D
This is `tateQuotientToPresheafHom` (from PresheafIdentification.lean),
which sends `mk(∑ aₙ Xⁿ)` to `∑ canonicalMap(aₙ) · invS^n`.

### Composites
Both composites are the identity on the dense localization subring.
By density + T₂, they are the identity on the whole ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, §8.1, Prop 5.49(3)
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [HasRestrictionMaps A]

section CompletionIsomorphism

/-! ### The presheaf-to-quotient map

For the discrete case, we already have `tateQuotientPresheafEquiv`
which gives the full ring isomorphism. The non-discrete case requires
the topology comparison.

For now, we record that the composition
`Localization.Away s → presheafValue D → A⟨X⟩/(1-sX) → presheafValue D`
is the identity on the dense subring, from which surjectivity follows
by completeness + T₂.
-/

variable [NonarchimedeanRing A]

/-- The composition `tateQuotientToPresheafHom ∘ locToQuotientOneSubfX_gen`
agrees with `locLiftToPresheaf` (both send `a/s^n` to `canonicalMap(a) · invS^n`).
Since `locLiftToPresheaf = coeRingHom` (the dense embedding), this shows
the round-trip through the quotient is the identity on the dense subring. -/
theorem tateQuotient_roundtrip_eq_locLift
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    ((tateQuotientToPresheafHom D hb).comp
      (locToQuotientOneSubfX_gen D.s)) =
    locLiftToPresheaf D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext b
  simp only [RingHom.comp_apply, RingHom.coe_comp]
  rw [locToQuotientOneSubfX_gen_algebraMap,
    tateQuotientToPresheafHom_algebraMap,
    locLiftToPresheaf_algebraMap]

/-- The round-trip sends each localization element to its image
under `locLiftToPresheaf = coeRingHom`. -/
theorem tateQuotient_roundtrip_apply
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (a : Localization.Away D.s) :
    tateQuotientToPresheafHom D hb
      (locToQuotientOneSubfX_gen D.s a) =
    locLiftToPresheaf D a :=
  RingHom.congr_fun (tateQuotient_roundtrip_eq_locLift D hb) a

/-! ### Surjectivity of tateQuotientToPresheafHom

The image of `tateQuotientToPresheafHom` contains the dense localization
subring (by the round-trip lemma). For surjectivity, we need the image
to be all of `presheafValue D`.

The key: construct the inverse map `presheafValue D → A⟨X⟩/(1-sX)` using
`UniformSpace.Completion.extensionHom` applied to `locToQuotientOneSubfX_gen`.
This requires `locToQuotientOneSubfX_gen` to be continuous for the
localization topology on the source.

For now, we prove surjectivity for the DISCRETE case (where everything
simplifies) and record the general strategy.
-/

/-- For discrete A, `tateQuotientToPresheafHom` is surjective. -/
theorem tateQuotientToPresheafHom_surjective_discrete
    [DiscreteTopology A] [IsNoetherianRing A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    Function.Surjective (tateQuotientToPresheafHom D hb) := by
  intro y
  have hbij := coeRingHom_bijective_of_discrete D
  obtain ⟨a, rfl⟩ := hbij.2 y
  refine ⟨locToQuotientOneSubfX_gen D.s a, ?_⟩
  rw [tateQuotient_roundtrip_apply, locLiftToPresheaf_eq_coeRingHom]

/-- For discrete A, the isomorphism `A⟨X⟩/(1-sX) ≃+* presheafValue D`. -/
noncomputable def tateQuotientPresheafEquiv_via_roundtrip
    [DiscreteTopology A] [IsNoetherianRing A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) ≃+* presheafValue D :=
  have hinj : Function.Injective (tateQuotientToPresheafHom D hb) := by
    suffices key : tateQuotientToPresheafHom D hb = quotientEvalPresheafHom D by
      rw [key]; exact quotientEvalPresheafHom_injective D
    apply Ideal.Quotient.ringHom_ext
    ext g
    simp only [tateQuotientToPresheafHom, quotientEvalPresheafHom,
      RingHom.comp_apply, Ideal.Quotient.lift_mk,
      tateEvalPresheafHom, evalPresheafHom]
    sorry -- Need: tsum-based eval = composition-based eval for discrete A
  RingEquiv.ofBijective (tateQuotientToPresheafHom D hb)
    ⟨hinj, tateQuotientToPresheafHom_surjective_discrete D hb⟩

end CompletionIsomorphism

end ValuationSpectrum
