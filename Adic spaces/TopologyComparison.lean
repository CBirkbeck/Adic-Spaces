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

omit [PlusSubring A] [HasRestrictionMaps A] in
/-- The round-trip `Localization → Quotient → presheafValue` equals
`locLiftToPresheaf = coeRingHom`. -/
theorem tateQuotient_roundtrip_eq_locLift (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D)) :
    ((tateQuotientToPresheafHom D hb).comp (locToQuotientOneSubfX_gen D.s)) =
    locLiftToPresheaf D := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
  ext b
  simp only [RingHom.comp_apply]
  rw [locToQuotientOneSubfX_gen_algebraMap, tateQuotientToPresheafHom_algebraMap,
    locLiftToPresheaf_algebraMap]

omit [PlusSubring A] [HasRestrictionMaps A] in
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

/-! ### Step 1: Quotient T-topology on A⟨X⟩/(1-sX)

The quotient of the T-topology on `A⟨X⟩` by the ideal `(1-sX)` gives a
topological ring structure on `A⟨X⟩/(1-sX)`. This is the correct topology
for the comparison with the localization topology: the T-topology scales
coefficients by powers of `s`, matching the denominator structure in the
localization. -/

/-- Quotient T-topology on `A⟨X⟩/(1-sX)`: the quotient of `tateTopologyT f`
by the ideal `(1-fX)`. This is the topology used for the comparison with
the localization topology on `Localization.Away f` (Wedhorn, §5.48). -/
@[reducible]
noncomputable def quotientTTopology (f : A) :
    TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @topologicalRingQuotientTopology _ (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f)

/-- The quotient of the T-topology is a topological ring
(from Mathlib's `topologicalRing_quotient`, applied with the T-topology). -/
noncomputable instance quotientTTopology_isTopologicalRing (f : A) :
    @IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @topologicalRing_quotient ↥(TateAlgebra A)
    (TateAlgebraWedhorn.tateTopologyT f) _
    (oneSubfXIdeal f) (TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f)

/-- The quotient T-topology on `A⟨X⟩/(1-fX)` is nonarchimedean:
inherited from the nonarchimedean T-topology on `A⟨X⟩` via the
quotient map (which is continuous and open). -/
noncomputable instance quotientTTopology_nonarchimedean (f : A) :
    @NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      _ (quotientTTopology f) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := TateAlgebraWedhorn.tateTopologyT f
  haveI : IsTopologicalRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_isTopologicalRing f
  haveI : NonarchimedeanRing ↥(TateAlgebra A) :=
    TateAlgebraWedhorn.tateTopologyT_nonarchimedean f
  constructor
  intro U hU
  -- The preimage of U in A⟨X⟩ is a neighborhood of 0.
  have hcont : @Continuous _ _ (TateAlgebraWedhorn.tateTopologyT f)
      (quotientTTopology f) (Ideal.Quotient.mk (oneSubfXIdeal f)) :=
    continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk (oneSubfXIdeal f)) ⁻¹' (U : Set _) ∈
      nhds (0 : ↥(TateAlgebra A)) :=
    hcont.continuousAt.preimage_mem_nhds hU
  -- Find an open additive subgroup V inside the preimage.
  obtain ⟨V, hVU⟩ := NonarchimedeanRing.is_nonarchimedean _ hU'
  -- Push V forward via the quotient map.
  refine ⟨{
    toAddSubgroup := V.toAddSubgroup.map
      (Ideal.Quotient.mk (oneSubfXIdeal f)).toAddMonoidHom
    isOpen' := QuotientRing.isOpenMap_coe _ _ V.isOpen
  }, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact hVU hy

/-! ### Step 1b: Continuity of locToQuotientOneSubfX_gen

The continuity proof requires connecting `locNhd` to the T-topology
quotient neighborhoods via the Artin-Rees comparison. The key insight:
an element of `locNhd m` has the form `b/s^k` with `b ∈ I^m * A₀`.
Its image in the quotient is `class(algebraMap(b) * X^k)`.
The T-topology via `scaleIncl` requires `s^n * coeff_n(g) ∈ U` for all `n`.
For `g = algebraMap(b) * X^k`, the only nonzero coefficient is at `n = k`,
giving `s^k * b ∈ U`. Since `b ∈ I^m` and the topology on `A` is nonarchimedean,
`s^k * I^m ⊆ U` for `m` large enough (continuity of scalar multiplication). -/

/-- The map `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology on `Localization.Away D.s` to the quotient T-topology on
`A⟨X⟩/(1-sX)`.

**Proof sketch (Wedhorn §8.1):** The localization neighborhoods `locNhd(n)`
map into quotient T-topology neighborhoods because elements `b/s^k` with
`b ∈ I^n` get sent to `class(algebraMap(b) * X^k)` whose scaled coefficients
`s^k * b ∈ s^k * I^n` lie in any target neighborhood for `n` sufficiently large.

This is the key continuity result bridging the localization topology with
the T-topology, enabling the completion extension. -/
theorem locToQuotientOneSubfX_gen_continuous (D : RationalLocData A)
    [T2Space A] :
    @Continuous _ _ D.topology (quotientTTopology D.s)
      (locToQuotientOneSubfX_gen D.s) := by
  sorry

/-! ### Step 2: Extension to completion via extensionHom

Once continuity is established, `UniformSpace.Completion.extensionHom`
extends `locToQuotientOneSubfX_gen` to the completion, giving:
`presheafValueToQuotient : presheafValue D →+* A⟨X⟩/(1-sX)` -/

/-- The `IsTopologicalAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isTopologicalAddGroup (f : A) :
    @IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTTopology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalRing f)

/-- The `UniformSpace` on the quotient T-topology. -/
@[reducible]
noncomputable def quotientTUniformSpace (f : A) :
    UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientTTopology f) (quotientTTopology_isTopologicalAddGroup f)

/-- The `IsUniformAddGroup` instance for the quotient T-topology. -/
noncomputable instance quotientTTopology_isUniformAddGroup (f : A) :
    @IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal f)
      (quotientTUniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (quotientTTopology f)
    (quotientTTopology_isTopologicalAddGroup f)

/-- The ring homomorphism `presheafValue D →+* A⟨X⟩/(1-sX)` extending
`locToQuotientOneSubfX_gen` to the completion.

Given that `locToQuotientOneSubfX_gen D.s` is continuous from the localization
topology to the quotient T-topology, `UniformSpace.Completion.extensionHom`
extends it to a ring homomorphism from the completion `presheafValue D`
to `A⟨X⟩/(1-sX)` (Wedhorn, Proposition 8.30).

The hypotheses `hcs` (completeness) and `ht0` (T0) on the quotient with the
T-topology hold for strongly noetherian Tate rings (Wedhorn Theorem 6.37). -/
noncomputable def presheafValueToQuotient (D : RationalLocData A)
    [T2Space A]
    (_hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s)) :
    presheafValue D →+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0

/-- `presheafValueToQuotient` on the dense image agrees with
`locToQuotientOneSubfX_gen`. -/
theorem presheafValueToQuotient_coe (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (a : Localization.Away D.s) :
    presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a) =
      locToQuotientOneSubfX_gen D.s a := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientTUniformSpace D.s) _ (quotientTTopology_isUniformAddGroup D.s)
    (quotientTTopology_isTopologicalRing D.s)
    (locToQuotientOneSubfX_gen D.s)
    (locToQuotientOneSubfX_gen_continuous D) hcs ht0 a

/-! ### Step 3: The round-trip composites are identity

Using the round-trip lemma `tateQuotient_roundtrip_eq_locLift` (already proved)
and T2 uniqueness of continuous extensions, we show both composites are identity. -/

/-- The composite `tateQuotientToPresheafHom ∘ presheafValueToQuotient` is the
identity on `presheafValue D`.

On the dense image `coeRingHom(a)`:
  `tateQuotientToPresheafHom (presheafValueToQuotient (coeRingHom a))`
  `= tateQuotientToPresheafHom (locToQuotientOneSubfX_gen a)`
  `= locLiftToPresheaf a`   (by round-trip)
  `= coeRingHom a`          (by `locLiftToPresheaf_eq_coeRingHom`)

By T2 density, this extends to all of `presheafValue D`. -/
theorem tateQuotientToPresheaf_comp_presheafToQuotient (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (x : presheafValue D) :
    tateQuotientToPresheafHom D hb
      (presheafValueToQuotient D hb hcs ht0 x) = x := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  -- Use T2 density: the composite and id agree on the dense image.
  refine @UniformSpace.Completion.ext' _ D.uniformSpace
    (presheafValue D) _ _ _ _
    (hcont_eval.comp UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  -- On the dense image: show agreement pointwise.
  intro a
  simp only [Function.comp, id]
  change tateQuotientToPresheafHom D hb
    (presheafValueToQuotient D hb hcs ht0 (D.coeRingHom a)) = D.coeRingHom a
  rw [presheafValueToQuotient_coe D hb hcs ht0 a,
    tateQuotient_roundtrip_apply D hb a,
    locLiftToPresheaf_eq_coeRingHom D]

/-- The composite `presheafValueToQuotient ∘ tateQuotientToPresheafHom` is the
identity on `A⟨X⟩/(1-sX)`.

For `q = mk(g)` in the quotient:
  `presheafValueToQuotient (tateQuotientToPresheafHom (mk g))`
  `= presheafValueToQuotient (∑ canonicalMap(aₙ) · (invS)ⁿ)`

This requires showing the evaluation is the inverse of the localization map
on the quotient. By the universal property, it suffices to check on generators:
  - `mk(algebraMap a) ↦ canonicalMap a ↦ mk(algebraMap a)`
  - `mk(X) ↦ invS ↦ mk(X)`

The full proof uses density of the localization image in `presheafValue D`
and the round-trip on generators. -/
theorem presheafToQuotient_comp_tateQuotientToPresheaf (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (q : ↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :
    presheafValueToQuotient D hb hcs ht0
      (tateQuotientToPresheafHom D hb q) = q := by
  sorry

/-! ### Step 4: Package as RingEquiv -/

/-- **The completion isomorphism** `presheafValue D ≃+* A⟨X⟩/(1-sX)`
(Wedhorn Proposition 8.30, Remark 7.55).

For a strongly noetherian Tate ring `A` and rational localization datum `D`,
the presheaf value (completion of `Localization.Away D.s`) is ring-isomorphic
to the Tate algebra quotient `A⟨X⟩/(1-sX)` equipped with the T-topology.

Both composites are identity:
- `tateQuotientToPresheafHom ∘ presheafValueToQuotient = id` (by T2 density)
- `presheafValueToQuotient ∘ tateQuotientToPresheafHom = id` (by round-trip on generators) -/
noncomputable def presheafValueTateQuotientEquiv (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb)) :
    presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) where
  toFun := presheafValueToQuotient D hb hcs ht0
  invFun := tateQuotientToPresheafHom D hb
  left_inv := tateQuotientToPresheaf_comp_presheafToQuotient D hb hcs ht0 hcont_eval
  right_inv := presheafToQuotient_comp_tateQuotientToPresheaf D hb hcs ht0
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism sends `canonicalMap(a)` to `mk(algebraMap a)`. -/
theorem presheafValueTateQuotientEquiv_canonicalMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (a : A) :
    presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval (D.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  change presheafValueToQuotient D hb hcs ht0
    (D.coeRingHom (algebraMap A _ a)) = _
  rw [presheafValueToQuotient_coe, locToQuotientOneSubfX_gen_algebraMap]

/-- The inverse sends `mk(algebraMap a)` back to `canonicalMap(a)`. -/
theorem presheafValueTateQuotientEquiv_symm_algebraMap (D : RationalLocData A)
    [T2Space A]
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont_eval : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (a : A) :
    (presheafValueTateQuotientEquiv D hb hcs ht0 hcont_eval).symm
      ((Ideal.Quotient.mk _) (algebraMap A _ a)) =
      D.canonicalMap a := by
  simp only [presheafValueTateQuotientEquiv, RingEquiv.symm_mk,
    RingEquiv.coe_mk, Equiv.coe_fn_mk]
  exact tateQuotientToPresheafHom_algebraMap D hb a

end CompletionIsomorphism

end ValuationSpectrum
