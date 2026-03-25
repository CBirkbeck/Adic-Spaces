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

/-- The image of `locSubring` under `locToQuotientOneSubfX_gen D.s` is bounded
in the quotient T-topology: for any neighborhood V of 0, there exists a
neighborhood U of 0 such that `φ(locSubring) * U ⊆ V`.

This follows from `A₀` being bounded in `A` (Wedhorn Corollary 6.4(2)),
`mk ∘ algebraMap` being continuous, and `locSubring` being generated by
`algebraMap(A₀)` and finitely many elements. -/
theorem locToQuotientOneSubfX_gen_locSubring_isBounded (D : RationalLocData A)
    [T2Space A] :
    @TopologicalRing.IsBounded (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      _ (quotientTTopology D.s)
      (locToQuotientOneSubfX_gen D.s '' (locSubring D.P D.T D.s :
        Set (Localization.Away D.s))) := by
  -- PROOF OUTLINE (self-preserving T-topology neighborhood):
  --
  -- For each tᵢ ∈ D.T, since A₀ is open and x ↦ D.s · tᵢ · x is continuous,
  -- ∃ Cᵢ : ℕ such that D.s · tᵢ · Im(I^{k+Cᵢ}) ⊆ Im(I^k) for all k ≥ 0.
  -- Let C = max(Cᵢ : tᵢ ∈ D.T).
  --
  -- Given target U ∈ nhds 0 (quotient T-topology), find M, N₀ such that
  -- the T-topology open additive subgroup
  --   W_T := {g ∈ A⟨X⟩ : ∀ n ≤ M, s^n · coeff_n(g) ∈ Im(I^{N₀ - n·C})}
  -- satisfies mk(W_T) ⊆ U.
  --
  -- Self-preservation (Subring.closure_induction with P(r) = φ(r)·mk(W_T) ⊆ mk(W_T)):
  -- - algebraMap(a₀), a₀ ∈ A₀: algebraMap(a₀)·g has s^n·coeff_n = a₀·(s^n·coeff_n(g)).
  --   Since a₀ ∈ A₀ and I^k is an ideal of A₀: a₀ · Im(I^k) ⊆ Im(I^k). ✓
  -- - tᵢ/s: φ(tᵢ/s)·mk(g) = mk(algebraMap(tᵢ)·X·g). Scaled coeff at n:
  --   s^n·coeff_n(algebraMap(tᵢ)·X·g) = s·tᵢ·(s^{n-1}·coeff_{n-1}(g)).
  --   Source: s^{n-1}·coeff_{n-1}(g) ∈ Im(I^{N₀-(n-1)·C}).
  --   Need: s·tᵢ · Im(I^{N₀-(n-1)·C}) ⊆ Im(I^{N₀-n·C}).
  --   Write N₀-(n-1)·C = (N₀-n·C) + C ≥ (N₀-n·C) + Cᵢ.
  --   By choice of Cᵢ: s·tᵢ · Im(I^{(N₀-n·C)+Cᵢ}) ⊆ Im(I^{N₀-n·C}). ✓
  -- - mul: P(r₁)∧P(r₂) → P(r₁·r₂) since r₁·(r₂·W) ⊆ r₁·W ⊆ W. ✓
  -- - add/neg/0/1: standard from additive subgroup properties.
  --
  -- Then V = mk(W_T), and φ(locSubring) · V ⊆ V ⊆ U. V ∈ nhds 0 since
  -- W_T is a T-topology open set (finitely many coordinates constrained to
  -- open sets Im(I^k)), and mk is an open map.
  --
  -- TODO: Formalize the T-topology neighborhood construction and the
  -- coefficient-level analysis. Requires:
  -- (1) The "Artin-Rees shift" Cᵢ for each tᵢ (from continuity of multiplication
  --     by s·tᵢ and openness of A₀).
  -- (2) Explicit T-topology open additive subgroup with graded constraints.
  -- (3) Subring.closure_induction at the quotient level.
  sorry

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
  -- Set up instances for the source and target topologies.
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away D.s) := D.isTopologicalAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  haveI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    @IsTopologicalRing.to_topologicalAddGroup _ _
      (quotientTTopology D.s) (quotientTTopology_isTopologicalRing D.s)
  -- Step 1: Reduce to continuity at 0 using additive group structure.
  apply continuous_of_continuousAt_zero (locToQuotientOneSubfX_gen D.s)
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro S hS
  -- Step 2: Get a basis neighborhood from the localization topology.
  have hbasis := locBasis D.P D.T D.s D.hopen
  let hb := hbasis.toRingFilterBasis.toAddGroupFilterBasis
  -- Step 3: The target neighborhood S contains an open additive subgroup.
  -- Use the nonarchimedean property of the quotient.
  haveI : NonarchimedeanRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_nonarchimedean D.s
  obtain ⟨W, hWS⟩ := NonarchimedeanRing.is_nonarchimedean S hS
  -- Step 4: It suffices to show locToQuotientOneSubfX_gen maps some
  -- locNhd n into W.
  suffices ∃ n, ∀ x ∈ locNhd D.P D.T D.s n,
      locToQuotientOneSubfX_gen D.s x ∈ (W : Set _) by
    obtain ⟨n, hn⟩ := this
    apply Filter.mem_of_superset
      (hb.nhds_zero_hasBasis.mem_iff.mpr
        ⟨locNhd D.P D.T D.s n, ⟨n, rfl⟩, le_refl _⟩)
    intro x hx
    exact hWS (hn x hx)
  -- Step 5: Use boundedness of φ(locSubring) in the quotient.
  -- By locToQuotientOneSubfX_gen_locSubring_isBounded, there exists
  -- U ∈ nhds 0 (quotient) with φ(locSubring) * U ⊆ W.
  have hW_nhds : (W : Set _) ∈ @nhds _ τQ 0 :=
    W.isOpen.mem_nhds (W.zero_mem)
  obtain ⟨U, hU, hbdd⟩ :=
    locToQuotientOneSubfX_gen_locSubring_isBounded D (W : Set _) hW_nhds
  -- Step 6: Use continuity of mk ∘ algebraMap to find m such that
  -- mk(algebraMap(I^m)) ⊆ U.
  have hmk_alg_cont : @Continuous A _ _ τQ
      ((Ideal.Quotient.mk (oneSubfXIdeal D.s)).comp
        (algebraMap A ↥(TateAlgebra A))) := by
    letI : TopologicalSpace ↥(TateAlgebra A) :=
      TateAlgebraWedhorn.tateTopologyT D.s
    exact continuous_quotient_mk'.comp
      (TateAlgebraWedhorn.tateTopologyT_continuous_algebraMap D.s)
  have hφ_alg : ∀ (a : A),
      locToQuotientOneSubfX_gen D.s (algebraMap A _ a) =
        (Ideal.Quotient.mk (oneSubfXIdeal D.s))
          (algebraMap A ↥(TateAlgebra A) a) :=
    locToQuotientOneSubfX_gen_algebraMap D.s
  have h_pre_U : ((Ideal.Quotient.mk (oneSubfXIdeal D.s)).comp
      (algebraMap A ↥(TateAlgebra A))) ⁻¹' U ∈ nhds (0 : A) := by
    exact hmk_alg_cont.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨m, -, hm⟩ := D.P.hasBasis_nhds_zero.mem_iff.mp h_pre_U
  -- hm: for b ∈ Subtype.val '' (I^m : Set D.P.A₀), mk(algebraMap(b)) ∈ U.
  -- Step 7: Show locNhd(m) maps into W.
  -- We use Submodule.span_induction with the STRENGTHENED predicate:
  -- P(d) = "for all r ∈ locSubring, φ(subtype(r * d)) ∈ W".
  -- This handles the scalar case because r * (s * d) = (r * s) * d.
  -- Then P(d) with r = 1 gives φ(subtype(d)) ∈ W.
  refine ⟨m, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  rw [locIdeal, ← Ideal.map_pow] at hd
  -- d ∈ Ideal.map algebraMapD (I^m). Use span_induction with
  -- strengthened predicate.
  suffices ∀ (r : locSubring D.P D.T D.s),
      locToQuotientOneSubfX_gen D.s
        ((locSubring D.P D.T D.s).subtype (r * d)) ∈ (W : Set _) by
    specialize this 1; simp [one_mul] at this; exact this
  intro r₀
  revert r₀
  refine Submodule.span_induction (p := fun d _ ↦
      ∀ (r : locSubring D.P D.T D.s),
        locToQuotientOneSubfX_gen D.s
          ((locSubring D.P D.T D.s).subtype (r * d)) ∈
            (W : Set _)) ?_ ?_ ?_ ?_ hd
  · -- Generator: d = algebraMapD(b) for b ∈ I^m.
    rintro d ⟨b, hb, rfl⟩ r
    -- subtype(r * algebraMapD(b)) = subtype(r) * algebraMap(b.val).
    show locToQuotientOneSubfX_gen D.s
      ((locSubring D.P D.T D.s).subtype r *
        algebraMap A (Localization.Away D.s) ↑b) ∈ _
    rw [map_mul, locToQuotientOneSubfX_gen_algebraMap]
    -- φ(subtype(r)) * mk(algebraMap(b.val)) ∈ φ(locSubring) * U ⊆ W.
    apply hbdd
    refine Set.mul_mem_mul ?_ (hm ⟨b, hb, rfl⟩)
    exact Set.mem_image_of_mem _ r.property
  · -- Zero
    intro r; simp [mul_zero, map_zero]
  · -- Addition: d₁ + d₂
    intro d₁ d₂ _ _ h₁ h₂ r
    have : (locSubring D.P D.T D.s).subtype (r * (d₁ + d₂)) =
        (locSubring D.P D.T D.s).subtype (r * d₁) +
        (locSubring D.P D.T D.s).subtype (r * d₂) := by
      simp [mul_add]
    rw [this, map_add]
    exact W.toAddSubgroup.add_mem (h₁ r) (h₂ r)
  · -- Scalar: s • d for s ∈ locSubring.
    intro s d _ hd r
    -- r * (s • d) = (r * s) * d, where • is the module action.
    have : (locSubring D.P D.T D.s).subtype (r * (s • d)) =
        (locSubring D.P D.T D.s).subtype ((r * s) * d) := by
      simp [mul_assoc]
    rw [this]
    exact hd (r * s)

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
  -- Setup instances for the quotient T-topology and localization.
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI τQ : TopologicalSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology D.s
  letI : UniformSpace (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTUniformSpace D.s
  letI : IsTopologicalRing (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalRing D.s
  letI : IsTopologicalAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isTopologicalAddGroup D.s
  letI : IsUniformAddGroup (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    quotientTTopology_isUniformAddGroup D.s
  -- T₀ uniform space is T₂ (uniform → regular → R1, and R1 + T₀ → T₂).
  haveI hT2 : @T2Space _ τQ := by
    haveI : @RegularSpace _ τQ :=
      @UniformSpace.to_regularSpace _ (quotientTUniformSpace D.s)
    exact inferInstance
  -- The composites agree on the dense image of locToQuotientOneSubfX_gen:
  -- presheafValueToQuotient(tateQuotientToPresheafHom(locToQuotientOneSubfX_gen a))
  -- = presheafValueToQuotient(coeRingHom a)     [round-trip]
  -- = locToQuotientOneSubfX_gen a               [extensionHom_coe]
  have hagree : ∀ (a : Localization.Away D.s),
      presheafValueToQuotient D hb hcs ht0
        (tateQuotientToPresheafHom D hb (locToQuotientOneSubfX_gen D.s a)) =
        locToQuotientOneSubfX_gen D.s a := by
    intro a
    rw [tateQuotient_roundtrip_apply D hb a,
      locLiftToPresheaf_eq_coeRingHom D,
      presheafValueToQuotient_coe D hb hcs ht0 a]
  -- KEY SORRY: Density of locToQuotientOneSubfX_gen + continuity of composite
  -- → DenseRange.equalizer closes this goal.
  --
  -- Density holds because: the T-topology on TateAlgebra A is induced from the
  -- product topology via scaleIncl. Truncations of any power series g converge
  -- to g coordinate-wise under scaleIncl, hence in the T-topology. Since the
  -- quotient map mk is continuous, mk(truncations) converge in the quotient.
  -- Each mk(truncation) is in the image of locToQuotientOneSubfX_gen.
  --
  -- Continuity of the composite requires showing tateQuotientToPresheafHom
  -- (= Ideal.Quotient.lift of evalHomBounded) is continuous from quotient
  -- T-topology to presheafValue D. This follows from continuity of
  -- evalHomBounded in the T-topology (the tsum converges by construction).
  --
  -- Both density and continuity need ~50-100 lines of new infrastructure
  -- (truncation convergence for T-topology, T-topology continuity of evaluation).
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
