/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».GeometricReduction
import «Adic spaces».LaurentOverlapConsumer

/-!
# Final Part-2 assembly: Lane C × Lane A composition

This file bolts the Lane-A caller-ready consumer
(`laurentCover_gluing_presheaf_via_primary`, `LaurentOverlapConsumer.lean`)
onto the Lane-C end-to-end Part-2 theorem
(`RationalCovering.tateAcyclicity_Part2_end_to_end`, `GeometricReduction.lean`)
by threading Lane-A's output through Lane-C's `hLaurentGlue` residual slot.

## The composition

`tateAcyclicity_Part2_end_to_end` takes, among other residuals, the Lane-A
gluing hypothesis

    hLaurentGlue : ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀))
                     (u_minus : presheafValue (laurentMinusDatum C.base f₀))
                     (_hoverlap : ...),
      ∃ x : presheafValue C.base,
        restrictionMap C.base (laurentPlusDatum C.base f₀)
          (laurentPlus_subset C.base f₀) x = u_plus ∧
        restrictionMap C.base (laurentMinusDatum C.base f₀)
          (laurentMinus_subset C.base f₀) x = u_minus

The Lane-A consumer `laurentCover_gluing_presheaf_via_primary` produces
exactly that existential, given Primary's Step-A inputs (the presheaf-level
bivariate iso `τ_preBiv` and the two intertwining compatibilities
`h_plus_compat`, `h_minus_compat`) together with the standard typeclass
preconditions on `(A, P, D₀, f)`. Specializing `D₀ := C.base`, `f := f₀`,
and substituting into `hLaurentGlue` closes the slot.

## The exported theorem

`RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary` replaces
Lane-C's `hLaurentGlue` residual with Lane-A's Primary-facing inputs. All
other residuals (`hE_sep`, `minus_section`, `plus_hV_glue`,
`h_restriction_prop`) remain caller-supplied — they come from Lane B,
minus-side bundle, recursive plus-half IH, and the plus-side outer V-piece
bridge respectively, not from Lane A.

## Residual map (post-composition)

Residuals (post-composition):
* `τ_preBiv` + `h_plus_compat` + `h_minus_compat` — Primary Step-A /
  S-OV-GLUE analytic inputs, out of Lane C.
* `hE_sep` — Lane B (Cor 8.32 /
  `productRestriction_injective_tate_via_prime_extension_closed`); parked.
* `minus_section` — minus-side bundle (needs `hBase_vle_minus`);
  genuine gap documented in `GeometricReduction.lean`.
* `plus_hV_glue` + `h_restriction_prop` — recursive plus-half IH at
  `|S.erase f₀|` + plus-side outer V-piece bridge; standard residuals.
* Consumer preconditions (`hNoeth_B`, `hLocLift_B`, …, `hcont_eval_B`) —
  Primary noetherian/continuity inputs; structural, not new residuals.

The consumer preconditions are **not new residuals**: they are the exact
typeclass/analytic inputs Primary's Lane-A theorem already requires.
Before this file, they lived inside the caller's `hLaurentGlue` discharge;
now they appear directly in the signature.

## Lane-B reminder

This file does NOT discharge `hE_sep` (Lane B / Cor 8.32). If Lane B
separation is later packaged into a Laurent/simple-cover exactness bundle
inside `LaurentOverlap.lean`, swap the `hE_sep` residual here for the
bundle consumer and re-export. Until then, `hE_sep` stays caller-supplied.

## References

* `Adic spaces/GeometricReduction.lean:3657` —
  `RationalCovering.tateAcyclicity_Part2_end_to_end` (Lane C boundary).
* `Adic spaces/LaurentOverlapConsumer.lean:180` —
  `laurentCover_gluing_presheaf_via_primary` (Lane A consumer).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **Final caller-ready Part-2 theorem** for the `T-ACYC-PART2` assembly,
with Lane-A (`hLaurentGlue`) discharged via Primary's Step-A inputs.

Composes `RationalCovering.tateAcyclicity_Part2_end_to_end`
(`GeometricReduction.lean:3657`) with
`laurentCover_gluing_presheaf_via_primary`
(`LaurentOverlapConsumer.lean:180`), removing `hLaurentGlue` from the
caller's direct residual list and replacing it with Primary's
`τ_preBiv` + two intertwinings + consumer typeclass preconditions.

**Residuals** (caller-supplied): `τ_preBiv` + `h_plus_compat` +
`h_minus_compat` (Lane A / Primary Step-A), `hE_sep` (Lane B),
`minus_section` (minus-side bundle), `plus_hV_glue` + `h_restriction_prop`
(recursive plus-half IH + outer V-piece bridge). No Lane-A gluing slot
remains; see module docblock for the residual map. -/
theorem RationalCovering.tateAcyclicity_Part2_end_to_end_via_primary
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (S : Finset A) (f₀ : A)
    (hf₀ : f₀ ∈ S) (hSnonempty : S.Nonempty)
    (hAplus : ∀ f ∈ S, f ∈ A⁺)
    (hBase_vle :
      ∀ f ∈ S, ∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s)
    (hS_contain : refines_contain C S) (hS_cover : refines_cover C S)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (plus_hV_glue : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (fV_plus : ∀ D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
          S f₀ hS_cover).standardCoverVCovers (S.erase f₀) },
          presheafValue D'.1),
        (∀ (D₁' D₂' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (D₃ : RationalLocData A)
          (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁'.1.T D₁'.1.s)
          (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂'.1.T D₂'.1.s),
          restrictionMap D₁'.1 D₃ h₃₁ (fV_plus D₁') =
            restrictionMap D₂'.1 D₃ h₃₂ (fV_plus D₂')) →
        ∃ u_plus : presheafValue (laurentPlusDatum C.base f₀),
          ∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
              S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
            (hD' : rationalOpen D'.1.T D'.1.s ⊆
              rationalOpen (laurentPlusDatum C.base f₀).T
                           (laurentPlusDatum C.base f₀).s),
            restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus = fV_plus D')
    (h_restriction_prop : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (_hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (u_plus : presheafValue (laurentPlusDatum C.base f₀)),
        (∀ (D' : { D' // D' ∈ (C.plusLaurentCovering_of_standardCoverVCovers
            S f₀ hS_cover).standardCoverVCovers (S.erase f₀) })
          (hD' : rationalOpen D'.1.T D'.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D'.1 hD' u_plus =
            (let h_exists :=
               ((C.plusLaurentCovering_of_standardCoverVCovers S f₀
                   hS_cover).mem_standardCoverVCovers (S.erase f₀)).mp D'.2
             let g := Classical.choose h_exists
             let hg_spec := Classical.choose_spec h_exists
             hg_spec.2 ▸ C.plusHalf_fV_transport_at_g S f₀ g hg_spec.1 fV)) →
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_plus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentPlusDatum C.base f₀).T
                         (laurentPlusDatum C.base f₀).s),
          restrictionMap (laurentPlusDatum C.base f₀) D.1 hD_plus u_plus = fV D)
    (minus_section : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      { u_minus : presheafValue (laurentMinusDatum C.base f₀) //
        ∀ (D : { D // D ∈ C.standardCoverVCovers S })
          (hD_minus : rationalOpen D.1.T D.1.s ⊆
            rationalOpen (laurentMinusDatum C.base f₀).T
                         (laurentMinusDatum C.base f₀).s),
          restrictionMap (laurentMinusDatum C.base f₀) D.1 hD_minus u_minus = fV D })
    (hrefine : ∀ D : { D // D ∈ C.standardCoverVCovers S },
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s) ∨
      (rationalOpen D.1.T D.1.s ⊆
        rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s))
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : HasLocLiftPowerBounded (presheafValue C.base) := hLocLift_B
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue C.base) :=
        presheafValue_pairOfDefinition_concrete P C.base
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue C.base) (C.base.canonicalMap f₀))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue C.base) P_B (C.base.canonicalMap f₀))))
        (example638Plus_forwardHom (presheafValue C.base) P_B (C.base.canonicalMap f₀)))
    (hcont_eval_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      let D : RationalLocData (presheafValue C.base) := iteratedMinusDatum_B P C.base f₀
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
      (↥(TateAlgebra₂ (presheafValue C.base)) ⧸
        TateAlgebra.bivariateOverlapIdeal (C.base.canonicalMap f₀)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentPlusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_plus C.base f₀) uplus)) =
        LaurentCover.posLift (C.base.canonicalMap f₀)
          (laurentPlusBridge P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum C.base f₀),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue C.base) (C.base.canonicalMap f₀))
          (τ_preBiv (restrictionMap (laurentMinusDatum C.base f₀)
              (laurentOverlapDatum C.base f₀)
              (laurentOverlap_subset_minus C.base f₀) uminus)) =
        LaurentCover.negLift (C.base.canonicalMap f₀)
          (laurentMinusBridge P C.base f₀ hnoeth_B hcont_eval_B uminus))
    (hoverlap_body : ∀ (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S },
        presheafValue D.1)
      (hV_compat : ∀ (D₁ D₂ : { D // D ∈ C.standardCoverVCovers S })
        (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)),
      ∀ (D₃ : RationalLocData A)
        (h₃p : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s)
        (h₃m : rationalOpen D₃.T D₃.s ⊆
          rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s),
        restrictionMap (laurentPlusDatum C.base f₀) D₃ h₃p
            (C.plus_section_of_plus_hV_glue_auto S f₀ hS_cover fV hV_compat
              (plus_hV_glue fV hV_compat) (h_restriction_prop fV hV_compat)).1 =
          restrictionMap (laurentMinusDatum C.base f₀) D₃ h₃m
            (minus_section fV hV_compat).1)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ C.standardCoverVCovers S })
         (hd : C.standardCoverTau S hS_contain d = E),
        restrictionMap E.1 d.1 (hd ▸ C.standardCoverTau_subset S hS_contain d) a =
          restrictionMap E.1 d.1
            (hd ▸ C.standardCoverTau_subset S hS_contain d) b) →
        a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  C.tateAcyclicity_Part2_end_to_end S f₀ hf₀ hSnonempty
    hAplus hBase_vle hS_contain hS_cover fC hC_compat
    plus_hV_glue h_restriction_prop minus_section hrefine
    (fun u_plus u_minus hoverlap =>
      laurentCover_gluing_presheaf_via_primary
        P C.base f₀ hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
        hnoeth_B hcont_forward_B hcont_eval_B
        τ_preBiv h_plus_compat h_minus_compat
        (laurentPlus_subset C.base f₀) (laurentMinus_subset C.base f₀)
        u_plus u_minus hoverlap)
    hoverlap_body hE_sep

end ValuationSpectrum
