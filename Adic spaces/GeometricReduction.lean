/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement
import «Adic spaces».RationalRefinement
import «Adic spaces».StandardCover

/-!
# Geometric reduction: from Laurent-cover acyclicity to arbitrary-cover acyclicity

This file implements the **geometric-reduction front** (ticket T-GEOM-RED)
of the `tateAcyclicity` closure plan. Its role: given exactness on every
simple Laurent cover (provided by `laurentCover_gluing_presheaf`, modulo
`laurentOverlapBridge_exists_compatible` = T-OV-1), produce exactness on
arbitrary finite rational covers.

This corresponds to **Hübner's Lemma 3.8** (arXiv 2405.06435): a pair is
sheafy and acyclic iff exactness holds for every simple Laurent covering
of every rational open. The reverse direction (assumed here) is the
content of this file.

## Key deliverables

* `tateAcyclicity_gluing_via_refinement_cover_level` — a corrected variant
  of the earlier `tateAcyclicity_gluing_via_refinement`. The earlier
  version invoked `restrictionMapHom_injective` (single-map), which is
  **false in general** per the 2026-04-18 reviewer counterexample
  (`A = k⟨T,U⟩/(TU)`, `U = R(1/T)`: the class of `U ∈ A` maps to `0` in
  `𝒪_X(U) ≅ A⟨X⟩/(1-TX)` via `U = U·(TX) = (UT)·X = 0`). The corrected
  variant takes the proper cover-level local-separation hypothesis
  `hE_sep` from `gluing_of_finer_rational`.

* (roadmap, not yet proved) Laurent-cover induction on standard-cover
  size: from `laurentCover_gluing_presheaf` applied pointwise, build
  `hV_glue` for the standard-cover refinement, and thereby close
  `tateAcyclicity` Part 2 modulo T-OV-1 and T-IDEAL-2 (local hE_sep).

## References

* [Hübner, *Adic spaces* (arXiv 2405.06435), Lemma 3.7, Lemma 3.8]
* [T. Wedhorn, *Adic Spaces* (2019 lecture notes), Lemma 8.33, Lemma 8.34]
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **Cover-level variant of `tateAcyclicity_gluing_via_refinement`**
(corrected 2026-04-18 per reviewer guidance).

The earlier `tateAcyclicity_gluing_via_refinement`
(`LaurentRefinement.lean:3605`) invoked `restrictionMapHom_injective`
at line 3638 to discharge the local-separation step. Reviewer
counterexample: `A = k⟨T,U⟩/(TU)`, `U = R(1/T)`; then
`𝒪_X(U) ≅ A⟨X⟩/(1-TX)`, and the class of `U ∈ A` maps to
`U = U·(TX) = (UT)·X = 0`, killing a nonzero element. So individual
restriction maps are **not injective in general**, and the earlier
theorem is unsound outside settings where single-map injectivity
happens to hold.

This variant replaces the illegal `hτ_surj + single-map-injectivity`
step with the correct cover-level hypothesis `hE_sep` from
`gluing_of_finer_rational`: for each `E ∈ C.covers`, separation on
`presheafValue E.1` via the restriction maps to those V-pieces `d`
with `τ d = E`.

**Discharging `hE_sep`**. The hypothesis `hE_sep` holds when, for
each `E`, the V-pieces refining `E` form a sub-covering of `E` and the
associated product-restriction map
`presheafValue E.1 → ∏_{d refining E} presheafValue d.1` is injective.
In the Wedhorn Cor 8.32 framework this is faithful flatness at the
`E`-level sub-cover, which reduces to `coeRingHom_preserves_proper`
(ticket T-IDEAL-2) applied at `E` rather than at `C.base`.

**Relationship to the unsound earlier theorem**. The earlier variant
is strictly stronger *only* when single-map injectivity holds (which
the reviewer counterexample shows is not a theorem). This corrected
variant is logically stronger in the correct direction: it no longer
assumes a false statement. -/
theorem tateAcyclicity_gluing_via_refinement_cover_level
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue : ∀ (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ V_covers }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ V_covers },
        restrictionMap C.base D.1 (hV_subset D.1 D.2) x = fV D)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ V_covers }) (hd : τ d = E),
        restrictionMap E.1 d.1 (hd ▸ hτ d) a =
          restrictionMap E.1 d.1 (hd ▸ hτ d) b) → a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  gluing_of_finer_rational C V_covers hV_subset τ hτ fC hC_compat hV_glue hE_sep

/-! ### Bridge from `refines_by_standard_cover` to the V_covers data

A `StandardCover A` produced by `refines_by_standard_cover` gives
`S.elts : Finset A` with span-top plus two existence clauses (covering
the base, containment in `C.covers`). To feed this into
`tateAcyclicity_gluing_via_refinement_cover_level` we need to convert
it into a `V_covers : Finset (RationalLocData A)` together with its
refinement map `τ`.

The plus-piece at each `f ∈ S.elts` is represented by `laurentPlusDatum
C.base f : RationalLocData A`, whose rational open equals
`rationalOpen (insert f C.base.T) C.base.s` by definitional unfold.
The helpers below package this construction.  -/

/-- The plus-piece rational data for an element `f` relative to a
rational covering `C`: exactly `laurentPlusDatum C.base f`. Its
`rationalOpen` equals `rationalOpen (insert f C.base.T) C.base.s`.
Introduced as an `abbrev` so projections (`.T`, `.s`) reduce transparently. -/
noncomputable abbrev RationalCovering.plusDatum (C : RationalCovering A)
    (f : A) : RationalLocData A :=
  laurentPlusDatum C.base f

/-- Each plus-piece `C.plusDatum f` is contained in `C.base`'s rational
open — by `laurentPlus_subset`. -/
theorem RationalCovering.plusDatum_subset_base (C : RationalCovering A) (f : A) :
    rationalOpen (C.plusDatum f).T (C.plusDatum f).s ⊆
      rationalOpen C.base.T C.base.s :=
  laurentPlus_subset C.base f

/-- The V-covers finset built from a standard-cover refinement: the image
of `S.elts` under `C.plusDatum`. Uses `Classical.decEq` since
`RationalLocData A` does not carry decidable equality in general. -/
noncomputable def RationalCovering.standardCoverVCovers
    (C : RationalCovering A) (S : Finset A) :
    Finset (RationalLocData A) :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  S.image C.plusDatum

omit [HasLocLiftPowerBounded A] in
/-- Membership in `standardCoverVCovers`: an element `D` is in the V-covers
iff it equals `C.plusDatum f` for some `f ∈ S`. -/
theorem RationalCovering.mem_standardCoverVCovers
    (C : RationalCovering A) (S : Finset A) {D : RationalLocData A} :
    D ∈ C.standardCoverVCovers S ↔ ∃ f ∈ S, C.plusDatum f = D := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  show D ∈ (S.image C.plusDatum) ↔ _
  exact Finset.mem_image

/-- Each element of `standardCoverVCovers S` is contained in `C.base`. -/
theorem RationalCovering.standardCoverVCovers_subset_base
    (C : RationalCovering A) (S : Finset A) (D : RationalLocData A)
    (hD : D ∈ C.standardCoverVCovers S) :
    rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s := by
  obtain ⟨f, _, rfl⟩ := (C.mem_standardCoverVCovers S).mp hD
  exact C.plusDatum_subset_base f

/-! **TODO (next incremental step)**: construct the refinement map
`τ : standardCoverVCovers → C.covers` from `hS_contain` (clause 2 of
`refines_by_standard_cover`) and prove it respects rational-open
containment. The construction is a Classical.choose on `f ∈ S.elts`;
the containment proof needs bridging the definitional projections from
`laurentPlusDatum` (i.e. `(laurentPlusDatum D₀ f).T = insert f D₀.T`
and `(laurentPlusDatum D₀ f).s = D₀.s`), which don't reduce via `rfl`
even after `unfold` (Lean 4 reducibility of `noncomputable def ... where`
struct bodies is fragile). Recommended workaround for a follow-up
session: state these T/s projection equalities in `LaurentRefinement.lean`
directly (next to `laurentPlusDatum`), tagged `@[simp]`, so they're
available transparently everywhere downstream. Similarly for
`laurentMinusDatum`. -/

/-! ## Roadmap: Laurent-cover induction for `hV_glue`

The next step in closing T-GEOM-RED is to build `hV_glue` for a
standard-cover refinement `V` from the pointwise Laurent-cover gluing
`laurentCover_gluing_presheaf`.

### Inductive target

Given `S : StandardCover A` (i.e. `S.elts : Finset A` with
`Ideal.span S.elts = ⊤`) refining `C` via the plus-pieces
`rationalOpen (insert f C.base.T) C.base.s` for `f ∈ S.elts`, the
`hV_glue` obligation is: for any compatible family on these plus-pieces,
there is a global section on `C.base`.

Induction on `|S.elts|`:

* **Base case `|S.elts| = 1`**: `S = {f}` with `Ideal.span {f} = ⊤`
  forces `f ∈ Aˣ`. The single plus-piece equals `rationalOpen C.base.T
  C.base.s` (since `v(f) > 0` for every valuation, so `v(f) ≤ v(C.base.s)`
  is the only nontrivial constraint). Gluing is trivial: the compatible
  family has a unique element which *is* the global section.

* **Inductive step `|S.elts| = n + 1`**: pick any `f₀ ∈ S.elts`. Apply
  Laurent cover at `f₀` to split `rationalOpen C.base.T C.base.s` into
  `rationalOpen (insert f₀ C.base.T) C.base.s` (plus at `f₀`) and
  `rationalOpen ((insert C.base.s C.base.T).product ... .image ...)
  (C.base.s * f₀)` (minus at `f₀`).

  Apply `laurentCover_gluing_presheaf` (after T-OV-1 lands) at `f₀` to
  the given V-compatible family, restricted to each half. The induction
  hypothesis applies to the `n`-element standard cover `S.elts \ {f₀}`
  on each half (after appropriate refinement adjustments).

### Remaining obligations

The induction requires:

1. **Laurent-cover splitting at the base level with compatibility transfer**:
   given a compatible family on `V_covers`, its restriction to each
   Laurent half is compatible. Mechanical.

2. **Intersection-of-refinements construction**: the induction step needs
   to refine `S.elts \ {f₀}` onto each Laurent half, which may require
   taking intersections with the plus/minus datum. This is the
   `laurentPlus/MinusDatum` composition that's already modelled in
   `laurentOverlapDatum`.

3. **`laurentCover_gluing_presheaf`** (provided externally, modulo T-OV-1).

4. **Local cover-level injectivity** for each piece of each refinement
   step (provided by T-IDEAL-2 via Cor 8.32, applied at each level).

Estimated lines for the full induction: ~150-250, once T-OV-1 and
T-IDEAL-2 land. This file currently provides the base-case wrap
(`tateAcyclicity_gluing_via_refinement_cover_level`); the inductive
assembly is deferred to a follow-up session.

The concrete next step is to formalize the base-case `|S.elts| = 1`
lemma and the "Laurent split transfers compatibility" lemma; both are
mechanical given `laurentCover_gluing_presheaf` and the existing
restriction-map API. -/

end ValuationSpectrum
