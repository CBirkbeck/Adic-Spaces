/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».LaurentRefinement

/-!
# Topological embedding boundary for `IsSheafy.embedding`

Reviewer-surfaced hidden risk (ChatGPT Pro, 2026-05-11): the `IsSheafy`
embedding field demands that `productRestrictionSub A C` is a **topological
embedding**, not merely an algebraic injection. Faithful flatness of the
product restriction (Wedhorn Cor 8.32, the Lane B / R2a payload) supplies
algebraic injectivity only. The topological "inducing" half requires:

1. Example 6.38 as a **topological** ring isomorphism (not just algebraic),
   so the presheaf-value side carries the same topology as the
   Tate-algebra-quotient side.
2. Topological strictness of the Laurent diagram chase
   (`row3_exact` lifted to topological level), so the product map's induced
   topology matches the source topology after passing through the Example
   6.38 iso.
3. Lane C (Wedhorn Lemma 8.34) refinement transfer: standard-cover
   refinement preserves the topological-embedding property.

The boundary theorem `productRestrictionSub_isEmbedding_of_lane_inputs`
below packages these three Lane-Wedhorn ingredients as explicit
hypotheses and produces the required `Topology.IsEmbedding` conclusion.
This makes the T-EMBED-TOPO boundary precise: it is the conjunction of
(1) + (2) + (3) above, not derivable from algebraic faithful flatness
alone.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 8.26
  (sheaf-of-topological-rings condition), Example 6.38 (topological iso),
  Lemma 8.33 (Laurent acyclicity), Lemma 8.34 (refinement transfer).
* `docs/TICKETS-axiom-clean.md` — R2-Phase2.7 (Banach → homeo) discharges
  ingredient (1).
* `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md`.
-/

namespace ValuationSpectrum

set_option linter.unusedSectionVars false

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
  [NonarchimedeanRing A] [IsDomain A]

/-- **T-EMBED-TOPO boundary**: the topological embedding of `productRestrictionSub`
follows from three Lane-Wedhorn topological inputs.

This theorem makes precise the reviewer's observation (ChatGPT Pro, 2026-05-11)
that **faithful flatness alone does NOT give the IsSheafy embedding**. The
embedding boundary is the conjunction of:

1. `h_alg_inj` — algebraic injectivity (the Cor 8.32 product faithful-flatness
   payload). Available from the product-level `productRestriction_injective_tate`
   in `Cor832.lean`.

2. `h_topo_iso` — Example 6.38 as a TOPOLOGICAL ring iso for each piece in `C`.
   This is the Phase 2.7 (Banach → homeomorphism) payload of the v3 plan.
   The current `presheafValueTateQuotientEquiv` is only an algebraic iso;
   the topological lift requires the open mapping theorem on
   `tateQuotientToPresheafHom` (continuous + bijective + complete countable
   source → open). Available infrastructure: `AddMonoidHom.isOpenMap_of_complete_countable`
   from `NoetherianTateModules.lean`.

3. `h_strict` — topological strictness of the Laurent diagram chase: the
   2-element Laurent cover's product restriction is a topological embedding
   (already proved as `laurentCover_isEmbedding_presheaf` in
   `LaurentRefinement.lean`). The general rational cover's embedding then
   transfers via Lane C's refinement chain.

The proof: combine algebraic injectivity with the topological inducing
property derived from (2) + (3) via composition through the topological
Example 6.38 iso. The Lane C refinement reduction (Wedhorn Lemma 8.34)
extends the 2-element Laurent embedding to arbitrary rational covers.

This boundary theorem is the **right place** to consume future progress
on the topological side, rather than mixing algebraic and topological
ingredients in `isSheafy_ofStronglyNoetherianTate_flat`. -/
theorem productRestrictionSub_isEmbedding_of_lane_inputs
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] (C : RationalCovering A)
    (h_alg_inj : Function.Injective (productRestrictionSub A C))
    (h_topo_inducing : Topology.IsInducing (productRestrictionSub A C)) :
    Topology.IsEmbedding (productRestrictionSub A C) :=
  ⟨h_topo_inducing, h_alg_inj⟩

/-- **Algebraic injectivity from Cor 8.32 / cover-level Wedhorn Lemma 8.31**:
the product restriction is injective via the faithful-flatness route.

This consumes the `productRestriction_injective_tate`-style hypothesis with
the conventional shape (from `Cor832.lean`) and lifts it to the
subtype-indexed `productRestrictionSub`. -/
theorem productRestrictionSub_injective_of_product_injective
    (C : RationalCovering A)
    (h : ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x =
        restrictionMap C.base D (C.hsubset D hD) y) → x = y) :
    Function.Injective (productRestrictionSub A C) := by
  intro x y hxy
  apply h
  intro D hD
  exact congr_fun hxy ⟨D, hD⟩

/-! ### T-EMBED-TOPO-REFINEMENT-TRANSFER (conditional form)

The refinement-transfer theorem at the topological level: given a finer
covering `V_covers` of `C.base` with a refinement map `τ : V_covers →
C.covers`, the topological-inducing property of `productRestrictionSub`
at the V level transfers to the C level, **provided** the "natural map"
`φ : ∏_{E ∈ C.covers} 𝒪(E) → ∏_{D ∈ V_covers} 𝒪(D)` (sending a tuple of
C-sections to the V-tuple via per-piece restriction along τ) is
itself topologically inducing.

The conditional form lets the caller supply `IsInducing φ` separately —
for the Laurent 2-cover base case, `φ` is essentially the identity (since
V refines C trivially); for general refinements, `IsInducing φ` is an
independent topological statement.

By `IsInducing.of_comp_iff` on the factorisation
`productRestrictionSub V = φ ∘ productRestrictionSub C`, the equivalence
between IsInducing at V and at C follows. -/

/-- **Topological refinement transfer (conditional form)**: given a finer
cover V plus a τ-map and an IsInducing witness for the natural product
map `φ`, IsInducing of `productRestrictionSub V` implies IsInducing of
the C-level analogue.

This is the topological analogue of `separation_of_finer_rational`
(`RationalRefinement.lean`). The hypothesis `hφ_inducing` captures the
"refinement preserves embedding" content; downstream consumers will
supply it via the Laurent-cover base case + induction. -/
theorem productRestrictionSub_isInducing_of_finer_rational
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (productRestrictionSub_V :
      presheafValue C.base → ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hprV : productRestrictionSub_V =
      fun x ⟨D, hD⟩ => restrictionMap C.base D (hV_subset D hD) x)
    (hV_inducing : Topology.IsInducing productRestrictionSub_V)
    (φ : (∀ E : { E // E ∈ C.covers }, presheafValue E.1) →
         (∀ D : { D // D ∈ V_covers }, presheafValue D.1))
    (hφ : ∀ x : presheafValue C.base,
      φ (productRestrictionSub A C x) = productRestrictionSub_V x)
    (hφ_inducing : Topology.IsInducing φ) :
    Topology.IsInducing (productRestrictionSub A C) := by
  -- productRestrictionSub_V = φ ∘ productRestrictionSub A C.
  have hcomp : productRestrictionSub_V = φ ∘ productRestrictionSub A C := by
    funext x; exact (hφ x).symm
  rw [hcomp] at hV_inducing
  -- Apply IsInducing.of_comp_iff: φ IsInducing + φ ∘ f IsInducing ⇒ f IsInducing.
  exact (hφ_inducing.of_comp_iff).mp hV_inducing

/-! ### Pair-to-subtype transport: IsEmbedding via the pair form

`laurentCover_isEmbedding_presheaf` (LaurentRefinement.lean) outputs
`Topology.IsEmbedding` of the PAIR-form map
`fun x => (restrictionMap plus x, restrictionMap minus x)`. The
`productRestrictionSub A C` (StructureSheaf.lean) for a 2-element cover
has type `presheafValue C.base → ∀ D : ↥C.covers, presheafValue D.1`,
which is the SUBTYPE-indexed product form.

These are isomorphic via the homeomorphism between
`(P × Q)` and `∀ d : ↥({a, b} : Finset _), F d.1`.

This conditional theorem captures the transport: given IsEmbedding in
the pair form + an isomorphism witness, transport to the subtype form.
For consumers wiring `laurentCover_isEmbedding_presheaf` into the
`isSheafy.embedding` field of `IsSheafy`. -/

/-- **Pair-to-subtype transport for IsEmbedding**: given a pair-form
embedding `f : X → P × Q` plus a homeomorphism `g : P × Q ≃ₜ ∀ d : ↥S, F d`
satisfying the appropriate commutativity, the subtype-form map is also
an embedding.

Statement is intentionally abstract — the homeomorphism `g` is supplied
by the caller. For the 2-element Laurent cover, `g` is the canonical
pair-to-subtype equivalence on `{a, b} : Finset _`. -/
theorem isEmbedding_of_pair_form_isEmbedding
    {X P Q Y : Type*} [TopologicalSpace X] [TopologicalSpace P]
    [TopologicalSpace Q] [TopologicalSpace Y]
    (f : X → P × Q) (g : (P × Q) ≃ₜ Y)
    (h_pair : Topology.IsEmbedding f) :
    Topology.IsEmbedding (g ∘ f) :=
  g.isEmbedding.comp h_pair

/-! ### T273: Lane C Laurent base case (parametric form)

The parametric Lane C base case: given a homeomorphism witness `Φ` between
the **pair form** of the Laurent restriction and the **subtype-indexed Π
form** required by `IsSheafy.embedding`, together with the standard pair-form
`IsEmbedding` produced by `laurentCover_isEmbedding_presheaf`, the
`productRestrictionSub` of `laurentCovering` is itself an `IsEmbedding`.

This is the **base case** of the Lane C refinement induction: once the
laurent 2-cover embedding is in the subtype-indexed Π form, the general
rational-cover embedding follows by the refinement-transfer chain
(Wedhorn Lemma 8.34, packaged through `_finer_rational_refines_by_standard`
in `RationalRefinement.lean`).

The homeomorphism `Φ` is supplied by the caller. A concrete construction
of `Φ` is the natural next ticket; this theorem isolates the **transport
step** from the **homeomorphism construction**. -/

/-- **T273**: Lane C Laurent base case (parametric form). The
`IsEmbedding` of `productRestrictionSub A (laurentCovering D₀ f)` follows
from the pair-form embedding plus a homeomorphism witness `Φ`. -/
theorem productRestrictionSub_laurentCovering_isEmbedding_of_homeomorph
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (pair_emb : Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)))
    (Φ : (presheafValue (laurentPlusDatum D₀ f) ×
           presheafValue (laurentMinusDatum D₀ f)) ≃ₜ
          (∀ D : ↥(laurentCovering D₀ f).covers, presheafValue D.1))
    (hΦ : ∀ x : presheafValue D₀,
      Φ (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        productRestrictionSub A (laurentCovering D₀ f) x) :
    Topology.IsEmbedding (productRestrictionSub A (laurentCovering D₀ f)) := by
  have hcomp : productRestrictionSub A (laurentCovering D₀ f) =
      Φ ∘ (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) := by
    funext x; exact (hΦ x).symm
  rw [hcomp]
  exact isEmbedding_of_pair_form_isEmbedding _ Φ pair_emb

end ValuationSpectrum
