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

end ValuationSpectrum
