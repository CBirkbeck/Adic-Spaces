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

/-! ### T274: Two-element subtype Pi ≃ₜ pair (generic utility)

For any decidable type `α` with distinct elements `a ≠ b` and a family
`F : α → Type*` with topologies on each fiber, there is a canonical
homeomorphism between the pair type `F a × F b` and the subtype-indexed
Π type `∀ x : ↥({a, b} : Finset α), F x.1`.

This is the Mathlib-style **generic utility** used to construct the
homeomorphism `Φ` required by T273. The construction is fully explicit:
the forward map dispatches by decidable equality with `a` and uses
dependent transport; the inverse evaluates the Π at the two canonical
membership witnesses. Continuity in both directions is mechanical
(each projection / each pair coordinate is continuous). -/

/-! ### T280: generic IsInducing absorbs additional projections

Key general topological lemma: if `f : X → Π i, Y i` is continuous and
the composition with **some single projection** `eval_i ∘ f` is
`IsInducing`, then `f` itself is `IsInducing`.

Mathematical content: `tX = induced (eval_i ∘ f) (Y i) = induced f (induced eval_i (Y i)) ≤ induced f (Pi.topology)`
since `induced eval_i (Y i) ≤ Pi.topology` (eval is continuous). Combined
with `tX ≤ induced f (Pi.topology)` (from `f` continuous), antisymmetry
gives equality.

This is the key tool for the Lane C induction: once a sufficient set of
restriction maps determines the source topology (e.g., a Laurent 2-cover
via T279), adding MORE pieces to the cover preserves the inducing property
of the diagonal.

The lemma is stated in generic form (no `Adic spaces` content); it could
in principle live in Mathlib. -/

/-- **T280**: if `f : X → Π i, Y i` is continuous and `(eval i ∘ f)` is
`IsInducing` for some `i`, then `f` itself is `IsInducing`.

This is the "adding more continuous projections preserves IsInducing"
lemma: once a subset of projections determines the source topology, the
full family also does. -/
theorem _root_.Topology.IsInducing.of_eval
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : X → ∀ i, Y i} (hf : Continuous f)
    {i : ι} (hi : Topology.IsInducing (fun x => f x i)) :
    Topology.IsInducing f := by
  rw [Topology.isInducing_iff]
  apply le_antisymm
  · exact hf.le_induced
  · rw [Topology.isInducing_iff] at hi
    rw [hi, show (fun x => f x i) = (fun y : ∀ j, Y j => y i) ∘ f from rfl,
      ← induced_compose]
    exact induced_mono (continuous_apply i).le_induced

/-- **T281**: generalization of T280 — if `f : X → Y`, `g : Y → Z`,
`f` continuous, `g` continuous, and `g ∘ f` is `IsInducing`, then `f`
itself is `IsInducing`.

This is the "post-composition with a continuous map only TIGHTENS the
inducing property" lemma. It does NOT require `g` to be `IsInducing` —
unlike `Topology.IsInducing.of_comp_iff` which needs `IsInducing g`.

The mathematical content: `tX = induced (g ∘ f) tZ = induced f (induced g tZ) ≤ induced f tY`
(since `induced g tZ ≤ tY` from `g` continuous). Combined with
`tX ≤ induced f tY` (from `f` continuous), antisymmetry gives equality.

T280 is the special case where `g = eval_i` (a single projection).
T281 covers the general case where the "extra structure" `g` is any
continuous map (not just a projection or a homeomorphism). -/
theorem _root_.Topology.IsInducing.of_continuous_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f)
    {g : Y → Z} (hg : Continuous g)
    (hgf : Topology.IsInducing (g ∘ f)) :
    Topology.IsInducing f := by
  rw [Topology.isInducing_iff]
  apply le_antisymm
  · exact hf.le_induced
  · rw [Topology.isInducing_iff] at hgf
    rw [hgf, ← induced_compose]
    exact induced_mono hg.le_induced

/-- **T283**: `productRestrictionSub A C` is always continuous.

Each component is `restrictionMap C.base D _`, which is continuous via
`restrictionMapHom_continuous` (the underlying-function form of the
continuous ring homomorphism). The full Π-valued map is continuous by
`continuous_pi`. -/
theorem productRestrictionSub_continuous (C : RationalCovering A) :
    Continuous (productRestrictionSub A C) := by
  refine continuous_pi ?_
  rintro ⟨D, hD⟩
  show Continuous (restrictionMap C.base D (C.hsubset D hD))
  exact restrictionMapHom_continuous C.base D (C.hsubset D hD)

/-- **T282**: **strengthened** topological refinement transfer.

Same as `productRestrictionSub_isInducing_of_finer_rational` (T267) but
with the heavy `IsInducing φ` hypothesis weakened to `Continuous φ` —
much easier to discharge in practice. Routes through T281
(`Topology.IsInducing.of_continuous_comp`) instead of `of_comp_iff`.

The downstream consumer chain becomes:
- Find a finer cover V with IsInducing of `productRestrictionSub_V`
  (e.g., from T279's laurentCovering IsEmbedding).
- Construct the natural product map `φ : Π_C → Π_V` and show its
  CONTINUITY (just continuity of each restriction-composed component).
- Conclude IsInducing for the C-level restriction.

This eliminates the substantial obligation to show `φ` is `IsInducing`
(which would otherwise require independent topological analysis of the
refinement map). -/
theorem productRestrictionSub_isInducing_of_finer_rational_continuous
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (productRestrictionSub_V :
      presheafValue C.base → ∀ D : { D // D ∈ V_covers }, presheafValue D.1)
    (hprV : productRestrictionSub_V =
      fun x ⟨D, hD⟩ => restrictionMap C.base D (hV_subset D hD) x)
    (hV_inducing : Topology.IsInducing productRestrictionSub_V)
    (φ : (∀ E : { E // E ∈ C.covers }, presheafValue E.1) →
         (∀ D : { D // D ∈ V_covers }, presheafValue D.1))
    (hφ : ∀ x : presheafValue C.base,
      φ (productRestrictionSub A C x) = productRestrictionSub_V x)
    (hφ_continuous : Continuous φ)
    (hprC_continuous : Continuous (productRestrictionSub A C)) :
    Topology.IsInducing (productRestrictionSub A C) := by
  have hcomp : productRestrictionSub_V = φ ∘ productRestrictionSub A C := by
    funext x; exact (hφ x).symm
  rw [hcomp] at hV_inducing
  exact Topology.IsInducing.of_continuous_comp hprC_continuous hφ_continuous hV_inducing

/-- **T274**: the canonical homeomorphism between a pair type and the
subtype-indexed Π type over a 2-element Finset (for distinct elements). -/
def twoElementSubtypePiHomeomorph
    {α : Type*} [DecidableEq α] (a b : α) (hne : a ≠ b)
    {F : α → Type*} [∀ x, TopologicalSpace (F x)] :
    F a × F b ≃ₜ (∀ x : ↥({a, b} : Finset α), F x.1) := by
  refine Homeomorph.mk
    { toFun := fun pq ⟨x, hx⟩ =>
        if h : x = a then h ▸ pq.1
        else
          have hxb : x = b := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            exact hx.resolve_left h
          hxb ▸ pq.2
      invFun := fun g =>
        (g ⟨a, Finset.mem_insert_self _ _⟩,
         g ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)
      left_inv := by
        rintro ⟨p, q⟩
        refine Prod.ext ?_ ?_
        · simp
        · simp [dif_neg hne.symm]
      right_inv := by
        intro g
        funext ⟨x, hx⟩
        by_cases h : x = a
        · subst h; simp
        · have hxb : x = b := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            exact hx.resolve_left h
          subst hxb
          simp [dif_neg h] }
    ?_ ?_
  · -- continuous_toFun
    refine continuous_pi ?_
    rintro ⟨x, hx⟩
    by_cases h : x = a
    · subst h
      simp only [dif_pos rfl]
      exact continuous_fst
    · have hxb : x = b := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact hx.resolve_left h
      subst hxb
      simp only [dif_neg h]
      exact continuous_snd
  · -- continuous_invFun
    refine continuous_prodMk.mpr ⟨?_, ?_⟩
    · exact continuous_apply _
    · exact continuous_apply _

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

/-- **T275**: Lane C Laurent base case, **concrete** form. Combines T274
(the generic two-element subtype Pi homeomorphism) with T273 (the
parametric transport): the `IsEmbedding` of `productRestrictionSub` for
`laurentCovering D₀ f` follows from the pair-form embedding plus the
distinctness `laurentPlusDatum D₀ f ≠ laurentMinusDatum D₀ f`.

The commutativity hypothesis of T273 is **discharged automatically**
because `restrictionMap` is proof-irrelevant in its subset argument
(Lean Prop). The homeomorphism `Φ` is constructed by T274. -/
theorem productRestrictionSub_laurentCovering_isEmbedding_of_distinct
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hne : laurentPlusDatum D₀ f ≠ laurentMinusDatum D₀ f)
    (pair_emb : Topology.IsEmbedding
      (fun x : presheafValue D₀ =>
        (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x))) :
    Topology.IsEmbedding (productRestrictionSub A (laurentCovering D₀ f)) := by
  classical
  -- Construct Φ via T274.
  let Φ : (presheafValue (laurentPlusDatum D₀ f) ×
            presheafValue (laurentMinusDatum D₀ f)) ≃ₜ
           (∀ D : ↥(laurentCovering D₀ f).covers, presheafValue D.1) :=
    twoElementSubtypePiHomeomorph (laurentPlusDatum D₀ f)
      (laurentMinusDatum D₀ f) hne
  -- Verify the commutativity hypothesis of T273.
  apply productRestrictionSub_laurentCovering_isEmbedding_of_homeomorph
    D₀ f hplus hminus pair_emb Φ
  intro x
  funext ⟨D, hD⟩
  -- The Pi value at ⟨D, hD⟩ is `restrictionMap D₀ D ((laurentCovering D₀ f).hsubset D hD) x`.
  -- The Φ-image dispatches: if D = plus, use the first projection; else (D = minus), use the second.
  -- Both sides equal `restrictionMap D₀ D _ x` by proof irrelevance.
  show Φ (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
         restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) ⟨D, hD⟩ =
       restrictionMap D₀ D ((laurentCovering D₀ f).hsubset D hD) x
  -- Unfold Φ to expose the dispatch by `Decidable.decEq`.
  by_cases hDp : D = laurentPlusDatum D₀ f
  · subst hDp
    show (if h : laurentPlusDatum D₀ f = laurentPlusDatum D₀ f then
            h ▸ restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x
          else _) = _
    rw [dif_pos rfl]
  · have hDm : D = laurentMinusDatum D₀ f := by
      simp only [laurentCovering, Finset.mem_insert, Finset.mem_singleton] at hD
      exact hD.resolve_left hDp
    subst hDm
    show (if h : laurentMinusDatum D₀ f = laurentPlusDatum D₀ f then _
          else _) = _
    rw [dif_neg hne.symm]

/-! ### T276: Concrete single-Laurent-cover IsInducing supplier

Wires the bridge-form pair embedding
`laurentCover_isEmbedding_presheaf_via_bridges_baire_quotientSigma_auto`
(LaurentRefinement.lean) into T275's concrete Lane C base case to produce
`Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f))`
— the concrete first step of the Lane C induction.

This is the **single-`f` IsInducing supplier**: given the bridge hypothesis
bundle (with the bridges auto-discharged via the `_baire_quotientSigma_auto`
variant), output the subtype-indexed IsInducing for the 2-element Laurent
cover. -/

/-- **T276**: concrete single-Laurent-cover IsInducing via the bridge form.
Consumes the same hypothesis bundle as the
`laurentCover_isEmbedding_presheaf_via_bridges_baire_quotientSigma_auto`
variant, plus the distinctness
`hne : laurentPlusDatum D₀ f ≠ laurentMinusDatum D₀ f`. -/
theorem productRestrictionSub_laurentCovering_isInducing_via_bridges
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hne : laurentPlusDatum D₀ f ≠ laurentMinusDatum D₀ f)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigCp_TA : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f)) := by
  -- Step 1: pair-form embedding from the bridges auto-supplier.
  have pair_emb :
      Topology.IsEmbedding
        (fun x : presheafValue D₀ =>
          (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
           restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) :=
    laurentCover_isEmbedding_presheaf_via_bridges_baire_quotientSigma_auto
      P D₀ f hf_nonunit hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B
      hnoeth₂_B hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
      hSigCp_TA hplus hminus
  -- Step 2: transport to subtype-indexed Π form via T275.
  have subtype_emb :
      Topology.IsEmbedding (productRestrictionSub A (laurentCovering D₀ f)) :=
    productRestrictionSub_laurentCovering_isEmbedding_of_distinct
      D₀ f hplus hminus hne pair_emb
  exact subtype_emb.toIsInducing

/-- **T278**: convenience wrapper for T276 with `hne` discharged via T277.
Replaces the `hne` parameter by the more natural `hs : D₀.s ≠ 0`, which
matches the case-split in `isSheafy_ofStronglyNoetherianTate_flat` (line
1128 of `StructureSheaf.lean`). -/
theorem productRestrictionSub_laurentCovering_isInducing_via_bridges_of_s_ne_zero
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hs : D₀.s ≠ 0)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigCp_TA : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f)) :=
  productRestrictionSub_laurentCovering_isInducing_via_bridges P D₀ f hf_nonunit
    (laurentPlus_ne_laurentMinus_of_nonunit D₀ f hf_nonunit hs)
    hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B hLocLift_B
    hA₀Noeth_B hcont_forward_B hcont_eval_B hSigCp_TA hplus hminus

/-- **T279**: single-Laurent-cover `IsEmbedding` supplier (full Embedding,
not just Inducing). Same hypothesis bundle as T278 but produces
`Topology.IsEmbedding` directly. Useful for consumers that need both the
inducing and injective halves of `IsEmbedding`. -/
theorem productRestrictionSub_laurentCovering_isEmbedding_via_bridges_of_s_ne_zero
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hs : D₀.s ≠ 0)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigCp_TA : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsEmbedding (productRestrictionSub A (laurentCovering D₀ f)) := by
  have pair_emb :
      Topology.IsEmbedding
        (fun x : presheafValue D₀ =>
          (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x,
           restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x)) :=
    laurentCover_isEmbedding_presheaf_via_bridges_baire_quotientSigma_auto
      P D₀ f hf_nonunit hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B
      hnoeth₂_B hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
      hSigCp_TA hplus hminus
  exact productRestrictionSub_laurentCovering_isEmbedding_of_distinct
    D₀ f hplus hminus
    (laurentPlus_ne_laurentMinus_of_nonunit D₀ f hf_nonunit hs)
    pair_emb

/-! ### T284: Lane C single-step closer

The end-to-end Lane C **closer** for the case where a Laurent covering
at `C.base` refines `C`. Combines:

- **T279** `productRestrictionSub_laurentCovering_isEmbedding_via_bridges_of_s_ne_zero`:
  the laurent-2-cover `IsEmbedding` at `C.base`.
- **T282** `productRestrictionSub_isInducing_of_finer_rational_continuous`:
  strengthened refinement transfer (only needs `Continuous φ`).
- **T283** `productRestrictionSub_continuous`: automatic continuity of
  `productRestrictionSub A C`.

The result: given a Laurent covering `laurentCovering C.base f₀` that
refines `C` (each laurent piece is contained in some C-piece), and a
**continuous** natural map `φ` between the C and laurent product types,
`productRestrictionSub A C` is `IsInducing`.

This is the **single-Laurent-refinement** closer. For arbitrary `C`,
multiple Laurent refinements may be needed (full standard-cover
induction), but the single-step form captures the essential transport
mechanism. -/

/-! ### T285: Natural refinement map between product types

For a refinement `V` of `C` (each V-piece contained in some C-piece via
τ), the **natural product map** `φ : Π_C → Π_V` sends `(x_E)_{E ∈ C}` to
`(restrictionMap (τ D) D _ (x_{τ D}))_{D ∈ V}`.

This is the canonical map appearing in the refinement transfer (T282).
It is automatically continuous by `continuous_pi` + projection
continuity + `restrictionMap` continuity. -/

/-- **T285 (def)**: the natural refinement map `φ : Π_C → Π_V` for a
τ-function from V back to C. -/
noncomputable def naturalRefinementMap
    {C : RationalCovering A}
    {V_covers : Finset (RationalLocData A)}
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s) :
    (∀ E : { E // E ∈ C.covers }, presheafValue E.1) →
      (∀ D : { D // D ∈ V_covers }, presheafValue D.1) :=
  fun x_C d => restrictionMap (τ d).1 d.1 (hτ d) (x_C (τ d))

/-- **T285 (continuity)**: the natural refinement map is continuous. -/
theorem naturalRefinementMap_continuous
    {C : RationalCovering A}
    {V_covers : Finset (RationalLocData A)}
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s) :
    Continuous (naturalRefinementMap τ hτ) := by
  refine continuous_pi ?_
  intro d
  unfold naturalRefinementMap
  exact (restrictionMapHom_continuous (τ d).1 d.1 (hτ d)).comp (continuous_apply (τ d))

/-- **T285 (commutativity)**: the natural refinement map composes with
`productRestrictionSub_C` to give `productRestrictionSub_V` (where V is
the refined cover with subset proof factoring through τ). -/
theorem naturalRefinementMap_comp
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (x : presheafValue C.base) :
    naturalRefinementMap τ hτ (productRestrictionSub A C x) =
      fun d => restrictionMap C.base d.1
        ((hτ d).trans (C.hsubset (τ d).1 (τ d).2)) x := by
  funext d
  unfold naturalRefinementMap
  show restrictionMap (τ d).1 d.1 (hτ d)
      (restrictionMap C.base (τ d).1 (C.hsubset (τ d).1 (τ d).2) x) = _
  exact congr_fun (restrictionMap_comp C.base (τ d).1 d.1
    (C.hsubset (τ d).1 (τ d).2) (hτ d)) x

/-- **T284**: Lane C single-step closer via laurent refinement. Given
the bridges hypothesis bundle + laurent refinement data + commutativity
+ continuity of the natural map `φ`, conclude `IsInducing` for the C-level
product restriction. -/
theorem productRestrictionSub_isInducing_via_laurent_refinement
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (f₀ : A)
    (hf_nonunit : ¬IsUnit (C.base.canonicalMap f₀))
    (hs : C.base.s ≠ 0)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hDom_B : IsDomain (presheafValue C.base))
    (hSigCp_B : SigmaCompactSpace (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
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
    (hSigCp_TA : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      SigmaCompactSpace ↥(TateAlgebra (presheafValue C.base)))
    (hplus : rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s ⊆
      rationalOpen C.base.T C.base.s)
    (hminus : rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s ⊆
      rationalOpen C.base.T C.base.s)
    (φ : (∀ E : { E // E ∈ C.covers }, presheafValue E.1) →
         (∀ D : { D // D ∈ (laurentCovering C.base f₀).covers }, presheafValue D.1))
    (hφ : ∀ x : presheafValue C.base,
      φ (productRestrictionSub A C x) =
        productRestrictionSub A (laurentCovering C.base f₀) x)
    (hφ_continuous : Continuous φ) :
    Topology.IsInducing (productRestrictionSub A C) := by
  -- Step 1: laurent IsEmbedding via T279.
  have hlaurent_emb :
      Topology.IsEmbedding
        (productRestrictionSub A (laurentCovering C.base f₀)) :=
    productRestrictionSub_laurentCovering_isEmbedding_via_bridges_of_s_ne_zero
      P C.base f₀ hf_nonunit hs hNoeth_B hDom_B hSigCp_B hA_complete_B
      hnoeth_B hnoeth₂_B hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
      hSigCp_TA hplus hminus
  have hlaurent_ind : Topology.IsInducing
      (productRestrictionSub A (laurentCovering C.base f₀)) :=
    hlaurent_emb.toIsInducing
  -- Step 2: apply T282 (strengthened refinement transfer).
  -- Note: the laurent V is `(laurentCovering C.base f₀).covers`, refinement
  -- transfer uses `productRestrictionSub_V = productRestrictionSub A (laurentCovering C.base f₀)`.
  refine productRestrictionSub_isInducing_of_finer_rational_continuous
    C (laurentCovering C.base f₀).covers
    (fun D hD => (laurentCovering C.base f₀).hsubset D hD)
    (productRestrictionSub A (laurentCovering C.base f₀))
    ?_ hlaurent_ind φ hφ hφ_continuous (productRestrictionSub_continuous C)
  funext x ⟨D, hD⟩
  rfl

/-- **T286**: τ-only Lane C closer. Combines T285 (natural refinement
map + continuity + commutativity) with T284 to eliminate the manual
`φ` / `hφ_continuous` / `hφ` hypotheses. The consumer needs only:

- The bridges hypothesis bundle (consumed by T279).
- A τ-function from `↥(laurentCovering C.base f₀).covers` to `↥C.covers`.
- The per-piece containment proof for τ.

This is the **practical** end-to-end Lane C closer for single-Laurent
refinements. The τ-function plus containment is the **structural input
about C** (each laurent piece is contained in some C-piece), and it is
what an actual consumer would need to provide. -/
theorem productRestrictionSub_isInducing_via_laurent_refinement_tau
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (f₀ : A)
    (hf_nonunit : ¬IsUnit (C.base.canonicalMap f₀))
    (hs : C.base.s ≠ 0)
    (hNoeth_B : IsNoetherianRing (presheafValue C.base))
    (hDom_B : IsDomain (presheafValue C.base))
    (hSigCp_B : SigmaCompactSpace (presheafValue C.base))
    (hA_complete_B : @CompleteSpace (presheafValue C.base)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue C.base)))
    (hnoeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue C.base)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      HasLocLiftPowerBounded (presheafValue C.base))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      letI : IsNoetherianRing (presheafValue C.base) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P C.base).A₀))
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
    (hSigCp_TA : letI : IsTateRing (presheafValue C.base) :=
        presheafValue_isTateRing P C.base
      SigmaCompactSpace ↥(TateAlgebra (presheafValue C.base)))
    (hplus : rationalOpen (laurentPlusDatum C.base f₀).T (laurentPlusDatum C.base f₀).s ⊆
      rationalOpen C.base.T C.base.s)
    (hminus : rationalOpen (laurentMinusDatum C.base f₀).T (laurentMinusDatum C.base f₀).s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { d // d ∈ (laurentCovering C.base f₀).covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { d // d ∈ (laurentCovering C.base f₀).covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s) :
    Topology.IsInducing (productRestrictionSub A C) := by
  -- Discharge φ + commutativity + continuity from T285.
  apply productRestrictionSub_isInducing_via_laurent_refinement
    P C f₀ hf_nonunit hs hNoeth_B hDom_B hSigCp_B hA_complete_B
    hnoeth_B hnoeth₂_B hLocLift_B hA₀Noeth_B hcont_forward_B hcont_eval_B
    hSigCp_TA hplus hminus
    (naturalRefinementMap τ hτ)
  · -- Commutativity (via T285's `naturalRefinementMap_comp`).
    intro x
    rw [naturalRefinementMap_comp]
    funext d
    rfl
  · -- Continuity (via T285's `naturalRefinementMap_continuous`).
    exact naturalRefinementMap_continuous τ hτ

/-! ### T287: sanity check — T286 specialized to C = laurentCovering

For `C = laurentCovering D₀ f`, the τ-function is the identity on
`↥C.covers` with reflexive containment. This re-derives T278 via the
Lane C single-step chain (T279 → T285 → T284 → T286), validating that
the chain is consistent.

This is **redundant** with T278 (which closes the same IsInducing more
directly), but serves as a sanity check on the T286 consumer interface.
-/

theorem productRestrictionSub_laurentCovering_isInducing_via_tau_identity
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hs : D₀.s ≠ 0)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hDom_B : IsDomain (presheafValue D₀))
    (hSigCp_B : SigmaCompactSpace (presheafValue D₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hnoeth₂_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing
        ↥(TateAlgebra.pairSubring₂
            (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (hSigCp_TA : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      SigmaCompactSpace ↥(TateAlgebra (presheafValue D₀)))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Topology.IsInducing
      (productRestrictionSub A (laurentCovering D₀ f)) := by
  -- (laurentCovering D₀ f).base = D₀ by definition; the typeclass instance
  -- on D₀ transfers to (laurentCovering D₀ f).base via show.
  haveI : IsNoetherianRing (locSubring (laurentCovering D₀ f).base.P
      (laurentCovering D₀ f).base.T (laurentCovering D₀ f).base.s) :=
    inferInstanceAs (IsNoetherianRing (locSubring D₀.P D₀.T D₀.s))
  haveI : LaurentNormalized (laurentCovering D₀ f).base :=
    inferInstanceAs (LaurentNormalized D₀)
  exact productRestrictionSub_isInducing_via_laurent_refinement_tau
    P (laurentCovering D₀ f) f hf_nonunit hs
    hNoeth_B hDom_B hSigCp_B hA_complete_B hnoeth_B hnoeth₂_B hLocLift_B
    hA₀Noeth_B hcont_forward_B hcont_eval_B hSigCp_TA hplus hminus
    id (fun d => le_refl _)

end ValuationSpectrum
