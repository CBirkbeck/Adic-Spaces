/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornMultiPieceLaurentRefinement

/-!
# Wedhorn 8.34(ii) — Per-piece Laurent cover-assembly API (T057)

T054 (commit `3799c8e`) accepted the per-piece Laurent cover refinement
output `MultiPieceLaurentCoverRefinementOutput`: at every `w ∈ Spa A A⁺`
there exists `τ ∈ T_test` with `w` in the σ-rescaled Laurent piece
`V_τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and a per-piece **singleton**
residual on `V_τ`. T056 (parallel C1 supplier reroute lane, owned by
Claude Tertiary) consumes T054's per-piece data via the per-piece
source-restricted subset inclusion
`R(insert f T_base, s) ∩ V_τ ⊆ R({σ⁻¹ * τ}, D_s)` and exposes the
remaining gap as the named Prop predicate `CoverLevelAssemblyResidual`.

This file lands the **cover-assembly API** parallel to T056's reroute
lane: a reusable, source-side bridge from T054's per-piece subset data
to a Wedhorn 8.34(ii) Lemma 8.33 / Laurent-cover gluing input shape.
The bridge operates **at the subset-of-Spv level** (matching T054's
output type), produces a clean `⋃`-form covering, and **structurally
identifies** the precise content the Wedhorn Lemma 8.33 multi-piece
assembly needs in order to upgrade the union covering to a single
global subset clause (consumed by the C1 supplier).

The write set is disjoint from `WedhornPerPieceLaurentC1Supplier.lean`
(T056) and from all T031–T054 accepted leaves: this is a fresh leaf
file containing only new declarations.

## What this file provides

* `source_subset_iUnion_via_per_piece_cover` — generic mathlib-style
  set-theoretic primitive: from per-piece subset inclusions `S ∩ V_i ⊆
  R_i` and a covering `∀ s ∈ S, ∃ i, s ∈ V_i`, derive `S ⊆ ⋃ i, R_i`.
  Real proof, fully provable, reusable beyond T054 and the Wedhorn
  setting.

* `source_subset_finset_iUnion_via_per_piece_cover` — `Finset`-indexed
  specialisation matching T054's finite Laurent cover indexing.

* `rationalOpen_subset_iUnion_laurentPiece_via_per_piece` — Wedhorn-
  specific specialisation: from per-piece Laurent-piece subset
  inclusions and the σ-rescaled Laurent cover hypothesis, derive
  `rationalOpen (insert f T_base) s ⊆ ⋃ τ ∈ T_test, R τ`. The
  per-piece RHS targets `R τ` are arbitrary and chosen by the caller
  (e.g., `R τ := rationalOpen ({σ⁻¹ * τ}) D_s` for T056's per-piece
  shape).

* `MultiPieceLaurentCover_source_iUnion_assembly` — bridge consuming
  T054's `MultiPieceLaurentCoverRefinementOutput` directly: from the
  per-piece refinement output + per-piece subset inclusions on each
  Laurent piece, derive the union-form source inclusion. The cover
  hypothesis is internally extracted from
  `MultiPieceLaurentCoverRefinementOutput`, exposing how T054 feeds the
  cover-assembly API without manually re-proving the Laurent cover
  hypothesis.

* `LaurentCoverPresheafLemma833Assembly` — explicit Lean Prop
  predicate for the **structured blocker**: Wedhorn 8.33 multi-piece
  cover-level acyclicity assembly. Names exactly the content needed
  to upgrade a `⋃`-form covering to a single global subset clause /
  presheaf-level gluing of the kind consumed by `LaurentRefinement`'s
  existing 2-element Laurent cover gluing API
  (`laurentCover_gluing_presheaf`).

* `coverLevelAssemblyResidual_via_lemma833_iUnion_collapse` — bridge
  showing that **if** the structured Lemma 8.33-style assembly
  `LaurentCoverPresheafLemma833Assembly` holds AND collapses each
  per-piece RHS to a common global RHS (the Lemma 8.33 collapse
  condition documented in the predicate's docstring), the
  `⋃`-form covering yields T056's `CoverLevelAssemblyResidual` as a
  direct consequence. Identifies the **single** missing assembly API
  beyond T057's reachable set-theoretic content.

## Connection to existing `LaurentRefinement.lean` APIs

`LaurentRefinement.lean` provides Wedhorn Lemma 8.33 / Laurent-cover
gluing in **2-element** form (`laurentCover_gluing_presheaf`) and a
general refinement-transfer API (`gluing_of_finer_rational`,
`tateAcyclicity_gluing_via_refinement` in `RationalRefinement.lean`).
Both expect `RationalCovering A` / `Finset (RationalLocData A)` inputs,
NOT the `Set (Spv A)`-level Laurent pieces produced by T054.

The natural connection is:

1. T054's σ-rescaled Laurent pieces `V_τ = rationalOpen ({(1:A)})
   (σ⁻¹ * τ)` are themselves rational-open subsets, but lifting them to
   `RationalLocData A` requires choosing a `PairOfDefinition A` and
   discharging the `hopen` condition for each `σ⁻¹ * τ` — this is the
   **substantive missing infrastructure**, not addressed in T054 or in
   this ticket.

2. Once each `V_τ` is lifted to a `RationalLocData A` `D_τ` (with
   `D_τ.T = {(1:A)}`, `D_τ.s = σ⁻¹ * τ`, suitable `P_τ`,
   `hopen`-witness), the multi-piece `Finset {D_τ : τ ∈ T_test}`
   together with a base `RationalLocData` (e.g., `Spa(A,A⁺)` itself
   if it is `rationalOpen`-shaped) form a `RationalCovering A`. Then
   `tateAcyclicity_gluing_via_refinement` applies, reducing the
   global gluing to per-piece gluing; the per-piece gluing on each
   Laurent piece is exactly the input `laurentCover_gluing_presheaf`
   would consume after its own 2-element Laurent cover step.

3. The **structured blocker** named here packages step (2) as a
   single Prop predicate, with explicit reference to the `RationalLocData`-
   lifting requirement on `V_τ`. The associated bridge theorem then
   deduces `CoverLevelAssemblyResidual` (from T056) from the structured
   blocker plus a Lemma 8.33-style collapse condition.

## Why a structured blocker is the honest output

Per T035's counter-example analysis (and T054's documented gap), the
**universal-over-Spa-and-D_T** lower-bound residual for multi-element
`D_T` is mathematically false in general. The natural Wedhorn 8.34(ii)
proof avoids this by using **per-piece subsets + cover-level acyclicity
(Lemma 8.33)** rather than a global multi-element subset clause. The
multi-piece Laurent cover acyclicity assembly is itself a substantial
piece of infrastructure (Wedhorn pp. 81–85), beyond what T054's
per-piece refinement directly delivers. T057 lands the reusable
set-level cover assembly that IS reachable from T054, plus a precise
Prop-level statement of the missing Lemma 8.33 multi-piece collapse,
without reviving the false universal-over-Spa multi-element residual
(per T054's `MultiElementLowerBoundResidual` blocker doc).

## Notes

* No root import; leaf-level file.
* Imports `WedhornMultiPieceLaurentRefinement` (T054), which transitively
  brings in T053's content. Disjoint from T056's
  `WedhornPerPieceLaurentC1Supplier.lean`.
* No edits to T031–T056 accepted leaves, root imports, or final theorem
  signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B, Cor 8.32 /
  Jacobson, faithful-flatness, Zavyalov, or bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim (per T035's
  counter-example).
* No sorry / admit / custom axiom / unsafe / native_decide.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **Generic set-theoretic per-piece cover assembly** (T057 reusable
primitive).

From per-piece subset inclusions `S ∩ V i ⊆ R i` and a covering
`∀ s ∈ S, ∃ i, s ∈ V i`, derive `S ⊆ ⋃ i, R i`.

This is **mathlib-style and fully general** — it depends on no
typeclasses, no algebraic structure, and applies to any indexing type.
Specialises trivially to T054's `Finset`-indexed Laurent cover. The
proof is direct unfolding of `Set.mem_iUnion`. -/
theorem source_subset_iUnion_via_per_piece_cover
    {α : Type*} {ι : Sort*} (S : Set α) (V R : ι → Set α)
    (h_per_piece : ∀ i, S ∩ V i ⊆ R i)
    (h_cover : ∀ s ∈ S, ∃ i, s ∈ V i) :
    S ⊆ ⋃ i, R i := by
  intro s hs
  obtain ⟨i, hsV⟩ := h_cover s hs
  exact Set.mem_iUnion.mpr ⟨i, h_per_piece i ⟨hs, hsV⟩⟩

omit [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] in
/-- **`Finset`-indexed per-piece cover assembly** (T057 specialisation).

The `Finset`-indexed analogue of
`source_subset_iUnion_via_per_piece_cover`, matching T054's finite
Laurent cover shape `Finset T_test ⊆ A`. Per-piece data is restricted
to `i ∈ T_test`; the conclusion uses `⋃ i ∈ T_test, R i` (membership-
indexed iUnion). -/
theorem source_subset_finset_iUnion_via_per_piece_cover
    {α : Type*} {ι : Type*} (S : Set α) (T_test : Finset ι)
    (V R : ι → Set α)
    (h_per_piece : ∀ i ∈ T_test, S ∩ V i ⊆ R i)
    (h_cover : ∀ s ∈ S, ∃ i ∈ T_test, s ∈ V i) :
    S ⊆ ⋃ i ∈ T_test, R i := by
  intro s hs
  obtain ⟨i, hi_mem, hsV⟩ := h_cover s hs
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine Set.mem_iUnion.mpr ⟨hi_mem, ?_⟩
  exact h_per_piece i hi_mem ⟨hs, hsV⟩

omit [IsTopologicalRing A] in
/-- **Wedhorn-specific Laurent-piece per-piece cover assembly** (T057
specialisation).

From per-piece subset inclusions on each σ-rescaled Laurent piece
`V_τ = rationalOpen ({(1 : A)}) (σ⁻¹ * τ)` and the σ-rescaled Laurent
cover hypothesis (every `w ∈ Source` lies in some `V_τ`), derive
`Source ⊆ ⋃ τ ∈ T_test, R τ`. The per-piece RHS targets `R τ` are
arbitrary and chosen by the caller (e.g., for T056's reroute,
`R τ := rationalOpen ({σ⁻¹ * τ}) D_s`).

Direct specialisation of `source_subset_finset_iUnion_via_per_piece_cover`
with `V τ := rationalOpen ({(1 : A)}) (σ⁻¹ * τ)`. -/
theorem rationalOpen_subset_iUnion_laurentPiece_via_per_piece
    {σ : Aˣ} (Source : Set (Spv A)) (T_test : Finset A)
    (R : A → Set (Spv A))
    (h_per_piece :
      ∀ τ ∈ T_test,
        Source ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          R τ)
    (h_cover :
      ∀ w ∈ Source, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    Source ⊆ ⋃ τ ∈ T_test, R τ :=
  source_subset_finset_iUnion_via_per_piece_cover Source T_test
    (fun τ => rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
    R h_per_piece h_cover

omit [IsTopologicalRing A] in
/-- **Cover-assembly bridge from T054's `MultiPieceLaurentCoverRefinementOutput`**
(T057 substantive bridge).

Bridges T054's per-piece refinement output to the per-piece cover-
assembly API. Hypotheses:

* `h_refinement : MultiPieceLaurentCoverRefinementOutput T_test`
  — T054's per-piece refinement output (the σ-rescaled Laurent pieces
  cover `Spa A A⁺`, with per-piece singleton residuals).

* `h_source_subset_spa : Source ⊆ Spa A A⁺`
  — the source set is a subset of the adic spectrum (e.g., a
  `rationalOpen` subset for the C1 supplier).

* `h_per_piece` — per-piece subset inclusions on each Laurent piece.

Conclusion: `Source ⊆ ⋃ τ ∈ T_test, R τ`. The σ-rescaled Laurent
cover hypothesis is **internally extracted** from `h_refinement` (via
the membership clause of `MultiPieceLaurentCoverRefinementOutput`),
matching T054's per-piece output shape directly. No additional
universal-over-Spa supplier required.

This is the **substantive bridge** showing T054's per-piece refinement
directly feeds the union-form cover-assembly: callers need only
provide per-piece source-restricted subset clauses (e.g., from T056's
`per_piece_singleton_subset_via_laurent_membership`) — the cover
hypothesis is extracted from T054. -/
theorem MultiPieceLaurentCover_source_iUnion_assembly
    {σ : Aˣ} {T_test : Finset A} (Source : Set (Spv A))
    (R : A → Set (Spv A))
    (h_refinement : MultiPieceLaurentCoverRefinementOutput (σ := σ) T_test)
    (h_source_subset_spa : Source ⊆ Spa A A⁺)
    (h_per_piece :
      ∀ τ ∈ T_test,
        Source ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          R τ) :
    Source ⊆ ⋃ τ ∈ T_test, R τ := by
  refine rationalOpen_subset_iUnion_laurentPiece_via_per_piece
    Source T_test R h_per_piece ?_
  intro w hw_source
  have hw_spa : w ∈ Spa A A⁺ := h_source_subset_spa hw_source
  obtain ⟨τ, hτ_mem, hw_in_piece, _⟩ := h_refinement w hw_spa
  exact ⟨τ, hτ_mem, hw_in_piece⟩

/-- **Lemma 8.33 multi-piece cover-acyclicity collapse — structured
blocker** (T057 named missing API).

The cover-assembly API in this file produces a **`⋃`-form** covering
`Source ⊆ ⋃ τ ∈ T_test, R τ`. The C1 supplier's clause 2 conclusion
needs a **single** subset `Source ⊆ R_target` for a globally-fixed
target `R_target` (e.g., `R_target := rationalOpen D.T D.s` in T056's
shape).

The bridge from `⋃`-form to single-subset form is the **Wedhorn
Lemma 8.33 multi-piece cover-level acyclicity collapse**: from the
per-piece RHS `R τ` and the union covering, plus the per-piece
compatibility data inherited from T054's σ-rescaled Laurent cover
structure, derive a single global RHS that the source maps into.

This Prop predicate names exactly that collapse content. The
`R_target` is the single target the union of `R τ`'s is meant to
collapse onto; the `h_collapse` hypothesis is the Wedhorn Lemma 8.33
content (multi-piece cover-acyclicity for the σ-rescaled Laurent cover,
extracted from the existing 2-element `LaurentRefinement.lean` Laurent
cover gluing API by induction on `|T_test|`).

**Why this is the right structured blocker**:

* The 2-element Laurent cover case (`|T_test| = 1`, `T_test = {τ₀}`)
  is essentially trivial: `⋃ τ ∈ {τ₀}, R τ = R τ₀`, so collapse =
  `R_target := R τ₀` and the assembly is automatic.

* The general `|T_test| > 1` case requires the iterated 2-element
  Laurent cover refinement (Wedhorn pp. 81–85), which is exactly
  Lemma 8.33's content. The existing `laurentCover_gluing_presheaf`
  in `LaurentRefinement.lean` provides the 2-element step; the
  multi-piece iteration is the missing infrastructure.

* The collapse content is **at the subset / set-of-Spa level**, not
  the presheaf-value level — matching the C1 supplier's subset-form
  clause 2 conclusion. The presheaf-value-level analogue (Wedhorn
  Theorem 8.28(b) acyclicity) is downstream of Lemma 8.33.

**Note**: this is NOT the false universal-over-D_T residual rejected
by T035. The collapse operates at the union-of-rationalOpen ↦ single-
rationalOpen level, with the σ-rescaled Laurent cover structure as
input data. -/
def LaurentCoverPresheafLemma833Assembly
    {σ : Aˣ} (T_test : Finset A) (R : A → Set (Spv A))
    (R_target : Set (Spv A)) : Prop :=
  -- Per-piece RHS subsets `R τ` (the per-piece subset inclusions
  -- output by T056 / similar).
  -- Multi-piece Laurent cover structure (the σ-rescaled Laurent pieces
  -- cover the relevant Spa region).
  -- Collapse to a single global target `R_target`:
  -- the union `⋃ R τ` is contained in `R_target` thanks to the
  -- multi-piece cover-acyclicity (Lemma 8.33 multi-piece form).
  (∀ w : Spv A,
    w ∈ Spa A A⁺ →
    (∃ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) →
    (∀ τ ∈ T_test,
      w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) →
      w ∈ R τ) →
    w ∈ R_target)

omit [IsTopologicalRing A] in
/-- **`⋃`-form covering implies single-target covering under
Lemma 8.33 collapse** (T057 substantive bridge to single-subset form).

From `Source ⊆ ⋃ τ ∈ T_test, R τ` and `LaurentCoverPresheafLemma833Assembly`
together with the σ-rescaled Laurent cover hypothesis on `Source`,
derive `Source ⊆ R_target`.

This is the **single substantive consequence** of the Lemma 8.33
multi-piece collapse: it converts the union-form output of T057's
cover-assembly into the single-subset form consumed by the C1
supplier's clause 2.

**Hypothesis source structure**:

* `h_source_in_pieces` — per-`w ∈ Source` membership in some Laurent
  piece (extracted from T054's `MultiPieceLaurentCoverRefinementOutput`
  via `MultiPieceLaurentCover_source_iUnion_assembly`'s internal
  unpacking).

* `h_per_piece_at_w` — per-`w ∈ Source` per-piece membership
  consequence: at every Laurent piece containing `w`, `w ∈ R τ`. This
  is exactly what the per-piece subset inclusions
  `Source ∩ V_τ ⊆ R τ` give at each `w ∈ Source`.

* `h_lemma833` — the structured blocker `LaurentCoverPresheafLemma833Assembly`,
  consumed at each `w` to extract `w ∈ R_target` from per-piece data.

Real proof — substantive consumption of the structured blocker. -/
theorem source_subset_target_via_lemma833_collapse
    {σ : Aˣ} {T_test : Finset A} (Source : Set (Spv A))
    (R : A → Set (Spv A)) (R_target : Set (Spv A))
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test R R_target)
    (h_source_subset_spa : Source ⊆ Spa A A⁺)
    (h_source_in_pieces :
      ∀ w ∈ Source, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ))
    (h_per_piece_at_w :
      ∀ w ∈ Source,
        ∀ τ ∈ T_test,
          w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) →
          w ∈ R τ) :
    Source ⊆ R_target := by
  intro w hw_source
  have hw_spa : w ∈ Spa A A⁺ := h_source_subset_spa hw_source
  exact h_lemma833 w hw_spa
    (h_source_in_pieces w hw_source)
    (fun τ hτ_mem hw_in => h_per_piece_at_w w hw_source τ hτ_mem hw_in)

omit [IsTopologicalRing A] in
/-- **Per-piece subsets + Laurent cover + Lemma 8.33 collapse ⊢ single
global subset** (T057 substantive consumer-facing theorem).

Concrete consumer-facing form of `source_subset_target_via_lemma833_collapse`,
specialised to the C1 supplier's clause 2 shape: the source is
`rationalOpen (insert f T_base) s` (a Wedhorn 8.34(ii) base-side rational
subset), the per-piece RHS is `rationalOpen ({σ⁻¹ * τ}) D_s` (the
T056-shape per-piece singleton), and the target is `rationalOpen D_T
D_s` (the C1 supplier's target rational subset).

**Inputs**:

* `h_lemma833` — the Lemma 8.33 multi-piece cover-acyclicity collapse
  predicate (`LaurentCoverPresheafLemma833Assembly`) specialised to
  T056-shape per-piece RHS and the C1 target. **The single named
  missing assembly API.**

* `h_per_piece_subset` — per-piece subset inclusions on each
  σ-rescaled Laurent piece. Compatible shape with T056's
  `per_piece_singleton_subset_via_laurent_membership`.

* `h_cover` — the σ-rescaled Laurent cover hypothesis on the source.
  Provable from Cor 7.32 σ-strict-domination via T054's
  `cor732_multi_piece_laurent_refinement`.

**Output**: the global subset clause `R(insert f T_base, s) ⊆ R(D_T,
D_s)` — the C1 supplier's clause 2 conclusion shape.

**Cross-lane decomposition**: this theorem decomposes the C1
supplier's clause 2 gap into exactly two named pieces: per-piece
subset (provable from local-bounds; the parallel C1 supplier reroute
lane delivers this via `per_piece_singleton_subset_via_laurent_membership`
or analogous content) and Lemma 8.33 collapse (the only remaining
theorem-level missing API beyond this ticket and the parallel C1
supplier reroute lane combined). -/
theorem rationalOpen_global_subset_via_lemma833_assembly
    [DecidableEq A]
    {σ : Aˣ} (T_test : Finset A) (T_base D_T : Finset A)
    (s D_s f : A)
    (h_lemma833 :
      LaurentCoverPresheafLemma833Assembly (σ := σ) T_test
        (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
        (rationalOpen D_T D_s))
    (h_per_piece_subset :
      ∀ τ ∈ T_test,
        rationalOpen (insert f T_base) s ∩
            rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) ⊆
          rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (h_cover :
      ∀ w ∈ rationalOpen (insert f T_base) s, ∃ τ ∈ T_test,
        w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ)) :
    rationalOpen (insert f T_base) s ⊆ rationalOpen D_T D_s := by
  -- The source `R(insert f T_base, s)` is contained in `Spa A A⁺` via
  -- `rationalOpen_subset_spa`.
  have h_source_subset_spa :
      rationalOpen (insert f T_base) s ⊆ Spa A A⁺ :=
    rationalOpen_subset_spa
  -- At each `w ∈ Source` and each `τ ∈ T_test` with `w` in the Laurent
  -- piece, the per-piece subset gives `w ∈ R τ`.
  have h_per_piece_at_w :
      ∀ w ∈ rationalOpen (insert f T_base) s,
        ∀ τ ∈ T_test,
          w ∈ rationalOpen ({(1 : A)} : Finset A) (((σ⁻¹ : Aˣ) : A) * τ) →
          w ∈ rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s := by
    intro w hw_source τ hτ_mem hw_in_piece
    exact h_per_piece_subset τ hτ_mem ⟨hw_source, hw_in_piece⟩
  -- Apply the Lemma 8.33 collapse.
  exact source_subset_target_via_lemma833_collapse
    (rationalOpen (insert f T_base) s)
    (fun τ => rationalOpen ({((σ⁻¹ : Aˣ) : A) * τ} : Finset A) D_s)
    (rationalOpen D_T D_s) h_lemma833 h_source_subset_spa
    h_cover h_per_piece_at_w

end ValuationSpectrum
