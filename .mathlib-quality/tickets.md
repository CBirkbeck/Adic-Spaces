# Ticket Board — Tate Acyclicity Sessions A+B

## Summary
- Total: 10 tickets | Open: 7 | In Progress: 0 | Done: 0 | Blocked: 3
- 2026-04-14 Wave 1 dispatch: T-A1, T-B1, T-B2 all returned BLOCKED with concrete diagnoses
- Peak parallel capacity: 3 workers (Wave 1: A1 || B1 || B2)
- Target deliverable: separation sorry-free end-to-end + `laurentCover_gluing_presheaf` sorry-free

## Wave 1 dispatch findings (2026-04-14)

**All three independent tickets blocked on missing upstream infrastructure.**

| Ticket | Status | Concrete blocker |
|---|---|---|
| T-A1 | BLOCKED | `completedLocSubring_isAdic` (Presheaf.lean:421) + `completedLocSubring_isAdicComplete` (Presheaf.lean:493) both have unfilled sorries. Once filled, T-A1 closes in ~5 lines. |
| T-B1 | BLOCKED | No `TateAlgebra` coefficient base-change along `D₀.canonicalMap`; no unit-rescaling iso for `(1 - u·c·X)` quotients; 5 Phase 2 iso hypotheses not discharged at `laurentMinusDatum`. ~200 lines, multi-file. |
| T-B2 | BLOCKED | No non-discrete `TateAlgebra.quotientFSubXEquiv` (Mathlib lacks TateAlgebra; existing version is `[DiscreteTopology]`-only). Phase 2 iso hypotheses not discharged at plus datum. Spans 4-6 files. |

**Implication:** Sessions A and B are not single-session deliverables given current upstream gaps. Both require prior infrastructure work (T-A1's blockers in `Presheaf.lean`; T-B1/B2's blockers across `TateAlgebra.lean` + `TopologyComparison.lean`). Recommend opening dedicated infrastructure-first sessions before retrying Sessions A/B.

## New tickets surfaced by Wave 1 investigation

### [INFRA-1] Fill `completedLocSubring_isAdic`
- **Status**: open
- **File**: `Adic spaces/Presheaf.lean:421`
- **Depends on**: nothing (uses existing `locSubring_topology_eq_adic`)
- **Estimated**: ~50 lines
- **Unblocks**: T-A1, T-A5, Cor 8.32 chain

### [INFRA-2] Fill `completedLocSubring_isAdicComplete`
- **Status**: open
- **File**: `Adic spaces/Presheaf.lean:493`
- **Depends on**: INFRA-1 + `AdicCompletionBridge.adicAbstractCompletion`
- **Estimated**: ~80 lines
- **Unblocks**: same as INFRA-1

### [INFRA-3] Non-discrete `TateAlgebra.quotientFSubXEquiv`
- **Status**: open
- **File**: `Adic spaces/TateAlgebra.lean` (extend existing)
- **Depends on**: regularity of `f - X` in non-domain bases
- **Estimated**: ~150 lines
- **Unblocks**: T-B2

### [INFRA-4] Phase 2 iso hypothesis dispatcher for sno Tate
- **Status**: open
- **File**: `Adic spaces/TopologyComparison.lean` (extend) + `StructureSheaf.lean`
- **Depends on**: nothing major
- **Estimated**: ~100-200 lines
- **Unblocks**: T-B1 + T-B2 (eliminates the 5-hypothesis discharge per call)

## Tickets

### [T-A1] Fill `exists_spa_point_in_rationalOpen` non-open prime case
- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:682`
- **Depends on**: none
- **Parallel**: yes (Wave 1)
- **Description**: For a non-open prime `p` of A (Tate, T2, NonarchimedeanRing) with `D.s ∉ p`, construct a continuous valuation `v ∈ rationalOpen D.T D.s` with `p ≤ v.supp`. Use Wedhorn Lemma 7.44(3) via `Lemma745.exists_valuation_extension`: extend the trivial valuation on `A/p` (viewed through completion) to A, pulling back through the quotient.
- **Sketch**:
  1. Build quotient `A/p` with induced topology; complete to `Completion(A/p)`.
  2. `Completion(A/p)` is a Tate ring; has a natural non-trivial valuation (via Tate unit).
  3. Compose: A → A/p → Completion(A/p) → valuation.
  4. Verify continuity (small elements go to small valuations via completion).
  5. Verify `v ∈ rationalOpen D.T D.s`: `v(D.s) > 0` since D.s ∉ p; `v(t) ≤ v(D.s)` for t ∈ D.T (uses that rational subset definition places T power-bounded wrt D.s).
  6. Verify `p ≤ v.supp`: a ∈ p ⟹ image of a in A/p is 0 ⟹ v(a) = 0.
- **Est. lines**: ~80-120
- **Key infra used**: `Lemma745.exists_valuation_extension`, `ofValuation`, `isContinuous_ofValuation_of`
- **Naming**: keep `exists_spa_point_in_rationalOpen`.

### [T-A2] Prove Cor 8.32 — faithful flatness of product restriction
- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean` (new section, or inline near `presheafValue_flat_of_tateQuotient`)
- **Depends on**: T-A1
- **Parallel**: no (wave 2 after T-A1)
- **Description**: Show that for a `RationalCovering A`, the product restriction `presheafValue C.base → ∏ presheafValue D` is faithfully flat (hence injective). Uses individual flatness (from `presheafValue_flat_of_tateQuotient`) + the radical argument: no prime of `presheafValue C.base` is in kernel of all restrictions (via Spa-point construction from T-A1 pulled back through `canonicalMap`).
- **Sketch**:
  1. Each `presheafValue D` flat over A via Phase 2 iso.
  2. Product of flat A-modules is A-flat.
  3. For faithful flatness: `∀ prime q of presheafValue C.base, exists D such that canonicalMap(D.s) ∉ q after pullback`. Use Spa-point radical argument via `base_s_in_annihilator_radical_of_covering` + T-A1.
  4. Faithful flatness ⟹ injective.
- **Est. lines**: ~150
- **Key lemma produced**: `productRestriction_faithfullyFlat` (or `_injective_viaFaithfulFlatness`).

### [T-A3] Rewrite `restrictionMapHom_injective` via Cor 8.32
- **Status**: open
- **File**: `Adic spaces/PresheafTateStructure.lean:1322`
- **Depends on**: T-A2
- **Parallel**: no
- **Description**: Replace the `sorry` with a proof using Cor 8.32. Strategy: consider the trivial cover by D itself (single-element cover of D₀ by D). Apply Cor 8.32 to get injectivity of `presheafValue D₀ → presheafValue D`.
- **Est. lines**: ~20

### [T-A4] Rewrite `tateAcyclicity` Part 1 via Cor 8.32 product injectivity
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:664-667`
- **Depends on**: T-A2 (or T-A3)
- **Parallel**: no
- **Description**: Currently uses `restrictionMapHom_injective` for a single D. Replace with product-injectivity from Cor 8.32: `productRestriction` injective ⟹ element with all-zero restrictions is zero.
- **Est. lines**: ~15

### [T-A5] Fill `rationalCovering_hasSeparation` empty-cover branch
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:741`
- **Depends on**: T-A1 (uses the non-open-prime Spa-point)
- **Parallel**: yes with {T-A3, T-A4} after T-A1/T-A2 done
- **Description**: When `C.covers = ∅` and `C.base.s ≠ 0`, derive contradiction: for A a domain, `(0)` is prime with `s ∉ (0)`; use T-A1 to construct Spa-point `v ∈ rationalOpen C.base.T C.base.s`; apply `C.hcover v` to get `D ∈ ∅`, contradiction. Hence presheafValue is effectively trivial and x = y.
- **Est. lines**: ~25

### [T-B1] Fill `laurentMinusBridge`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:436` (`noncomputable def laurentMinusBridge`)
- **Depends on**: none (Phase 2 iso is done)
- **Parallel**: yes (Wave 1)
- **Description**: Construct the RingEquiv `presheafValue (laurentMinusDatum D₀ f) ≃+* LaurentCover.B₂_gen (D₀.canonicalMap f)`. Recipe:
  1. Apply `presheafValueTateQuotientEquiv` (or `presheafValueCanonicalQuotientEquiv`) at the minus datum (s = D₀.s · f): gives `presheafValue(minus) ≃+* A⟨X⟩/(1 - (D₀.s·f)·X)`.
  2. Base-change coefficients from A to `presheafValue D₀` via `D₀.canonicalMap`: yields a map from `A⟨X⟩/(1-(D₀.s·f)X)` to `TateAlgebra(presheafValue D₀)/(1 - canonicalMap(D₀.s·f)·X)`. Since `canonicalMap(D₀.s)` is a unit in `presheafValue D₀`, change of variable `X ↦ canonicalMap(D₀.s)·X'` identifies this with `TateAlgebra(presheafValue D₀)/(1 - canonicalMap(f)·X')` = `B₂_gen(canonicalMap f)`.
  3. Compose.
- **Est. lines**: ~80-100
- **Note**: Hypothesis discharge for `presheafValueTateQuotientEquiv` (5 hypotheses) happens inside the def. If infrastructure for this dispatch is missing, extract as sub-ticket.

### [T-B2] Fill `laurentPlusBridge`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:419` (`noncomputable def laurentPlusBridge`)
- **Depends on**: none
- **Parallel**: yes (Wave 1)
- **Description**: Construct `presheafValue (laurentPlusDatum D₀ f) ≃+* LaurentCover.B₁_gen (D₀.canonicalMap f)`. Recipe:
  1. Plus datum has `s = D₀.s` (same as base). `presheafValue(plus) ≃+* A⟨X⟩/(1-D₀.s·X)` via Phase 2 iso (with plus's T extended by f).
  2. In `A⟨X⟩/(1-D₀.s·X)`, `X = 1/D₀.s` (since `D₀.s·X = 1`). This quotient is ≃ `Localization.Away D₀.s` via `tateQuotientOneSubfXEquiv` — BUT that requires discrete. For complete non-discrete, use Phase 2 iso + the fact that `canonicalMap(D₀.s)` is a unit in presheafValue D₀.
  3. Target `B₁_gen(canonicalMap f) = TateAlgebra(presheafValue D₀)/(canonicalMap f - X)` evaluates X at canonicalMap f. Construct a ring hom that identifies `1/D₀.s` in source with the appropriate element.
  4. Approach: use the T-extension property — adding `f` to `T` makes `f/D₀.s` part of the ring of definition. In the completion with plus topology, `f/D₀.s` is in `A°`; mapping `X := canonicalMap(f)` satisfies `canonicalMap(f) - X = 0` ⟹ B₁_gen relation.
- **Est. lines**: ~80-120
- **Note**: This is more intricate than B1 because it identifies the T-extension topology with the quotient-at-f structure. May need a helper lemma.

### [T-B3] Fill `laurentPlusBridge_restrictionMap`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:446`
- **Depends on**: T-B2
- **Parallel**: yes with {T-B4} after B2
- **Description**: Prove `laurentPlusBridge D₀ f ∘ restrictionMap D₀ (plus) hplus = π₁ ∘ epsilonHom_gen (canonicalMap f)`. This is a compatibility of the bridge with canonical maps. Should follow from definition of `laurentPlusBridge` via `presheafValueTateQuotientEquiv_canonicalMap` + chase.
- **Est. lines**: ~30

### [T-B4] Fill `laurentMinusBridge_restrictionMap`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:460`
- **Depends on**: T-B1
- **Parallel**: yes with {T-B3} after B1
- **Description**: Prove `laurentMinusBridge D₀ f ∘ restrictionMap D₀ (minus) hminus = π₂ ∘ epsilonHom_gen (canonicalMap f)`. Same shape as T-B3 but for minus.
- **Est. lines**: ~30

### [T-B5] Fill `laurentBridge_delta_eq_zero_of_compat`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:480`
- **Depends on**: T-B1, T-B2
- **Parallel**: yes after both bridges done
- **Description**: Prove that compatibility of `(uplus, uminus)` on common refinements implies `deltaMap_gen(τ+ uplus, τ- uminus) = 0`. Uses: bridge definitions + the overlap refinement `D_overlap` with `s = D₀.s · f` and T containing both plus's T and minus's T; apply `hcompat` at `D_overlap`; transport via the bridges.
- **Est. lines**: ~40

## Execution Plan

### Wave 1 (parallel): T-A1, T-B1, T-B2
Dispatch three workers simultaneously on independent tickets. Each uses `lean4:lean4-sorry-filler-deep` for focused filling.

### Wave 2 (after Wave 1): T-A2, T-B3, T-B4
- T-A2 depends on T-A1 being done.
- T-B3 depends on T-B2 being done.
- T-B4 depends on T-B1 being done.

### Wave 3 (after Wave 2): T-A3, T-A4, T-A5, T-B5
- T-A3, T-A4, T-A5 depend on T-A2.
- T-B5 depends on T-B1 and T-B2 (ready as soon as Wave 1 done, can overlap with Wave 2).
