# Ticket Board — `tateAcyclicity` Completion

## Summary

| Status | Count |
|---|---|
| Open | 4 |
| In Progress | 0 |
| Blocked | 3 |
| Done | many (see commits) |

See `plan.md` for strategy. Updated 2026-04-16.

## Tate-core sorries (critical path)

### [T-OV-1] Bivariate Example 6.38 primitive — `evalBivariateHom`

- **Status**: open
- **Blocker for**: `laurentOverlapBridge_exists_compatible`
  (`LaurentRefinement.lean:3173`)
- **File(s)**: new section in `Adic spaces/Example638.lean` or a new file
  `Adic spaces/LaurentOverlap.lean`.
- **Description**: build a `RingEquiv presheafValue(overlap_B b) (B₁₂_gen b)`
  over an arbitrary complete strongly noetherian Tate base `B` and
  `b ∈ B` power-bounded (with `b⁻¹` also power-bounded after localization).
  This is the bivariate analog of `example638Plus_equiv` /
  `example638Minus_equiv`.
- **Est. lines**: ~500.
- **Proof approach**:
  - Define `overlap_B b : RationalLocData B` with `s = b, T = {1, b}` (or
    equivalent bivariate rational data).
  - Define `evalBivariateHom : LaurentTateAlgebra B →+* presheafValue(overlap_B b)`
    sending `ζ ↦ coeRingHom_B b` and `ζ⁻¹ ↦ coeRingHom_B b⁻¹`.
  - Show it factors through `laurentFSubZetaIdeal b`.
  - Build backward via dense algebraic localization + Completion extension.
  - Round trips via `Completion.ext'`.
  - Conclude the iso.

### [T-OVERLAP-COMPAT] Close `laurentOverlapBridge_exists_compatible`

- **Status**: open (blocked on T-OV-1)
- **File**: `Adic spaces/LaurentRefinement.lean:3173`
- **Description**: produce the compatible bridge `τ₁₂` satisfying
  `LaurentOverlapBridgeCompatible`. Reduces to T-OV-1 via iterated
  rational identification (Lemma 2.13) at base `B := presheafValue D₀`.
- **Est. lines**: ~80 once T-OV-1 is available.
- **Downstream**: closes `laurentCover_gluing_presheaf` transitively.

### [T-ACYC-PART2] `tateAcyclicity` Part 2 (gluing) assembly

- **Status**: open (blocked on T-OVERLAP-COMPAT + Wedhorn Prop 7.14 content)
- **File**: `Adic spaces/LaurentRefinement.lean:3737`
- **Description**: with `laurentCover_gluing_presheaf` sorry-free, assemble
  Part 2 via `tateAcyclicity_gluing_via_refinement` +
  `refines_by_standard_cover` + Laurent-cover induction on standard-cover
  size. Requires `hZavyalov` (Wedhorn Prop 7.14) to be available
  unconditionally.
- **Est. lines**: ~50 after both prerequisites.

### [T-INJ-1] `restrictionMapHom_injective` — Part 1 closer

- **Status**: open (two competing routes, both with hard blockers)
- **File**: `Adic spaces/PresheafTateStructure.lean:1322`
- **Blocker for**: `tateAcyclicity` Part 1 (separation)
- **Description**: prove `restrictionMapHom D₀ D h` is injective.
- **Route A (algebraic NZD)**: show `D.s` is NZD in `A⟨X'⟩/(1-D₀.s·X')`
  (source-side quotient). Reviewer note says this may be as hard as
  Route B.
- **Route B (via Cor 8.32)**: use
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper` +
  T-IDEAL-1 (DONE) + T-IDEAL-2 (BLOCKED on Bourbaki CA III §2.8).
- **Est. lines**: ~30 once either blocker discharged.

## Blocked tickets (external infrastructure needed)

### [T-IDEAL-2] Closedness of `Ideal.map algebraMap p` — BLOCKED

- **Status**: blocked
- **Blocker**: Bourbaki CA III §2.8 (`Submodule.isClosed_of_fg` in complete
  T2 linearly-topologized rings) — not in Mathlib.
- **Description**: for `p` prime of `A` with `D.s ∉ p`,
  `Ideal.map (algebraMap A (Loc.Away D.s)) p` is closed in `Loc.Away D.s`.
- **Unlocks**: alternative route to T-INJ-1 via
  `coeRingHom_preserves_proper`.
- **Est. lines**: ~500-800 (including Bourbaki dependencies).

### [T-NULL-7] Wedhorn Prop 7.14 (adic Nullstellensatz) — NOT STARTED

- **Status**: blocked / not started
- **Description**: close `hZavyalov` hypothesis in
  `refines_by_standard_cover` unconditionally.
- **Unlocks**: clean Part 2 closing via standard-cover reduction.
- **Est. lines**: ~300+.

### [T-BAIRE] `restrictionMap_isLocalization` / sigma surj — NOT STARTED

- **Status**: not on critical path for the Route-B closure
- **File**: `Adic spaces/PresheafTateStructure.lean:1208`
- **Description**: Baire category argument for the sigma surjection
  (Wedhorn Prop 8.15).
- **Est. lines**: ~200+.

## Done (recent)

- T-IDEAL-1: `one_mem_closure_coeRingHom_image` — topological approximation
  (Cor832.lean:1289).
- Cor 8.32 abstract framework (`productRestriction_injective_of_flat_and_lifting`
  + downstream reductions).
- T-NULL-0/0a/1: Spa / Spv compactness + Cor 7.32.
- Q3-STEP2/2A/2C/2D: Wedhorn 2.13 iterated rational identification.
- T-PLUS-FWD-PB, T-MINUS-FWD-PB, T-PLUS-BWD-PB, T-MINUS-BWD-PB: all
  power-boundedness obligations for the iterated-rational forward/backward
  locHoms.
- T-INJ-PROP618 (Wedhorn Prop 6.18): unconditional
  `tateQuotientToPresheafHom_continuous_of_tate`.
- T-INJ-NZD: `mk(D₀.s)` is unit in `A⟨X⟩/(1-D.s·X)` (half of T-INJ-1
  Route A).
- T-WEDHORN-1: `productRestriction_injective_tate` packaging.
- Example 6.38 generic (`example638Plus_equiv`, `example638Minus_equiv`)
  over arbitrary complete strongly noetherian Tate base.
- Route-B bridges (`laurentPlusBridge`, `laurentMinusBridge` + their
  `_restrictionMap` companions).
- R1 standard-cover reduction (scaffold; `hZavyalov` hypothesis remains).

## Suggested execution order (next session[s])

1. **T-OV-1 / T-OVERLAP-COMPAT** (single-focus session): builds the
   bivariate primitive, closes the overlap bridge, which cascades to
   `laurentCover_gluing_presheaf` being sorry-free.
2. **T-NULL-7** (Prop 7.14) in parallel: independent work unblocking Part 2.
3. Post both: T-ACYC-PART2 + T-INJ-1 in assembly sessions.
