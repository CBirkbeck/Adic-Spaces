# Ticket Board — Close tateAcyclicity Part 1 via Cor 8.32 reroute

## Summary
- Total: 3 tickets (renumbered 2026-04-16).
- Open: 3 | In Progress: 0 | Done: 0.
- See `plan.md` for strategy.

## Tickets

### [T-WEDHORN-1] productRestriction_injective_tate — Cor 8.32 discharge
- **Status**: open
- **File**: `Adic spaces/Cor832.lean`
- **Depends on**: Cor 8.32 abstract (done), Example 6.38 iso (done), Lemma 7.45 (done)
- **Parallel**: no (blocks T-WEDHORN-2)
- **Description**: Prove `productRestriction_injective_tate`: under `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]` + `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` + `(C : RationalCovering A) hne`, the product restriction is injective. Discharges the two conditional hypotheses of existing `tateAcyclicity_zero_kernel_of_flat_and_lifting`:
  - `flat_over_base`: each `presheafValue C.base → presheafValue D` is flat. Use Example 6.38 iso + Lemma 8.31 flatness of A⟨X⟩ quotients + appropriate flat-composition.
  - `hSpa_surj`: Spec surjection from product to base. Use `exists_spa_point_with_supp_ge_of_prime` (StandardCover.lean, already proved) + valuation-restriction to cover piece.
- **Est. lines**: 150-250.
- **Risk**: hb_D (invS power-bounded) and other Example 6.38 iso hypotheses may not discharge cleanly. If not, may need to relax via partial approach or find a direct route.

### [T-WEDHORN-2] Reroute tateAcyclicity Part 1
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:3688-3696`
- **Depends on**: T-WEDHORN-1
- **Parallel**: no
- **Description**: Replace the `obtain ⟨D, hD⟩ := hne; exact restrictionMapHom_injective C.base D ...` call at line 3695 with a direct call to `productRestriction_injective_tate` (from T-WEDHORN-1). The hypothesis `hx : ∀ D ∈ C.covers, restriction x = 0` is exactly what the new theorem takes.
- **Est. lines**: 10-20 (mostly deletion + rename).

### [T-WEDHORN-3] (optional) Direct close of restrictionMapHom_injective
- **Status**: open
- **File**: `Adic spaces/PresheafTateStructure.lean:1238`
- **Depends on**: T-WEDHORN-1 (or independent via different route)
- **Parallel**: yes (independent of T-WEDHORN-2)
- **Description**: Close single-map injectivity directly. Possible routes:
  - (a) Via product injectivity + singleton cover extension.
  - (b) Via explicit NZD argument: prove `D.s` is a non-zero-divisor in `presheafValue D₀`.
  - (c) Via flat localization + Wedhorn Prop 8.15 structure.
- **Est. lines**: 100-200.
- **Note**: NOT required for tateAcyclicity Part 1 closure (T-WEDHORN-2 bypasses it). This is cleanup.

## Execution Plan

**This session**:
1. **T-WEDHORN-1** (CRITICAL) — 150-250 lines. Dispatch focused agent.
2. **T-WEDHORN-2** (QUICK) — after T-WEDHORN-1 lands, 10-20 lines.
3. Verify tateAcyclicity Part 1 sorry-free (would still show `sorryAx` via remaining Part 2).

**T-WEDHORN-3** deferred to future session.
