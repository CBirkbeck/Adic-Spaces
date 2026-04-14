# Development Plan: Tate Acyclicity (non-discrete case) Sessions A + B

## Goal

Make `tateAcyclicity` sorry-free for the non-discrete strongly noetherian Tate case.
Specifically, execute Sessions A and B from `docs/plans/2026-04-14-tate-acyclicity-finish-plan.md`:

- **Session A**: non-open-prime Spa-point → Cor 8.32 → separation sorry-free (~265 lines)
- **Session B**: 5 Route B bridges → `laurentCover_gluing_presheaf` sorry-free (~200 lines)

Both together deliver separation + Laurent-cover gluing; Session C (Lemma 8.34 + final
assembly) would then finalise `tateAcyclicity` in a follow-up session.

## References

- `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — main Wedhorn-route plan
- `docs/plans/2026-04-14-tate-acyclicity-finish-plan.md` — concrete dependency map
- Wedhorn, *Adic Spaces* lecture notes (1910.05934v1.pdf), §8 + Lemma 7.44/7.45

## Mathlib Inventory

| Concept | Status | Action |
|---------|--------|--------|
| `presheafValueTateQuotientEquiv` (Phase 2 iso) | `TopologyComparison.lean:831` | USE as building block |
| `tateQuotientToPresheafHom_isHomeomorph` | `TopologyComparison.lean:2266` | USE for topological iso |
| `Lemma745.exists_valuation_extension` | `Lemma745.lean:337` | USE for Spa-point at non-open prime |
| `LaurentCover.row3_exact` (general case) | `LaurentCoverExact.lean:1560` | USE in bridges via instantiation at `presheafValue D₀` |
| `flat_quotient_oneSubfX_general` | `TateAlgebra.lean` | USE for flatness of presheafValue |
| `laurentCover_gluing_presheaf_viaRow3` | `LaurentRefinement.lean:588` | USE as sorry-free Route B consumer |

## File Structure

- `Adic spaces/StructureSheaf.lean` — Spa-point at non-open prime, Cor 8.32, rewrite empty separation
- `Adic spaces/PresheafTateStructure.lean` — rewrite `restrictionMapHom_injective` via Cor 8.32
- `Adic spaces/LaurentRefinement.lean` — rewrite `tateAcyclicity` Part 1, fill 5 Route B bridges

## Dependency Graph

```
 T-A1 Spa-point non-open prime   T-B1 laurentMinusBridge   T-B2 laurentPlusBridge
          │                            │                          │
          ▼                            ▼                          ▼
 T-A2 Cor 8.32 faithful flat   T-B3 minusBridge_restrictionMap   T-B4 plusBridge_restrictionMap
          │
          ▼                            ├────────────┬──────────────┘
 T-A3 restrictionMapHom_injective      ▼            ▼
          │                    T-B5 delta_eq_zero_of_compat
          ▼
 T-A4 tateAcyclicity Part 1 rewrite
          │
          ▼
 T-A5 hasSeparation empty branch
```

Parallel: {A1, B1, B2}, then {A2, B3, B4}, then {A3, A4, A5, B5}.

## Generality Decisions

- Keep all theorems over `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]` (no `[IsDomain A]` unless essential).
- `IsDomain A` remains an assumption on `tateAcyclicity` (current signature) — do not weaken.
- Route B bridges are for `RationalLocData` at arbitrary base `D₀`. Phase 2 iso hypotheses are discharged via strongly-noetherian-Tate dispatches in the implementation.
