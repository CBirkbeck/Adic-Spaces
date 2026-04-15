# Development Plan: Close the 10 remaining sorries on `tateAcyclicity` path

## Goal

Make `ValuationSpectrum.tateAcyclicity` (`Adic spaces/LaurentRefinement.lean:2692`)
sorry-free in the strongly noetherian Tate setting by closing all 10 remaining
sorries on its transitive dependency path.

## Target theorem (Lean)

```lean
theorem tateAcyclicity
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    -- Part 1: Zero kernel (separation)
    (∀ x : presheafValue C.base, ... → x = 0) ∧
    -- Part 2: Gluing
    (∀ f : ∀ D : ↥C.covers, presheafValue D.1, ... → ∃ x, ...)
```

## References

- **Wedhorn, *Adic Spaces***:
  - Theorem 8.28(b) — Tate acyclicity (the goal).
  - Prop 7.14 / Lemma 7.44 — Nullstellensatz for Spa.
  - Lemma 7.45 — non-open-prime Spa-point via completion.
  - Prop 8.2 — continuity of restriction map between rational localizations.
  - Example 6.38 — `A⟨X⟩/(1−sX) ≃ 𝒪_X(R(1/s))` (and its plus/Laurent analogs).
  - Lemma 2.13 / Prop 8.7 — iterated rational localizations.
  - Cor 8.32 (retired) — faithful flatness of product restriction.
- **Zavyalov, §2–3** — standard-cover reduction.
- Project memory: `project_T001_completion_route.md` — Bourbaki CA III §2.8 blocker.

## The 10 target sorries

| # | Ticket | Sorry location | Dependencies |
|---|---|---|---|
| 1 | T-ACYC-PART2 | `LaurentRefinement.lean:2758` (Part 2 gluing) | T-NULL, T-CONT-* (via laurentCover_gluing_presheaf), T-OVERLAP |
| 2 | T-INJ-REROUTE | `PresheafTateStructure.lean:1177` (restrictionMapHom_injective) | T-SEP-NEW (new lemma) |
| 3 | T-NULL-EMPTY | `StandardCover.lean:223` (empty covers edge) | Statement fix (add Nonempty hypothesis) |
| 4 | T-NULL-MAIN | `StandardCover.lean:259` (genuine Nullstellensatz) | Lemma 7.44 / 7.45 (existing) |
| 5 | T-CONT-PLUS-FWD | `LaurentRefinement.lean:743` (plus forward cont.) | Wedhorn Prop 8.2 for canonicalMap |
| 6 | T-CONT-PLUS-BWD | `LaurentRefinement.lean:753` (plus backward cont.) | restrictionMapHom continuity |
| 7 | T-PLUS-ROUND | `LaurentRefinement.lean:894` (plus forward∘backward=id) | Density of canonicalMap A in B |
| 8 | T-CONT-MINUS-FWD | `LaurentRefinement.lean:976` (minus forward cont.) | Wedhorn Prop 8.2 for base change |
| 9 | T-CONT-MINUS-BWD | `LaurentRefinement.lean:986` (minus backward cont.) | restrictionMapHom continuity |
| 12 | T-OVERLAP | `LaurentRefinement.lean:2151` (Laurent overlap bridge compatible) | Bivariate `evalHomBounded` for LaurentTateAlgebra |

Items 10 and 11 (the `_restrictionMap_canonicalMap` atomic sub-sorries) were
closed during the 2026-04-15 session.

## Dependency graph

```
T-NULL-EMPTY (statement fix) ──┐
                               │
T-NULL-MAIN (Wedhorn 7.44) ────┴─→ StandardCover.refines_by_standard_cover CLOSED
                                                │
T-CONT-PLUS-FWD ──┐                            │
T-CONT-PLUS-BWD ──┤                            │
T-PLUS-ROUND  ────┤                            ↓
                  ├──→ W2.13 plus equiv CLOSED ──┐
T-CONT-MINUS-FWD ─┤                              │
T-CONT-MINUS-BWD ─┴──→ W2.13 minus equiv CLOSED ─┼──→ laurentCover_gluing_presheaf CLOSED
                                                 │                   │
T-OVERLAP ──────────→ overlap bridge CLOSED ─────┘                   │
                                                                     │
T-INJ-REROUTE ──→ restrictionMapHom_injective CLOSED                 │
  (OR reroute Part 1 via standard cover)                             │
       │                                                             │
       ↓                                                             │
   tateAcyclicity Part 1 CLOSED                                      │
                                                                     ↓
                                  tateAcyclicity Part 2 CLOSED via T-ACYC-PART2
                                                                     │
                                                                     ↓
                                          tateAcyclicity sorry-free
```

## Execution order

Phase A (parallelisable, independent primitives):
1. T-NULL-EMPTY (cheap statement fix).
2. T-CONT-PLUS-FWD (W2.13 plus continuity forward).
3. T-CONT-PLUS-BWD (W2.13 plus continuity backward).
4. T-CONT-MINUS-FWD (W2.13 minus continuity forward).
5. T-CONT-MINUS-BWD (W2.13 minus continuity backward).
6. T-PLUS-ROUND (W2.13 plus round trip).
7. T-NULL-MAIN (substantial Wedhorn 7.44).
8. T-OVERLAP (Laurent bivariate primitive).

Phase B (depends on A):
9. T-INJ-REROUTE (or direct reroute of Part 1).
10. T-ACYC-PART2 (final assembly).

## Generality decisions

- All new lemmas stated over generic complete strongly noetherian Tate `A`
  (or `B` for the Example 6.38 generic primitive).
- Use `PairOfDefinition` + `RationalLocData` framework uniformly.
- No `[IsDomain]` hypotheses (per reviewer Q3-STEP1).
- Continuity proofs use the `locBasis` filter basis characterisation.
