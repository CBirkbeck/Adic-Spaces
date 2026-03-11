# Project Status

> **Agents: Read this file before starting work. Update it when you begin or complete a task.**
>
> Last updated: 2026-03-11

## Module Status

| Module | Lines | Status | Notes |
|--------|-------|--------|-------|
| `ValuationSpectrum.lean` | 386 | DONE | Spv(A), ValuativeRel, supp |
| `ValuativeRel/Comap.lean` | 55 | DONE | Comap for ValuativeRel, not_vle_zero_of_isUnit |
| `ContinuousValuations.lean` | 153 | DONE | isContinuous, Spa membership |
| `GeometricSeries.lean` | 69 | DONE | Topologically nilpotent => summable, 1-a unit |
| `AdicSpectrum.lean` | 455 | DONE | Spa(A, A+), Prop 7.51/7.52, exists_mem_spa_supp_eq_of_prime |
| `RationalSubsets.lean` | 165 | DONE | RationalLocData, rational subset containment |
| `Bounded.lean` | 344 | DONE | IsBounded, IsPowerBounded, A° subring, A°° |
| `OpenIdeals.lean` | 91 | DONE | Open ideals <-> topological nilradical |
| `AffinoidRings.lean` | 94 | DONE | IsRingOfIntegralElements, IsAffinoidRing |
| `HuberRings.lean` | 619 | DONE | PairOfDefinition, IsHuberRing, IsTateRing, IsAdicHom, Prop 6.25 |
| `LocalizationTopology.lean` | 366 | DONE | Localization topology, RingSubgroupsBasis |
| `CompleteTopCommRingCat.lean` | 94 | DONE | Bundled category, forgetful functors |
| `Presheaf.lean` | 893 | DONE | presheafValue, restriction maps, productRestriction |
| `StructureSheaf.lean` | 640 | DONE | IsSheafy, structure sheaf, adic space defn |
| `OrderedGroupConvex.lean` | 444 | DONE | ConvexSubgroup, quotient order, maxAvoid, archimedean iff (§7.1) |
| `ValuationCoarsening.lean` | 213 | DONE | Valuation coarsening, cofinal property for archimedean (§7.1) |
| `AnalyticPoints.lean` | 112 | DONE | IsAnalytic, Tate => analytic, Jacobson radical, idealOfDef API |
| `AdicMorphisms.lean` | 171 | DONE | Lemma 7.46(1)+(2 first part), Tate specializations |
| `Basic.lean` | 1 | PLACEHOLDER | Empty |

## Sorry-Free Status

As of 2026-03-11: **No sorries in any Lean source file.** All theorems are fully proved.

## Key Theorems (Adic Morphisms Chain)

| Theorem | File | Wedhorn ref | Status |
|---------|------|-------------|--------|
| `IsAdicHom` (Def 6.23) | HuberRings:502 | Def 6.23 | DONE |
| `IsTateRing.isAdicHom_of_continuous_with_pairs` (Prop 6.25) | HuberRings:534 | Prop 6.25 | DONE (with h_map hyp) |
| `nonAnalytic_comap_of_continuous` (Lem 7.46(1) first) | AdicMorphisms:53 | Lem 7.46(1) | DONE |
| `analytic_comap_of_isAdicHom` (Lem 7.46(1) second) | AdicMorphisms:123 | Lem 7.46(1) | DONE |
| `analytic_comap_of_isAdicHom_tate` (Tate specialization) | AdicMorphisms:164 | Lem 7.46(1) | DONE |
| Lemma 7.45 (analytic point construction) | — | Lem 7.45 | NOT STARTED |
| Lemma 7.46(2) (converse: analytic preservation => adic) | — | Lem 7.46(2) | NOT STARTED (needs 7.45) |
| Def 8.38 (adic morphisms of adic spaces) | — | Def 8.38 | NOT STARTED |
| Prop 8.39, Cor 8.40 | — | Prop 8.39, Cor 8.40 | NOT STARTED |

## Open Work Items

### High Priority
- [x] **Verify full project builds** — `lake build` passes (2337 jobs, 2026-03-11)
- [ ] **Commit all current work** — many new files + modified files uncommitted

### Medium Priority (extending the formalization)
- [ ] **Lemma 7.45** — Analytic point construction for complete affinoid rings (needs Mathlib `IsLocalRing.exists_factor_valuationRing`, `IsAdicComplete.le_jacobson_bot`)
- [ ] **Lemma 7.46(2)** — Converse: analytic preservation implies adic (needs 7.45)
- [ ] **Remove h_map hypothesis from Prop 6.25** — needs Prop 6.4(5) (bounded open subring = ring of definition)
- [ ] **General (non-discrete) sorry removal** — `isUnit_canonicalMap_s` and `restrictionMapAlg_continuous` currently require `[DiscreteTopology A]`
- [ ] **Sheaf condition for general Huber rings** — `IsSheafy` only proved for discrete; need Tate acyclicity (Thm 8.28)
- [ ] **Categories V^pre and V** — see `docs/plans/2026-03-08-complete-top-ring-category.md` Tasks 2-3

### Low Priority / Future
- [ ] **Tate's acyclicity theorem** (Wedhorn Thm 8.28) — the hard theorem
- [ ] **Perfectoid spaces** — long-term goal
- [ ] **Clean up `Basic.lean`** — currently a placeholder

## Plan Documents

Detailed implementation plans live in `docs/plans/`:
- `2026-03-07-restriction-maps-and-sheafy.md` — Original plan for restriction maps (mostly implemented)
- `2026-03-08-prove-remaining-sorries.md` — Plan for removing sorries (completed for discrete case)
- `2026-03-08-complete-top-ring-category.md` — Plan for CompleteTopCommRingCat and V categories
- `2026-03-11-adic-morphisms-cor-8-40.md` — Plan for Cor 8.40 (Phases 1-3 done, Phase 4 partial)

## Agent Activity Log

> When you start working, add a line here. Remove it when done.

| Agent | Working On | File(s) | Started |
|-------|-----------|---------|---------|
| — | — | — | — |
