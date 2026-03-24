# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## Project Overview

A Lean 4 formalization of adic spaces, building on Mathlib. The project follows Wedhorn's *Adic Spaces* textbook. Uses Lean 4 v4.29.0-rc3 with Mathlib v4.29.0-rc3.

## Build Commands

```bash
# Build the full project
lake build

# Build and fetch Mathlib cache first (recommended on fresh clone)
lake exe cache get && lake build

# Check a single file without full build
lake env lean "Adic spaces/Presheaf.lean"
```

## Project Structure

The Lake library name is `«Adic spaces»` (French-quoted due to the space). Imports use this quoting: `import «Adic spaces».Basic`.

```
lakefile.toml                     — Lake build config; depends on mathlib
Adic spaces.lean                  — Root import file (must import every module)
Adic spaces/
  Basic.lean                      — Placeholder base module (1 line)
  ValuationSpectrum.lean          — Valuation spectrum Spv(A), ValuativeRel (386 lines)
  ContinuousValuations.lean       — Continuous valuations, isContinuous (153 lines)
  GeometricSeries.lean            — Topologically nilpotent geometric series (69 lines)
  AdicSpectrum.lean               — Spa(A, A+), PlusSubring, rational subsets (455 lines)
  RationalSubsets.lean            — RationalLocData, rational subset containment (165 lines)
  Bounded.lean                    — IsBounded, IsPowerBounded, A°, A°° (344 lines)
  OpenIdeals.lean                 — Open ideals ↔ topological nilradical (94 lines)
  AffinoidRings.lean              — Rings of integral elements, affinoid rings (94 lines)
  HuberRings.lean                 — Huber rings (f-adic), Tate rings (309 lines)
  LocalizationTopology.lean       — Localization topology on A_s for rational subsets (366 lines)
  CompleteTopCommRingCat.lean     — Category of complete top. comm. rings (94 lines)
  Presheaf.lean                   — Presheaf O_X on Spa(A, A+), restriction maps (893 lines)
  StructureSheaf.lean             — Structure sheaf, IsSheafy, adic spaces (640 lines)
docs/plans/                       — Detailed implementation plans (read before starting work)
docs/STATUS.md                    — CURRENT STATUS of each module (read and update this!)
```

## Module Dependency Graph

```
ValuationSpectrum
  └→ ContinuousValuations
       └→ AdicSpectrum ← GeometricSeries
            ├→ RationalSubsets → Presheaf → StructureSheaf
            ├→ OpenIdeals                       ↑
            └→ AffinoidRings ← Bounded → HuberRings → LocalizationTopology → Presheaf
                                                            CompleteTopCommRingCat ↗  ↗
```

## Lean Options (from lakefile.toml)

- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- `relaxedAutoImplicit = false` — no auto-implicit variables; all variables must be declared
- `weak.linter.mathlibStandardSet = true` — mathlib style linting enabled
- `maxSynthPendingDepth = 3`

## Conventions

- Follow Mathlib naming conventions and style (the mathlib linter is active).
- All new `.lean` files under `Adic spaces/` must be imported in `Adic spaces.lean`.
- Since `relaxedAutoImplicit = false`, always declare universe variables and type variables explicitly with `variable` or `section` blocks.
- Reference Wedhorn section numbers in docstrings (e.g., "Definition 7.14 of Wedhorn").
- Use the MCP lean-lsp tools for checking goals, diagnostics, searching Mathlib, etc.

## Multi-Agent Coordination

Multiple Codex agents may work on this project concurrently. Follow these rules:

1. **Read `docs/STATUS.md` before starting work.** It tracks what's done, in progress, and blocked.
2. **Update `docs/STATUS.md` when you start or finish a task.** Mark items `IN PROGRESS (agent: Codex/claude2/claude3)` or `DONE`.
3. **Read `docs/plans/` for detailed implementation plans** before working on Presheaf, StructureSheaf, or sorry-removal tasks.
4. **Do not modify files another agent is working on** (check STATUS.md). Work on independent modules or tasks.
5. **Check `lake env lean "Adic spaces/YourFile.lean"` compiles** before considering work done.
6. **Commit frequently** with descriptive messages referencing Wedhorn sections.

### Tate Acyclicity Tickets

For the Tate acyclicity project (Wedhorn Thm 8.28(b)), use the ticket tracker:

1. **Read `docs/TICKETS-tate-acyclicity.md`** — it has the tracker table and dependency graph.
2. **Before starting a ticket:** Update the tracker table (Status → `IN PROGRESS`, fill Agent + date), then **commit** before writing code.
3. **When done:** Update tracker (Status → `DONE`, fill date + commit hash), then **commit**.
4. **Never work on a ticket that's already `IN PROGRESS`** by another agent.
5. **Only pick tickets whose dependencies are all `DONE`.**

## Key Design Decisions

- **Discrete case first:** Sorries for `isUnit_canonicalMap_s`, `restrictionMapAlg_continuous`, and `IsSheafy.discrete` are proved under `[DiscreteTopology A]`. General case is future work.
- **Presheaf values are completions:** `presheafValue D` = completion of `Localization.Away D.s` with the localization topology.
- **Restriction maps via extensionHom:** Algebraic lift + continuity proof → extend to completion.
- **Trivial valuation at primes:** `exists_mem_spa_supp_eq_of_prime` constructs Spa points for any prime (discrete case), used for the radical ideal argument.
