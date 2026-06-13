# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## BINDING RULE — no work-deferral via hypotheses, witnesses, or parameters

You are NOT allowed to defer work by adding any of the following to a theorem signature:

1. **Hypotheses** (additional `(h : ...)` premises).
2. **Witnesses / data parameters** (extra `(x : T)` parameters that supply structure the conclusion uses).
3. **Typeclass instances** (extra `[Foo X]` brackets that constrain the setting).
4. **"Parametric" reformulations** that turn a deep dependency into a parameter pushed to callers.

These are prohibited UNLESS one of these holds:

- **(a)** The user has explicitly told you to do that specific thing.
- **(b)** The result is genuinely *mathematically false* without the addition — not "the project's current proof route happens to need it"; the *result itself* must be false.

If neither (a) nor (b) holds, prove the result as stated with the existing signature, even if that takes substantial work.

**What IS allowed**, and is the right move when you can't close everything in one go:

- **Sub-lemmas with `sorry` bodies** — fine. Decomposing a hard proof into named sub-lemmas (each with its own sorry) is normal proof structure, not work-deferral, as long as the sub-lemma's statement does not itself add hypotheses to dodge work.
- **New files** containing such sub-lemmas — fine. File granularity is an organisational choice, not a deferral.
- **Sub-tickets on the planning board** — fine. Planning artifacts don't pollute Lean signatures.

The difference: sub-lemma-with-sorry keeps the obligation honest at the original signature; adding a hypothesis silently *removes* the obligation by changing what's being claimed.

Forbidden patterns observed in past sessions:
- Adding `(g_inv : A) (hg_inv : g * g_inv = 1) ...` to make a unitness argument easier.
- Adding `(hArch : ∀ v, MulArchimedean ...)` to "match the project pattern" when the result is true without it.
- Adding `h_spa_lift : Wedhorn 7.49 reverse` as a parameter and calling the consumer "closed".

When you reach for any of these, stop and either (1) actually prove the thing without the addition, or (2) leave the theorem with a `sorry` body — possibly decomposed into sub-lemma sorries — and report the obstruction concretely.

## BINDING RULE — Wedhorn-faithfulness (mirror the source; never invent a route)

As binding as the rule above. It applies to YOU and to EVERY agent you launch.

The recurring, expensive failure in this project is this: a proof gets decomposed into
sub-lemmas that *diverge from Wedhorn's actual argument*, and the decomposition then bottoms
out at a lemma Wedhorn never proves — which is reliably either **mathlib-lacking infrastructure**
(e.g. a restricted-power-series Fubini) or **outright false** (e.g. "strongly noetherian ⇒
noetherian ring of definition", or "noetherian ⇒ strongly noetherian", or the dead `L21`).
Every such episode is wasted work, and the cause is always the same: leaving the source.

Rules:

1. **Cite the source on every declaration.** Each `theorem`/`def`/`lemma` formalizing a Wedhorn
   result carries, in its docstring, the exact citation: statement number, page, AND the line
   range in `/private/tmp/wedhorn.txt` — e.g. "Wedhorn Remark 6.37(1), p. 54 (wedhorn.txt:2682)".
   A declaration with no source citation is suspect by default.

2. **Read Wedhorn's proof, then transcribe its skeleton, BEFORE decomposing.** Open
   `/private/tmp/wedhorn.txt`, read the actual proof, and write down the chain of propositions it
   invokes with their exact hypotheses and dependencies. Your Lean decomposition must mirror
   *that* chain. Do NOT decompose by "what looks provable in Lean" or "what connects to the code
   we already have" — those pulls are exactly what produce the divergence.

3. **No orphan leaves.** A sub-lemma with no Wedhorn counterpart is permitted ONLY as a genuine
   mathlib-level prerequisite (a general algebra/topology fact), and it must be labelled
   `-- INFRASTRUCTURE (not in Wedhorn)`. If discharging a step requires you to *build substantial
   missing infrastructure*, STOP — that is the tell that you have left Wedhorn's route. Re-read
   the source for the real argument before writing another line.

4. **Never use memory or a conversation summary as the source of a statement or a proof route.**
   They drift from both Wedhorn and the code. Re-read the Wedhorn passage and the actual `.lean`
   for everything you touch. Memory/summaries are for pointers ("X lives in file Y"), never for
   "what Wedhorn proves" or "how the proof goes".

5. **Propagate to every launched agent.** An agent given a formalization task MUST receive, in its
   prompt: this rule, the verbatim Wedhorn passage for its target (with wedhorn.txt line numbers),
   and the proof-map skeleton for its part. Never launch an agent with a bare goal.

**Acceptance test** for any leaf on the board: you can quote the Wedhorn passage (verbatim, with
wedhorn.txt line numbers) that justifies it. If you cannot, it is an artifact — delete it and find
Wedhorn's real route. Plan top-down from `/private/tmp/wedhorn.txt`, reading from the headline
theorem downward, before writing code. The current plan for Thm 8.28(b) is
`docs/WEDHORN-8.28b-PROOFMAP.md`.

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

Multiple Claude Code agents may work on this project concurrently. Follow these rules:

1. **Read `docs/STATUS.md` before starting work.** It tracks what's done, in progress, and blocked.
2. **Update `docs/STATUS.md` when you start or finish a task.** Mark items `IN PROGRESS (agent: claude/claude2/claude3)` or `DONE`.
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
