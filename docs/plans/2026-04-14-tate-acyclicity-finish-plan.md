# Finishing Tate Acyclicity (non-discrete): Dependency Map

**Date:** 2026-04-14
**Goal:** Make `tateAcyclicity` sorry-free for the non-discrete strongly noetherian Tate case.
**Prerequisite plan:** `2026-04-08-wedhorn-vs-zavyalov.md` (the main Wedhorn route).

## What's actually done (verified)

| Phase | Item | File:line |
|---|---|---|
| 1 | Audit + reframe R2 | DONE |
| 2.1 | Prop 6.17 statement | `NoetherianTateModules.lean:299` |
| 2.2 | Natural Tate topology on `TateAlgebra A` | `TateAlgebraTopology.lean` |
| 2.3 | Prop 6.17 proof (Krull intersection route) | `NoetherianTateModules.lean` |
| 2.4 | `(1-sX)` closed | `TateAlgebra.lean` |
| 2.5 | Quotient complete + T2 | `TateAlgebraTopology.lean` |
| 2.6 | Continuous bijection `tateQuotientToPresheafHom` | `TopologyComparison.lean:1616` |
| 2.7 | Banach → homeomorphism | `TopologyComparison.lean:2266` (`tateQuotientToPresheafHom_isHomeomorph`) |
| 4 (partial) | Route B: `laurentCover_gluing_presheaf` via `row3_exact` | `LaurentRefinement.lean:588` (reduced to 5 bridge stubs) |

**Phase 2 is fully in place:** the topological ring iso `presheafValue D ≃_top A⟨X⟩/(1-s·X)` is accessible via `presheafValueTateQuotientEquiv`, `presheafValueCanonicalQuotientEquiv`, and `tateQuotientToPresheafHom_isHomeomorph` (with 5 hypotheses, all dischargeable for strongly noetherian Tate rings).

## The real blockers (what's still sorry'd)

### Sorry layer A — "independent infrastructure"

These are not sorry-chained through other Tate-acyclicity sorries. Fixing any of them is a standalone win.

| Sorry | File:line | Dependency | Est. effort |
|---|---|---|---|
| `exists_spa_point_in_rationalOpen` (non-open prime case) | `StructureSheaf.lean:682` | Lemma 7.45 via completion (`Lemma745.lean` sorry-free) | ~80 lines |
| 5 Route B bridges | `LaurentRefinement.lean:419–480` | Phase 2 iso + base-change machinery | ~200 lines combined |
| `RationalLocData.completedLocSubring_isAdic` | `Presheaf.lean:421` | AdicCompletionBridge extension | ~50 lines |
| `PresheafTateStructure.lean:1073` (idealOfDef_pow_val_isClosed) | `PresheafTateStructure.lean:1073` | AdicCompletion map_exact | ~150 lines |

### Sorry layer B — "Phase 3/4/5 assembly"

These CAN be filled once layer A lands, but they assemble other pieces:

| Sorry | File:line | Blocks | Blocked by |
|---|---|---|---|
| `restrictionMapHom_surj` | `PresheafTateStructure.lean:1226` | `restrictionMap_isLocalization` | Baire infrastructure (or: skip via Route B) |
| `restrictionMapHom_injective` | `PresheafTateStructure.lean:1322` | `tateAcyclicity` Part 1, `rationalCovering_hasSeparation` | Cor 8.32 faithful flatness |
| `tateAcyclicity` Part 2 | `LaurentRefinement.lean:642` | `rationalCovering_hasGluing` (nonempty), `isSheafy...flat.gluing` | Lemma 8.34 + `laurentCover_gluing_presheaf` (Route B bridges) |
| `rationalCovering_hasSeparation` empty branch | `LaurentRefinement.lean:716` | `isSheafy...flat` empty edge | Spa-point at non-open prime (layer A) |
| `isSheafy_ofStronglyNoetherianTate_flat.embedding` | `StructureSheaf.lean:996` | `IsSheafy` instance | Phase 2 iso + 3×3 topological chase (Phase 4) |

## Critical path to sorry-free `tateAcyclicity`

```
  Lemma 7.45 completion → exists_spa_point_in_rationalOpen (non-open)  ─┐
                                                                        │
  ┌─── Phase 2 iso ────┐                                               │
  │    (DONE)          │                                               │
  │                    ↓                                               │
  │              presheafValue_flat_of_tateQuotient (DONE)              │
  │                    ↓                                               │
  │              Cor 8.32 faithful flatness  ←──────────────────────────┘
  │                    ↓                                               (uses Spa-point radical arg)
  │              restrictionMapHom_injective  ←──────── Cor 8.32 injectivity corollary
  │                    ↓
  │              tateAcyclicity Part 1 (rewrite)
  │
  └─── Route B ──→ 5 bridge lemmas ──→ laurentCover_gluing_presheaf (sorry-free via bridges)
                         ↓
                   Lemma 8.34 refinement transfer
                         ↓
                   tateAcyclicity Part 2 (rewrite)

  Result: tateAcyclicity sorry-free.
```

## Critical-path line budget

| Step | Est. lines |
|---|---|
| Non-open prime Spa-point (`exists_spa_point_in_rationalOpen`) | ~80 |
| Cor 8.32 (faithful flatness + radical arg) | ~150 |
| Rewrite `restrictionMapHom_injective` via Cor 8.32 | ~20 |
| Rewrite `tateAcyclicity` Part 1 using Cor 8.32 directly | ~15 |
| 5 Route B bridges (`laurentPlus/MinusBridge` + 3 compat) | ~200 |
| Lemma 8.34 (refinement transfer via `CechCohomology` + Laurent) | ~100 |
| Rewrite `tateAcyclicity` Part 2 via `laurentCover_gluing_presheaf` + 8.34 | ~50 |
| Rewrite `rationalCovering_hasSeparation` empty branch | ~10 |
| Dead code removal (Baire surj, old `restrictionMap_isLocalization`) | ~30 |
| **Total** | **~655** |

**Realistic pacing:** 3 sessions of ~200 lines each, or 2 sessions of ~325 lines.

## Suggested session order

**Session A (unblocking layer A + Phase 3 core):**
1. Fill `exists_spa_point_in_rationalOpen` non-open prime via Lemma 7.45 completion.
2. Prove Cor 8.32 (needs the above).
3. Rewrite `restrictionMapHom_injective` + Part 1 of `tateAcyclicity` via Cor 8.32.
4. Empty-branch `hasSeparation` via same Spa-point lemma.
5. **Expected end state:** separation-side sorry-free end-to-end; `tateAcyclicity` Part 2 still sorry.

**Session B (Route B bridges):**
1. Fill `laurentMinusBridge` (Phase 2 iso + base-change + unit-rescaling).
2. Fill `laurentPlusBridge` (Phase 2 iso + f-X identification).
3. Fill the three compat lemmas.
4. **Expected end state:** `laurentCover_gluing_presheaf` sorry-free end-to-end.

**Session C (Lemma 8.34 + final assembly):**
1. State + prove Lemma 8.34 (induction over `|T|`, uses `laurentCover_gluing_presheaf` + `CechCohomology` refinement).
2. Rewrite `tateAcyclicity` Part 2 using 8.34.
3. Rewrite `isSheafy_ofStronglyNoetherianTate_flat.embedding` via the topological iso chain.
4. Dead code removal.
5. **Expected end state:** `tateAcyclicity` sorry-free; `isSheafy_ofStronglyNoetherianTate_flat` sorry-free.

## Single-session partial-progress notes

If you only have one session:
- **Sessions A or B each produce a genuine, self-contained deliverable.** A yields separation; B yields Laurent gluing.
- **Do not start C without A+B both done** — C assembles other pieces and stalls without them.
- **Route B bridges (B)** are the most confined single-session target: they touch only `LaurentRefinement.lean` + `TopologyComparison.lean` and don't interact with the Spa-point infrastructure.

## Files that will be touched

- `LaurentRefinement.lean` (main: bridges, `tateAcyclicity`, `rationalCovering_*`)
- `StructureSheaf.lean` (Spa-point at non-open prime, `isSheafy_...flat`)
- `PresheafTateStructure.lean` (remove dead sorries, rewrite `restrictionMapHom_injective`)
- `CechCohomology.lean` or a new `Lemma8_34.lean` (refinement transfer)
- New: `Cor8_32.lean` or integrated into `StructureSheaf.lean` (faithful flatness)

## Known risks

1. **`exists_spa_point_in_rationalOpen` non-open prime case** is the most mathematically delicate piece. The completion route (take A/p completion as a Tate ring, use its Tate unit valuation, pull back) is well-trodden mathematically but needs careful topological bookkeeping. Budget a full session just for this.
2. **Route B bridges require non-discrete generalization of `tateQuotientFSubXEquiv`** (currently `[DiscreteTopology]` only). The complete-A setting should make this tractable via Phase 2 iso + evaluation at X=f, but the details need care around the T-extension topology.
3. **Lemma 8.34 may need `CechCohomology.Refinement` extensions** — check existing refinement API before writing new primitives.
