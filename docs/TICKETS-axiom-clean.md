# Axiom-Clean Tickets v2: Remove sorryAx from isSheafy

**Goal:** `isSheafy_ofStronglyNoetherianTate_flat` axiom-clean.

**Key insight (2026-04-03, reviewer):** `locLift_preimage_locNhd` (old S1) is **FALSE**.
Individual restriction maps are NOT topological embeddings. The sheaf condition
requires the PRODUCT map to be an embedding, proved via strict exactness of the
Laurent row, NOT via individual inducing maps.

**Counterexample (Conrad):** `A = Q_p⟨X⟩`, `U = R({p,X}/p)`. Then `X^m ∈ p^m A₀[X/p]`
but `X^m ∉ pA₀`, so no backward neighborhood inclusion exists.

---

## New Architecture

**DELETE** the false chain:
- `locLift_preimage_locNhd` (FALSE)
- `locLift_isUniformInducing` (depends on above)
- `restrictionMapAlg_isUniformInducing` (depends on above)
- `restrictionMapHom_isInducing` (depends on above)
- `restrictionMapHom_injective` (depends on above)
- `productRestrictionSub_isInducing` (depends on above)

**REPLACE** with strict exactness route:
```
δ surjective + continuous
  → δ open (Banach open mapping, T3)
  → ker(δ) closed in B₁ × B₂ → complete
  → ε : A → ker(δ) continuous bijection, complete source
  → ε open (Banach open mapping again)
  → ε is topological embedding
  → product restriction is embedding for Laurent covers
  → refinement transfers embedding to rational covers
```

**KEEP:**
- Forward continuity of restriction maps (`restrictionMapAlg_continuous`)
- Algebraic exactness (T1: `row3_exact`, sorry-free)
- Open mapping theorem (T3: done)
- Laurent refinement chain

---

## Tracker

| Ticket | Status | Agent | Notes |
|--------|--------|-------|-------|
| R1 | DONE | claude-opus | 2026-04-03. Quarantined false chain, gave restrictionMapHom_injective a sorry for new proof. |
| R2 | IN PROGRESS | claude-opus | Banach open mapping theorem stated (1 sorry). R2 lives at presheaf level (StructureSheaf). Needs: open mapping thm + presheaf continuity + completeness. |
| R3 | NOT STARTED | — | Refactor `IsSheafy` proof to use strict exactness. BLOCKED on R2. |
| R4 | IN PROGRESS | claude | HasLocLiftPowerBounded class + API propagation done. Tate instance has 1 sorry: adic Nullstellensatz (Prop 7.14: v≤1 → integral). |
| R5 | NOT STARTED | — | Remove `[FirstCountableTopology]` (derive from Tate) |

## Dependency Graph

```
R1 (delete false chain)
    ↓
R2 (strict exactness) ←── R4 (forward continuity)
    ↓
R3 (refactor IsSheafy)
    ↓
R5 (cleanup FirstCountableTopology)
```

R1 is prerequisite for everything. R2 and R4 can be parallel after R1.
R3 needs R2. R5 is cleanup.

---

## TICKET R1: Delete False Inducing Chain

**Status:** NOT STARTED
**Estimated:** ~50 lines (deletions + quarantine)
**Blocks:** R2, R3

### Task

Delete or quarantine the false `locLift_preimage_locNhd` and all theorems
that depend on it. Mark them as FALSE with a reference to the counterexample.

### What to delete/quarantine

1. `locLift_preimage_locNhd` (PresheafTateStructure.lean:1069) — FALSE
2. `locLift_isUniformInducing` (PresheafTateStructure.lean:1117) — depends on 1
3. `restrictionMapAlg_isUniformInducing` (PresheafTateStructure.lean:1157) — depends on 2
4. `restrictionMapHom_isInducing` (PresheafTateStructure.lean:1245) — depends on 3
5. `restrictionMapHom_injective` (PresheafTateStructure.lean:1221) — depends on 3
6. `productRestrictionSub_isInducing` (StructureSheaf.lean:938) — depends on 4

### What to keep

- `locLift_maps_locNhd` (forward direction, TRUE)
- `restrictionMapAlg_continuous` (forward continuity, TRUE but has its own sorry)
- `restrictionMapHom_surj` (surjectivity condition, TRUE but has sorry)

---

## TICKET R2: Strict Exactness of Laurent Row

**Status:** NOT STARTED
**Estimated:** ~150 lines
**Blocks:** R3
**Depends on:** R1, T1 (row3_exact), T3 (open mapping)

### Task

Prove the Laurent cover exact sequence `0 → A → B₁ × B₂ → B₁₂ → 0` is STRICT:
- ε is a topological embedding
- δ is open (hence strict)

### Proof strategy (from reviewer)

1. **δ is open:** `deltaMap_gen` is surjective (T1) and continuous (forward
   continuity). By the Banach open mapping theorem for complete Tate modules
   (T3 / Wedhorn Thm 6.16), surjective continuous maps between complete
   modules with countable neighborhood bases are open.

2. **ker(δ) is closed:** Preimage of {0} under continuous map.

3. **ker(δ) is complete:** Closed subgroup of complete space.

4. **ε is a topological embedding:** ε : A → ker(δ) is a continuous bijection
   (from algebraic exactness T1). Source A is complete. Target ker(δ) is
   complete T₂. By the same open mapping theorem, ε is open. Hence ε is a
   homeomorphism onto ker(δ), i.e., a topological embedding into B₁ × B₂.

### Key requirements

- Continuity of δ (forward, from restriction map continuity)
- Completeness of B₁, B₂, B₁₂ (as completed rational localizations)
- Countable neighborhood bases (from Noetherian Tate ring structure)
- Open mapping theorem (T3, already done)

---

## TICKET R3: Refactor IsSheafy Proof

**Status:** NOT STARTED
**Estimated:** ~100 lines
**Blocks:** Nothing (final)
**Depends on:** R2

### Task

Rewrite `isSheafy_ofStronglyNoetherianTate_flat` to use strict exactness
(R2) instead of `productRestrictionSub_isInducing` (deleted in R1).

### Proof route

1. For the Laurent cover `{R(f/1), R(1/f)}`: strict exactness gives
   embedding of A into B₁ × B₂ (from R2).
2. Rational covers refine to products of Laurent covers (Lemma 8.34).
3. Refinement preserves the embedding property.
4. Assemble: `IsSheafy` instance.

---

## TICKET R4: Forward Continuity (Power-Bounded from Rational Containment)

**Status:** NOT STARTED (existing sorry in Presheaf.lean:807)
**Estimated:** ~100 lines
**Blocks:** R2 indirectly

### Task

Prove: for `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)` and `t ∈ D₀.T`, the element
`t/D₀.s` is power-bounded in the D-localization topology.

### Proof strategy (from reviewer)

1. `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)` means: for all `v ∈ R(D.T/D.s)`,
   `v(t) ≤ v(D₀.s)`.
2. Since `D₀.s` is a unit in `Loc.Away D.s`, this gives `v(t/D₀.s) ≤ 1`.
3. By the characterization `B⁺ = {b : v(b) ≤ 1 for all v ∈ Spa}`, we get
   `t/D₀.s ∈ B⁺ ⊆ B°` (power-bounded).
4. Step 3 is the "adic Nullstellensatz" / Prop 7.14, which is a medium
   formalization target.

### Alternative

For now, add `IsPowerBounded (locLift(divByS t D₀.s))` as a hypothesis
and discharge it separately.

---

## TICKET R5: Remove FirstCountableTopology

**Status:** NOT STARTED
**Estimated:** ~50 lines
**Depends on:** R1-R3

### Task

Prove `FirstCountableTopology` from `[IsTateRing A] [IsNoetherianRing A]`:
the ideal of definition gives a countable neighborhood basis `{I^n}`.
Then remove `[FirstCountableTopology A]` from the theorem statement.

---

## Summary

| Ticket | Lines | Depends on | Parallel with | Difficulty |
|--------|-------|------------|---------------|------------|
| **R1** | ~50 | None | — | Easy |
| **R2** | ~150 | R1 | R4 | Hard |
| **R3** | ~100 | R2 | — | Medium |
| **R4** | ~100 | None | R2 | Hard |
| **R5** | ~50 | R1-R3 | — | Medium |

**Critical path:** R1 → R2 → R3
**Total:** ~450 lines of new code + deletions
