# Ticket Board — Close 10 sorries on `tateAcyclicity` path

## Summary
- Total: 10 tickets (renumbered 2026-04-15).
- Open: 10 | In Progress: 0 | Done: 0.
- See `plan.md` for mathematical goal and dependency graph.

## Tickets

### [T-NULL-EMPTY] Fix `exists_nullstellensatz_refinement_of_empty_covers` statement
- **Status**: open
- **File**: `Adic spaces/StandardCover.lean:223`
- **Depends on**: none
- **Parallel**: yes
- **Type**: statement fix
- **Description**: The sorry is genuinely unprovable as stated (need non-empty S for span-top ∧ empty S for refines_contain in `Nontrivial A`). Fix: add `(hne : C.covers.Nonempty)` to `refines_by_standard_cover` (downstream already has it). Alternative: return `Sum` / `Option` witnesses, or derive `False` via some non-trivial-base axiom. Simplest: thread `hne` through and close the pathological branch by `absurd`.
- **Est. lines**: ~10.

### [T-CONT-PLUS-FWD] `iteratedPlus_forwardToCompletion_continuous`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:743`
- **Depends on**: none (fresh proof)
- **Parallel**: yes
- **Description**: Continuity of `coeRingHom_B ∘ iteratedPlus_forwardLocHom : Loc_A(D₀.s) → presheafValue(iteratedPlusDatum_B)` from `(laurentPlusDatum D₀ f).topology` to the completion topology. Strategy: coeRingHom is continuous; reduce to continuity of `iteratedPlus_forwardLocHom` at the loc-topology level. Check that basic `locNhd P (insert f D₀.T) D₀.s n` maps into basic `locNhd P_B {canonicalMap f} 1 m` for suitable m, via canonicalMap A → B.
- **Est. lines**: ~60–100.

### [T-CONT-PLUS-BWD] `iteratedPlus_backwardLocHom_continuous`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:753`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Continuity of `iteratedPlus_backwardLocHom : Loc_B(1) → presheafValue(laurentPlusDatum D₀ f)`. Built via `IsLocalization.Away.lift` at `1` (trivial unit) with `restrictionMapHom` as the base B-hom. Since `restrictionMapHom_continuous` is already proved, the lift at 1 should transfer continuity. Key: show the localization topology on `Loc_B(1)` ≃ B's completion topology, then compose.
- **Est. lines**: ~40–60.

### [T-PLUS-ROUND] `iteratedPlus_forwardHom_comp_backwardHom`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:894`
- **Depends on**: T-CONT-PLUS-FWD, T-CONT-PLUS-BWD (or use completion API directly)
- **Parallel**: yes
- **Description**: Round trip `forward ∘ backward = id` on `presheafValue(iteratedPlusDatum_B)`. Use `Completion.ext'` on source; check on `coeRingHom_B b` for `b : Loc_B(1)`. Reduces to uncompleted-level identity + density of `canonicalMap A` image in `B`.
- **Est. lines**: ~50.

### [T-CONT-MINUS-FWD] `iteratedMinus_forwardToCompletion_continuous`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:976`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Analog of T-CONT-PLUS-FWD for minus branch. Source `Loc_A(D₀.s · f)` with `(laurentMinusDatum).topology`, target `presheafValue(iteratedMinusDatum_B)` = completion of `Loc_B(canonicalMap f)`. Continuity of the forward loc hom transferred via canonicalMap.
- **Est. lines**: ~60–100.

### [T-CONT-MINUS-BWD] `iteratedMinus_backwardLocHom_continuous`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:986`
- **Depends on**: none
- **Parallel**: yes
- **Description**: Continuity of `iteratedMinus_backwardLocHom : Loc_B(canonicalMap f) → presheafValue(laurentMinusDatum D₀ f)` via `IsLocalization.Away.lift` at `canonicalMap f` with `restrictionMapHom` as base hom. Uses `restrictionMap_canonicalMap_f_isUnit_laurentMinus`.
- **Est. lines**: ~40–60.

### [T-NULL-MAIN] `exists_nullstellensatz_refinement_of_rationalOpen_nonempty`
- **Status**: open
- **File**: `Adic spaces/StandardCover.lean:259`
- **Depends on**: none (uses existing Spa-point infrastructure)
- **Parallel**: yes (separate file from the W2.13 work)
- **Description**: Wedhorn Prop 7.14 / Lemma 7.44 — given a rational cover with nonempty base rational open, produce a finite family `S ⊂ A` with `span S = ⊤` that refines the cover. Combines:
  - Open-prime route via `exists_spa_point_in_rationalOpen_of_isOpen_prime` (StructureSheaf.lean:602).
  - Non-open-prime route via `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`.
  - Zavyalov §2.3 construction of the `fᵢ` from ratios `tⱼ/Dⱼ.s`.
- **Est. lines**: ~100–150.

### [T-OVERLAP] `laurentOverlapBridge_exists_compatible`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:2151`
- **Depends on**: none (building new infrastructure)
- **Parallel**: yes
- **Description**: Bivariate analog of Example 6.38: build a ring equiv `presheafValue(laurentOverlapDatum D₀ f) ≃+* LaurentCover.B₁₂_gen (canonicalMap f)` where the target is `LaurentTateAlgebra B ⧸ (algebraMap(canonicalMap f) − zeta)`. Use `evalHomBounded`-style construction for the bivariate Laurent algebra.
- **Est. lines**: ~150–200.

### [T-INJ-REROUTE] Reroute `tateAcyclicity` Part 1 to avoid `restrictionMapHom_injective`
- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean` (tateAcyclicity Part 1)
- **Depends on**: T-CONT-*, T-PLUS-ROUND (or T-NULL-MAIN for the refinement chain)
- **Parallel**: no (after W2.13 + bridges land)
- **Description**: Rewrite `tateAcyclicity` Part 1 to use `separation_of_finer_rational` (sorry-free, already in `RationalRefinement.lean`) + Laurent cover separation, instead of `restrictionMapHom_injective` directly. This closes item 2 by rerouting rather than discharging.
- **Est. lines**: ~30.

### [T-ACYC-PART2] `tateAcyclicity` Part 2 (gluing)
- **Status**: blocked
- **File**: `Adic spaces/LaurentRefinement.lean:2758`
- **Depends on**: T-NULL-MAIN, T-CONT-*, T-PLUS-ROUND, T-OVERLAP, T-NULL-EMPTY
- **Parallel**: no
- **Description**: Final assembly. Use `tateAcyclicity_gluing_via_refinement` (already in LaurentRefinement, sorry-free) + `refines_by_standard_cover` (from StandardCover) + `laurentCover_gluing_presheaf` (depends on bridges which depend on W2.13 + overlap).
- **Est. lines**: ~30.

## Execution Plan

Phase A — parallelisable independent tickets:
- T-NULL-EMPTY (trivial fix first).
- T-CONT-PLUS-FWD, T-CONT-PLUS-BWD, T-PLUS-ROUND (plus branch continuity).
- T-CONT-MINUS-FWD, T-CONT-MINUS-BWD (minus branch continuity).
- T-NULL-MAIN (independent Nullstellensatz).
- T-OVERLAP (independent Laurent overlap).

Phase B — after Phase A closes the W2.13 equivs and bridges:
- T-INJ-REROUTE.
- T-ACYC-PART2.

Up to 3–4 workers in parallel; Lean LSP stability limits it.
