# Ticket Board — `tateAcyclicity` Completion

**Last refreshed**: 2026-04-17 (verified against current codebase).

**Target**: `ValuationSpectrum.tateAcyclicity`
(`Adic spaces/LaurentRefinement.lean:3671`) sorry-free, signature unchanged
(`[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(C : RationalCovering A) (hne : C.covers.Nonempty)`).

## Current state at a glance

```
tateAcyclicity Part 1 (LaurentRefinement.lean:3693-3696)
   └── restrictionMapHom_injective (PresheafTateStructure.lean:1322)  ←[T-INJ-1]
          ├── Route A (algebraic NZD):        open
          └── Route B (via Cor 8.32):
                 └── coeRingHom_preserves_proper
                        └── T-IDEAL-1 (topological approx)  ✅ DONE
                        └── T-IDEAL-2 (closedness)  ❌ BLOCKED on Bourbaki CA III §2.8

tateAcyclicity Part 2 (LaurentRefinement.lean:3737)                     ←[T-ACYC-PART2]
   └── laurentOverlapBridge_exists_compatible (:3173)                   ←[T-OVERLAP-COMPAT]
          └── bivariate Example 6.38 primitive                          ←[T-OV-1]
   └── refines_by_standard_cover (StandardCover.lean:631)
          └── hZavyalov hypothesis (Wedhorn Prop 7.14)                  ←[T-NULL-7]
   └── restrictionMapHom_injective (via refinement injection)           ←[T-INJ-1]
```

Six Tate-core sorries remain (verified via
`awk '/^[[:space:]]*sorry[[:space:]]*$/' "Adic spaces"/*.lean`):

| File:line | Declaration | Ticket | Critical? |
|---|---|---|---|
| `LaurentRefinement.lean:3173` | `laurentOverlapBridge_exists_compatible` | T-OVERLAP-COMPAT | ✅ |
| `LaurentRefinement.lean:3737` | `tateAcyclicity` Part 2 (gluing) | T-ACYC-PART2 | ✅ |
| `PresheafTateStructure.lean:1322` | `restrictionMapHom_injective` | T-INJ-1 | ✅ |
| `PresheafTateStructure.lean:1208` | `restrictionMap_isLocalization` / sigma surj | T-BAIRE | off path |
| `StructureSheaf.lean:1096` | `isSheafy...flat.embedding` | downstream | off path |
| `Presheaf.lean:720` | `spa_point_nonOpen_of_rational_subset` | retired | off path |

## Open tickets (ordered by leverage)

### [T-OV-1] Bivariate Example 6.38 primitive

- **Status**: open
- **Blocker for**: T-OVERLAP-COMPAT, hence T-ACYC-PART2.
- **Target file**: new section at the end of `Adic spaces/Example638.lean`
  (or new file `Adic spaces/LaurentOverlap.lean` if it grows).
- **Statement** (target):
  ```lean
  noncomputable def example638Bivariate_equiv
      (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
      [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
      (P : PairOfDefinition B) [IsNoetherianRing P.A₀]
      (b : B) (hb_pb : TopologicalRing.IsPowerBounded b)
      (hb_unit_in_overlap : ...) :
      presheafValue (overlapDatum B P b) ≃+*
        LaurentCover.B₁₂_gen b
  ```
  where `overlapDatum B P b : RationalLocData B` is the bivariate
  Laurent-overlap datum at `b` over `B`.
- **Proof strategy (composition route, preferred)**:
  Leverage existing infrastructure rather than building from scratch:
  1. **Iteration via Lemma 2.13**: realize `laurentOverlapDatum D₀ f` over
     `A` as `laurentMinusDatum (laurentPlusDatum D₀ f) f`; apply
     `presheafValue_iteratedMinus_equiv` at base = `laurentPlusDatum D₀ f`
     with `f`. Result: iso with
     `presheafValue(iteratedMinusDatum_B ... (laurentPlusDatum) f)`
     (rational data over `B_plus := presheafValue (laurentPlusDatum D₀ f)`).
  2. **Example 6.38 minus at `B_plus`**: the iteratedMinus datum over
     `B_plus` has `s = canonicalMap_{plus}(f), T = {1}`, so by the generic
     `example638Minus_equiv` it is ≃ `B_plus⟨X⟩ / (1 − canonicalMap_{plus}(f)·X)`.
  3. **`laurentPlusBridge` identifies `B_plus` with `B₁_gen(D₀.canonicalMap f)`**
     (already proved). Under this iso, `canonicalMap_{plus}(f)` becomes
     the image of `Y` in `B⟨Y⟩/(D₀.canonicalMap f − Y)`, which equals
     `D₀.canonicalMap f` in that quotient.
  4. **Algebraic final step**: identify
     `(B⟨Y⟩/(f_B − Y))⟨X⟩ / (1 − Y·X)` with
     `LaurentTateAlgebra B / (f_B − ζ) = B₁₂_gen(f_B)`. This is essentially
     the standard `B⟨ζ, ζ⁻¹⟩ ≃ B⟨Y, X⟩ / (1 − YX)` combined with a shared
     `/(f_B − ζ)` quotient.
- **Proof strategy (direct evalHom route, alternative)**:
  1. Define `evalBivariateHom : LaurentTateAlgebra B →+* presheafValue(overlapDatum B P b)`
     sending `ζ ↦ coeRingHom_B b` and `ζ⁻¹ ↦ coeRingHom_B (1/b)` (which
     exists in the overlap completion since `b` is a unit there).
  2. Show it factors through `laurentFSubZetaIdeal b`, giving
     `B₁₂_gen b →+* presheafValue(overlapDatum B P b)`.
  3. Backward via dense algebraic localization + `Completion.extensionHom`.
  4. Round trips via `Completion.ext'`.
- **Estimated lines**: ~300 (composition) or ~500 (direct).
- **Risk**: threading `PairOfDefinition` and `IsNoetherianRing` instances
  through the `B_plus`-level Example 6.38 invocation (route 1) is
  mechanically tedious but has no novel content. The final algebraic
  iso (step 4) is the genuinely new piece.

### [T-OVERLAP-COMPAT] Close `laurentOverlapBridge_exists_compatible`

- **Status**: open, blocked on T-OV-1.
- **File**: `Adic spaces/LaurentRefinement.lean:3173`.
- **Task**: once T-OV-1 is available, instantiate it at
  `B := presheafValue D₀, b := D₀.canonicalMap f` to produce the
  `τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+* B₁₂_gen (D₀.canonicalMap f)`.
  Then verify the two `LaurentOverlapBridgeCompatible` intertwining
  identities by composition on generators (reduce to `Completion.ext'` +
  `IsLocalization.ringHom_ext`, as done for
  `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`).
- **Estimated lines**: ~80.

### [T-ACYC-PART2] `tateAcyclicity` Part 2 assembly

- **Status**: open, blocked on T-OVERLAP-COMPAT + T-NULL-7.
- **File**: `Adic spaces/LaurentRefinement.lean:3737`.
- **Task**: replace the sorry with a composition:
  1. `hZavyalov`-discharged `refines_by_standard_cover` produces a
     standard cover `S` refining `C`.
  2. Induct on `|S.elts|`: base case uses
     `laurentCover_gluing_presheaf` (sorry-free once T-OVERLAP-COMPAT
     lands), inductive step splits via a Laurent cover at one element of
     `S`.
  3. Use `tateAcyclicity_gluing_via_refinement` +
     `gluing_of_finer_rational` to transfer gluing back to `C`.
- **Estimated lines**: ~50 once prerequisites land.
- **Note**: also uses `restrictionMapHom_injective` (T-INJ-1) inside
  `tateAcyclicity_gluing_via_refinement`, but that dependency is
  independent of the T-OV-1 chain.

### [T-INJ-1] `restrictionMapHom_injective` — blocks Part 1

- **Status**: open, two routes each with a hard blocker.
- **File**: `Adic spaces/PresheafTateStructure.lean:1322`.
- **Route A** (algebraic NZD, conditional):
  `restrictionMapHom_injective_via_iso` (already proved, line 1349)
  reduces the sorry to: `mk(D.s)` is a non-zero-divisor in
  `A⟨X'⟩/(1 − D₀.s · X')`, which would follow from a symmetric version
  of the already-proved `mk_D₀s_isUnit` (which gives NZD in the OPPOSITE
  quotient). The asymmetry (from `R(D) ⊆ R(D₀)`) is documented in the
  docstring at `:1293-1301`.
- **Route B** (via faithful flatness, Cor 8.32):
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  (`Cor832.lean:1202`) gives Part 1 conditional on
  `coeRingHom_preserves_proper`, which reduces (via T-IDEAL-1, DONE) to
  T-IDEAL-2 (BLOCKED, below).
- **Estimated lines**: ~30 once either blocker discharged.

## Blocked tickets

### [T-IDEAL-2] Closedness of `Ideal.map algebraMap p` — BLOCKED

- **Status**: blocked on upstream Mathlib content.
- **Blocker**: Bourbaki CA III §2.8 (`Submodule.isClosed_of_fg` for complete
  T2 linearly-topologized rings) — not in Mathlib. See memory
  `project_T001_completion_route.md`.
- **Target statement**: for `p : Ideal A` prime with `D.s ∉ p`,
  `Ideal.map (algebraMap A (Loc.Away D.s)) p` is closed in `Loc.Away D.s`.
- **Unlocks**: T-INJ-1 Route B (via `coeRingHom_preserves_proper`).
- **Estimated lines**: ~500-800 including Bourbaki port.

### [T-NULL-7] Wedhorn Prop 7.14 (adic Nullstellensatz) — BLOCKED (shares Bourbaki with T-IDEAL-2)

- **Status**: blocked.
- **Task**: close `hZavyalov` hypothesis in `refines_by_standard_cover`
  (`StandardCover.lean:640`) unconditionally. Reference: Wedhorn Prop 7.14
  / Lemma 7.44.
- **Blocker analysis (2026-04-17)**: the dependency chain reduces T-NULL-7
  to the **same upstream obstruction as T-IDEAL-2**:
  1. `hZavyalov` needs a finite `S ⊆ A` satisfying the three refinement
     clauses.
  2. Zavyalov's construction produces `S := T.image (σ⁻¹ · ·)` via Cor 7.32
     applied to a no-common-zero family `T ⊆ A` on `Spa A A⁺`.
  3. For `T` to exist with `Ideal.span T = ⊤` **in `A`**, we need the
     `spanTop_iff_noCommonZero_spa` equivalence (StandardCover.lean:310),
     which requires `[IsAdicComplete P.I P.A₀]` on **`A` itself** —
     not satisfied in general (only `presheafValue` is complete).
  4. The A-level span-top is available from a completion-level span-top
     only via `coeRingHom_preserves_proper` transfer — **= T-IDEAL-2**
     (Bourbaki CA III §2.8).
  5. Separately, Cor 7.32 (`exists_dominating_unit`) requires
     `MulArchimedean` on all `Spv A` value groups, an additional
     signature incompatibility with `tateAcyclicity`.
- **Consequence**: T-NULL-7 and T-IDEAL-2 are not independent; both are
  downstream of the Bourbaki port. No parallel leverage between them.
- **Unlocks**: clean Part 2 closing via T-ACYC-PART2.
- **Estimated lines**: ~300+ **on top of** Bourbaki + MulArchimedean
  removal.

### [T-BAIRE] `restrictionMap_isLocalization` / sigma surj — NOT STARTED

- **Status**: off the Route-B critical path (we use bridges, not sigma surj).
- **File**: `Adic spaces/PresheafTateStructure.lean:1208`.
- **Task**: Baire-category argument for the sigma surjection, a.k.a.
  Wedhorn Prop 8.15.
- **Estimated lines**: ~200+.

## Infrastructure already landed (no sorries)

| File | Lines | Content |
|---|---|---|
| `Cor832.lean` | 1357 | Full Cor 8.32 framework, reduced to `coeRingHom_preserves_proper` residual. T-IDEAL-1 (`one_mem_closure_coeRingHom_image`) at `:1289`. |
| `Example638.lean` | 1501 | Generic Example 6.38 plus + minus equivs (`example638Plus_equiv`, `example638Minus_equiv`). |
| `StandardCover.lean` | 733 | `refines_by_standard_cover` modulo `hZavyalov` hypothesis. |
| `ValuationSpectrumCompact.lean` | 1035 | `CompactSpace (Spv A)` (Huber port). |
| `SpaCompact.lean` | 460 | `CompactSpace ↥(Spa A A⁺)` (discrete + Tate cases). |
| `Cor732.lean` | 292 | Wedhorn Cor 7.32 — dominating unit. |
| `RationalRefinement.lean` | — | `separation_of_finer_rational`, `gluing_of_finer_rational`. |
| `LaurentRefinement.lean` | 3819 | Bridge chain (plus, minus, their `_restrictionMap` companions), Lemma 2.13 iterated equivs, `laurentBridge_delta_eq_zero_of_compat`. |

Bridge chain status (all 0 sorry apart from the 2 noted above):
- `laurentPlusBridge`, `laurentMinusBridge`: DONE.
- `laurentPlusBridge_restrictionMap`, `laurentMinusBridge_restrictionMap`: DONE.
- `presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`: DONE.
- `laurentCover_gluing_presheaf`: proved modulo `laurentOverlapBridge_exists_compatible` (the T-OVERLAP-COMPAT sorry).

## Recently completed (session log, newest first)

- **2026-04-17**: Docs refresh — `plan.md` and `tickets.md` rewritten to
  match codebase state (commit `e75dd6f`).
- **2026-04-16**: T-IDEAL-1 closed (`one_mem_closure_coeRingHom_image`,
  topological approximation, commit `6a5f891`).
- **2026-04-16**: Cor 8.32 abstract framework + reduction chain to
  `coeRingHom_preserves_proper`.
- **2026-04-16**: T-INJ-NZD (`mk(D₀.s)` is unit in `A⟨X⟩/(1-D.s·X)` under
  iso-hypotheses — half of T-INJ-1 Route A).
- **2026-04-15/16**: Wedhorn Prop 6.18 port
  (`tateQuotientToPresheafHom_continuous_of_tate`, unconditional).
- **2026-04-15**: R3 complete (`example638Plus_equiv`,
  `example638Minus_equiv` generic). Extracted to `Example638.lean` to
  break import cycle.
- **2026-04-15**: R1 scaffolded (`refines_by_standard_cover`,
  `StandardCover.lean`).
- **Q3-STEP2/2A/2C/2D**: Wedhorn Lemma 2.13 iterated rational
  identification — DONE.
- **T-PLUS/MINUS-FWD/BWD-PB**: all power-boundedness obligations for
  iterated-rational forward/backward locHoms — DONE.
- **T-WEDHORN-1** (`productRestriction_injective_tate` packaging),
  **T-NULL-0/0a/1** (Spa/Spv compactness + Cor 7.32): DONE.

## Parallelism analysis

**Genuinely independent (can run concurrently)**:
- **T-OV-1** (bivariate Example 6.38) — purely algebraic-topological.
- **T-INJ-1 Route A** (algebraic NZD) — Krull intersection on source
  quotient `A⟨X'⟩/(1 − D₀.s · X')`.

**Shared blocker cluster** (all reduce to Bourbaki CA III §2.8):
- **T-IDEAL-2** — closedness of `Ideal.map algebraMap p` in `Loc.Away s`.
- **T-NULL-7** — see blocker analysis under its ticket (`hZavyalov`
  needs span-top in `A`, which lifts to presheafValue via
  `coeRingHom_preserves_proper` = T-IDEAL-2).
- **T-INJ-1 Route B** — via `productRestriction_injective_tate_via_coeRingHom_preserves_proper`.

So there are **two independent fronts**, not three:
- Algebraic front: T-OV-1, T-OVERLAP-COMPAT, T-INJ-1 Route A.
- Bourbaki front: T-IDEAL-2 ⇒ { T-NULL-7, T-INJ-1 Route B }.

T-ACYC-PART2 needs *both* fronts to close (T-OVERLAP-COMPAT for Route B
gluing + T-NULL-7 for the standard-cover reduction + T-INJ-1 for the
refinement-transfer injectivity).

## Suggested execution order

1. **T-OV-1** (single-focus session, composition route): ~300 lines if
   infrastructure threading goes smoothly. Biggest single lever remaining
   on the algebraic front.
2. **T-OVERLAP-COMPAT** immediately after T-OV-1 (~80 lines).
3. **T-INJ-1 Route A** (algebraic NZD on source): in parallel with (1);
   ~100-200 lines.
4. **Bourbaki CA III §2.8 port** (upstream Mathlib work): unblocks
   T-IDEAL-2 → T-NULL-7 → (alternative T-INJ-1 Route B). Multi-session
   project; see memory `project_T001_completion_route.md`.
5. After all of the above:
   **T-ACYC-PART2** (~50 lines) assembly.

## Notes and reminders

- Signature of `tateAcyclicity` must NOT change (no new hypotheses, no
  `[IsDomain A]`, no `[DiscreteTopology A]`, no `hZavyalov`,
  no `MulArchimedean`).
- `_pairOfDefinition_concrete` API (`PresheafTateStructure.lean`) gives
  the `P_B.A₀ = presheafValue_ringOfDef D₀` definitional equality needed
  when threading Example 6.38 at `B := presheafValue D₀`.
- For T-OV-1 composition route, the `LaurentNormalized` typeclass on
  `laurentPlusDatum D₀ f` needs an instance; check
  `LaurentRefinement.lean` for the existing `LaurentNormalized` instances.
- The historical `docs/plans/2026-04-14-acyclicity-completion.md` is
  superseded for critical-path planning; see its §"2026-04-15
  reviewer-guided plan revision" for the R1-R7 roadmap that's now ~80%
  landed.
