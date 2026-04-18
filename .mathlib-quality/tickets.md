# Ticket Board — `tateAcyclicity` Completion

**Last refreshed**: 2026-04-18 (incorporates AI reviewer guidance).

## 2026-04-18 reviewer-guided pivot

The AI reviewer (full transcript in session log) delivered three
architectural corrections that supersede prior planning:

1. **`T-INJ-1` Route A is structurally wrong** — individual
   restriction maps `restrictionMapHom D₀ D h` are **not injective in
   general**. Reviewer's counterexample: `A = k⟨T, U⟩/(TU)`, with
   `U = R(1/T)`; `𝒪_X(U) ≅ A⟨X⟩/(1 − TX)`, and the class of `U ∈ A`
   maps to `U = U · (TX) = (UT)·X = 0`, killing a nonzero element.
   Radical containment of `D.s` in `(D₀.s, D₀.T)` does NOT force
   regularity. → Route A is **retired**.

2. **`T-INJ-1` → reframe as cover-level injectivity**. The correct
   injectivity is for the *product* restriction
   `𝒪_X(base) → ∏ᵢ 𝒪_X(Uᵢ)`, which is faithfully flat hence injective
   (Wedhorn Cor 8.31 / 8.32). This is what the single-Laurent exact
   row actually uses. The existing `restrictionMapHom_injective`
   sorry in `PresheafTateStructure.lean:1322` is **off the critical
   path** and should stay sorry'd (or be retired if no downstream
   callers need the false statement).

3. **`T-IDEAL-2` is NOT the Bourbaki CA III §2.8 content**. The
   reviewer flagged the completion-preimage shortcut
   (`q̄ = ι⁻¹(closure(ι(q)))`) as circular. The correct route is
   **Artin–Rees on the ring of definition** `D = A₀[T/s]` with ideal
   `J = I·D`. Artin–Rees in Mathlib ([Stacks 00IN](https://stacks.math.columbia.edu/tag/00IN))
   shows f.g. ideals in noetherian adic `D` are `J`-adically closed;
   passage to `A_s = D[1/π]` is the Tate-specific lift. This avoids
   Bourbaki entirely.

### New critical path

```
tateAcyclicity Part 1 (cover-level injectivity, Cor 8.32)
   └── productRestriction_injective_tate_via_coeRingHom_preserves_proper  ✅ proved (Cor832.lean:1202)
          └── coeRingHom_preserves_proper                                 ← residual
                 ├── T-IDEAL-1 (topological approx)            ✅ DONE
                 └── T-IDEAL-2 (closedness via Artin-Rees)     ← NEW ATTACK SURFACE

tateAcyclicity Part 2 (Laurent refinement induction)
   └── laurentOverlapBridge_exists_compatible                 ←[T-OVERLAP-COMPAT]
          └── bivariate Example 6.38 primitive (composition)  ←[T-OV-1, IN PROGRESS]
   └── geometric reduction (Hübner Lemma 3.8 / Wedhorn 8.33)  ←[T-GEOM-RED, NEW]
   └── cover-level injectivity                                ← from Part 1 framework
```

`T-INJ-1` (single-map) is gone. `T-NULL-7` becomes `T-GEOM-RED` — the
minimal geometric reduction statement needed for the Hübner/Wedhorn
induction, not the full Wedhorn Prop 7.14 Nullstellensatz.

### Reviewer references
- Hübner, *Adic spaces* (arXiv 2405.06435), Lemma 3.7, Lemma 3.8 —
  simple-Laurent covering input suffices for sheafy+acyclic.
- Wedhorn Prop 6.17 — closed ideals in noetherian Tate rings (for
  topology transport in T-OV-1).
- Wedhorn Cor 8.31 / 8.32 — cover-level faithful flatness.
- Bosch, *Lectures on Formal and Rigid Geometry*, Prop 6.4/8 — model
  for formal-function/Artin-Rees arguments (cited by Zavyalov App A).

---

**Target**: `ValuationSpectrum.tateAcyclicity`
(`Adic spaces/LaurentRefinement.lean:3671`) sorry-free, signature unchanged
(`[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(C : RationalCovering A) (hne : C.covers.Nonempty)`).

## Current state at a glance

**Superseded by the 2026-04-18 reviewer pivot above.** See new
critical-path graph there. The `restrictionMapHom_injective` dependency
in Part 1 is a false lead; real injectivity is cover-level (Cor 8.32).

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

- **Status**: IN PROGRESS — scaffold + **Step B closed** 2026-04-17 in
  `Adic spaces/LaurentOverlap.lean`. Step A remains.
- **Blocker for**: T-OVERLAP-COMPAT, hence T-ACYC-PART2.
- **Target file**: `Adic spaces/LaurentOverlap.lean` (new).
- **Landed (2026-04-17, 0 sorry / 0 warning)**:
  * `overlapDatum B P b := laurentMinusDatum (trivialPlusDatum B P b) b`;
    `overlapDatum_s`, `overlapDatum_P`, `overlapDatum_subset_plus`.
  * **`bivariateOverlap_ideal_eq`** (Wedhorn p.83 key identity):
    `Ideal.span{b - X, 1 - b·Y} = Ideal.span{b - X, X·Y - 1}` in `TateAlgebra₂ B`.
  * **`laurentIdeal_sup_bSubX`**: `laurentIdeal B ⊔ span{b - X} = span{b - X, XY - 1}`.
  * **`bivariateOverlap_equiv_B₁₂gen`** (T-OV-1 Step B, Wedhorn Lemma 8.33
    pure-algebra core):
    `TateAlgebra₂ B / (b - X, 1 - b·Y) ≃+* B₁₂_gen b`,
    via ideal-equality + third-iso-theorem (`DoubleQuot.quotQuotEquivQuotSup`).
    Axiom-clean (`propext, Classical.choice, Quot.sound` only).
- **Residual: Step A** (bivariate Example 6.38 — topology): prove
  `presheafValue (overlapDatum B P b) ≃+* TateAlgebra₂ B / (b - X, 1 - b·Y)`.
  Requires bivariate analogs of `example638Plus_evalHom` /
  `example638Minus_evalHom` (evaluation of `TateAlgebra₂ B` at
  `coeRingHom b` and `invS = coeRingHom (divByS 1 b)` in the overlap
  completion).
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

### [T-INJ-1] `restrictionMapHom_injective` — RETIRED from critical path (2026-04-18)

- **Status**: RETIRED per reviewer guidance. The claim is **false in
  general**: reviewer counterexample `A = k⟨T, U⟩/(TU)`,
  `U = R(1/T)`, shows that the class of `U ∈ A` maps to `0` in
  `𝒪_X(U) ≅ A⟨X⟩/(1 − TX)` (via `U = U·(TX) = (UT)·X = 0`).
- **Route A (algebraic NZD)** is structurally doomed: radical
  containment of `D.s` in `(D₀.s, D₀.T)` does not force regularity.
  All `h_Ds_nzd` / `h_ker_torsion` scaffolding landed 2026-04-17 is
  therefore chasing a false statement for the unconditional form.
- **Route B (via Cor 8.32)** is still valid but attacks the *product*
  injectivity, not single-map — so the proper target lives in
  `Cor832.lean`'s `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  (already conditional on `coeRingHom_preserves_proper` = T-IDEAL-2).
- **Existing sorry at `PresheafTateStructure.lean:1322`**: leave
  sorry'd; audit callers to ensure they don't rely on the false
  unconditional form. Part 1 of `tateAcyclicity` currently uses it at
  line 3695; rewrite Part 1 to invoke
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  (product-level, via the Cor 8.32 chain) once T-IDEAL-2 lands.
- **Estimated lines to rewrite Part 1 via product-level**: ~30.

## Blocked tickets

### [T-IDEAL-2] Closedness via Artin-Rees (NEW ATTACK SURFACE, 2026-04-18)

- **Status**: open, **no longer blocked** — reviewer guidance flips
  this from Bourbaki-dependent to Artin-Rees-tractable.
- **Target statement**: for `q : Ideal (Localization.Away D.s)` proper
  (`q ≠ ⊤`), `Ideal.map D.coeRingHom q ≠ ⊤` in `presheafValue D`.
  Equivalently (via T-IDEAL-1 DONE): f.g. ideals of `Localization.Away D.s`
  are closed in its localization topology.
- **Reviewer strategy (Artin-Rees on the ring of definition)**:
  1. Descend from `A_s = Localization.Away D.s` to the **ring of
     definition** `𝔇 := D.P.A₀[D.T / D.s]` with ideal `J := D.P.I · 𝔇`.
     `𝔇` is a topologically finite type algebra over `A₀`, hence also
     noetherian (Wedhorn's t.f.t. algebras preserve noetherian rings
     of definition — cited but may need porting).
  2. Given `q ⊆ A_s` with f.g. generators, its intersection `q_𝔇 := q ∩ 𝔇`
     is a f.g. `𝔇`-submodule of `𝔇`.
  3. **Artin-Rees** (Mathlib: `Ideal.isAdic`, `Ideal.isAdic.add_right`,
     and [Stacks 00IN](https://stacks.math.columbia.edu/tag/00IN))
     gives that the `J`-adic topology on `𝔇` induces the `J`-adic
     topology on `q_𝔇` — i.e., `q_𝔇` is `J`-adically closed in `𝔇`.
  4. Lift to `A_s = 𝔇[1/π]` where `π` is the pseudo-uniformizer: the
     localization topology on `A_s` has basis `J^m · A_s`, and every
     element of `A_s` is `π^{-n} · d` with `d ∈ 𝔇`. So closedness of
     `q_𝔇` in `𝔇` + clearing powers of `π` gives closedness of
     `q = q_𝔇[1/π]` in `A_s`.
  5. Apply T-IDEAL-1 (DONE) to get `1 ∉ closure(coeRingHom '' q)` in
     `presheafValue D`, hence `Ideal.map coeRingHom q ≠ ⊤`.
- **Scope / unlocked sub-tickets**:
  - **S-IDEAL-A** — noetherianness of `𝔇 = A₀[T/s]` (topologically
    finite type over noetherian base). Possibly already in Mathlib via
    `Algebra.FinitelyGenerated`.
  - **S-IDEAL-B** — Artin-Rees application: identify Mathlib's
    `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson_bot` or equivalent.
  - **S-IDEAL-C** — lift `J`-adic closedness in `𝔇` to localization-
    topology closedness in `A_s = 𝔇[1/π]`.
  - **S-IDEAL-D** — assembly: chain (S-IDEAL-A) + (S-IDEAL-B) +
    (S-IDEAL-C) into `coeRingHom_preserves_proper`.
- **Unlocks**: Part 1 of `tateAcyclicity` via
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  (Cor 8.32 chain, already proved modulo this residual).
- **Est. lines**: ~200-300 (no Bourbaki port needed).
- **Key references**: Stacks 00IN (Artin-Rees); Bosch LFRG Prop 6.4/8
  (formal-function-style arguments, cited by Zavyalov App A); the
  existing Mathlib `IsAdic` API.

### [T-GEOM-RED] Minimal geometric reduction (Hübner Lemma 3.8 / Wedhorn 8.33)

- **Status**: new ticket (2026-04-18), replacing T-NULL-7 on the
  critical path.
- **Reviewer framing**: Hübner's Lemma 3.8 says: if exactness holds
  for *every* simple Laurent covering of *every* rational open, the
  pair is sheafy and acyclic. This isolates the decisive local input
  as what T-OV-1 + T-OVERLAP-COMPAT + `laurentCover_gluing_presheaf`
  already provide.
- **Task**: port the minimum geometric reduction from Hübner / Wedhorn
  8.33. This is **not** the full Wedhorn Prop 7.14 (adic
  Nullstellensatz) — only the reduction step that converts
  "exactness on every simple Laurent cover" to "exactness on every
  finite rational cover."
- **Reference**: Hübner, *Adic spaces* (arXiv 2405.06435), Lemmas 3.7
  and 3.8. Note that Lemma 3.8's proof still goes through standard
  rational / Laurent refinements — the geometric reduction front is
  not eliminated, just clarified.
- **Est. lines**: TBD. Likely shorter than a full Prop 7.14 port
  because the target is weaker.

### [T-NULL-7] Wedhorn Prop 7.14 (adic Nullstellensatz) — SUPERSEDED by T-GEOM-RED

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

- **2026-04-17**: T-OV-1 **Step B closed** (Wedhorn Lemma 8.33 p.83 pure-algebra
  core): `bivariateOverlap_equiv_B₁₂gen` in `Adic spaces/LaurentOverlap.lean`,
  giving `TateAlgebra₂ B / (b - X, 1 - b·Y) ≃+* B₁₂_gen b` via ideal-equality
  (`bivariateOverlap_ideal_eq`) + third-iso-theorem. 0 sorry, axiom-clean
  (`propext, Classical.choice, Quot.sound` only). Residual for T-OV-1 is Step A
  (bivariate evalHom from `TateAlgebra₂ B` to `presheafValue(overlap)`).
- **2026-04-18**: T-INJ-1 Route A presheafValue-level torsion bridge —
  added `ker_torsion_of_restrictionMapHom_torsion` in
  `PresheafTateStructure.lean`. Transports the `h_ker_torsion`
  obligation across the Example 6.38 iso, reducing it to a
  **presheafValue-level** torsion bound on `restrictionMapHom`
  (native habitat of `away_lift_torsion_bounded`,
  `CompletionLocalization.lean:173`). Proof: match
  `D₀.canonicalMap D.s ↦ mk(algebraMap D.s)` via
  `presheafValue_tateAlgebra_quotient_iso_canonicalMap` and transport
  the torsion identity across `e_{D₀}` using `RingEquiv.map_pow` and
  `map_mul`. Axiom-clean (same trace as existing scaffolds).
- **2026-04-18**: T-INJ-1 Route A closure — added
  `restrictionMapHom_injective_via_Ds_nzd_and_ker_torsion` in
  `PresheafTateStructure.lean` (after
  `restrictionMapHom_injective_via_Φ_inj`). Closes
  `restrictionMapHom_injective` conditional on two purely algebraic
  inputs: (1) `h_Ds_nzd` — `mk(algebraMap D.s) ∈ nonZeroDivisors T_{D₀}`,
  and (2) `h_ker_torsion` — every element of `ker Φ` is killed by some
  power of `mk(algebraMap D.s)`. Proof: powers of an NZD remain NZD, so
  `ker Φ ⊆ r^N·T_{D₀}-torsion = 0`. Axiom trace matches existing
  infrastructure.
- **2026-04-17**: T-INJ-1 Route A scaffold — added
  `restrictionMapHom_injective_via_Φ_inj` in `PresheafTateStructure.lean`
  (after `mk_D₀s_mem_nonZeroDivisors`). Fully conjugates by the Example
  6.38 iso on BOTH source (`D₀`) and target (`D`), reducing the sorry to
  injectivity of the concrete ring hom `Φ : T_{D₀} → T_D` between
  Tate-algebra quotients. Axiom trace matches
  `restrictionMapHom_injective_via_iso` (no new dependencies). The
  residual `h_Φ_inj` is now the purely algebraic target for Route A,
  standardly reducible to `mk(algebraMap D.s) ∈ nonZeroDivisors T_{D₀}`.
- **2026-04-17**: T-OV-1 scaffold — created `Adic spaces/LaurentOverlap.lean`
  with `overlapDatum` definition, basic unfolding lemmas, and composition-route
  proof roadmap. Integrated into `Adic spaces.lean` import chain. 0 sorry.
  Ticket status: IN PROGRESS; composition steps 1–4 documented as a roadmap
  for future sessions.
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

## Parallelism analysis (revised 2026-04-18)

Three independent fronts, all without the Bourbaki blocker:

1. **Local/simple Laurent algebra front**:
   - T-OV-1 Step A (IN PROGRESS) → T-OVERLAP-COMPAT →
     `laurentCover_gluing_presheaf` sorry-free.
   - Purely algebraic-topological. Composition route confirmed by
     reviewer.
2. **Ring-of-definition / Artin-Rees front**:
   - T-IDEAL-2 via Artin-Rees on `𝔇 = A₀[T/s]` (NEW ATTACK).
   - Unblocks Part 1 via
     `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
     (already proved conditional on `coeRingHom_preserves_proper`).
   - No Bourbaki dependency; uses Mathlib's existing `IsAdic` /
     Artin-Rees API.
3. **Geometric reduction front**:
   - T-GEOM-RED (Hübner Lemma 3.8 / Wedhorn 8.33) — reduce arbitrary
     finite rational covers to simple Laurent covers.
   - Independent of the other two.

**T-ACYC-PART2 (Part 2 assembly)** needs all three fronts.
**Part 1** needs only front 2.

## Retired / superseded tickets (2026-04-18)

- **T-INJ-1 Route A** (algebraic NZD on source): RETIRED. Reviewer
  counterexample shows single-map injectivity is false.
- **T-NULL-7** (full Wedhorn Prop 7.14): SUPERSEDED by T-GEOM-RED
  (only the minimal reduction is needed, not full Nullstellensatz).
- **Bourbaki CA III §2.8 port**: no longer on critical path — Artin-Rees
  on the ring of definition supersedes it.

## Suggested execution order (revised 2026-04-18)

1. **T-OV-1 Step A** (in progress, composition route): finish bivariate
   Example 6.38 — topology. Blocker for T-OVERLAP-COMPAT.
2. **T-IDEAL-2 via Artin-Rees** (NEW): prove `coeRingHom_preserves_proper`
   via Artin-Rees on `𝔇 = A₀[T/s]`. Unblocks Part 1.
3. **T-OVERLAP-COMPAT** (after T-OV-1): ~80 lines.
4. **T-GEOM-RED** (parallel with 2): Hübner Lemma 3.8 port.
5. **Part 1 rewrite**: invoke
   `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
   at `LaurentRefinement.lean:3695` (after step 2).
6. **T-ACYC-PART2**: final assembly (after 1-5).

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
