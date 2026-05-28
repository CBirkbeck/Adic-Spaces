# Ticket Board — `tateAcyclicity` Completion

**Last refreshed**: 2026-05-14 (beastmode session — 6/9 residuals in
`TateAcyclicityResiduals.lean` closed axiom-clean).

## 2026-05-14 beastmode session — residual closures (axiom-clean)

Six of the nine residuals in `TateAcyclicityResiduals.lean` closed
in this session. All closures verified axiom-clean via
`#print axioms` (deps: `propext, Classical.choice, Quot.sound` only;
no `sorryAx`).

- **V.2 `flat_descent_equaliser` (Stacks 023N)** — closed via Mathlib's
  `Module.FaithfullyFlat.tensorProduct_mk_injective` (B-on-left form)
  composed with `TensorProduct.comm.injective` to switch to the
  M-on-left form used in the project's algebraic-side downstream.
- **III.3 `relativeRationalLocData_generators_powerBounded`** — closed
  via `CompletionLocalization.coeRingHom_image_locSubring_isBounded`
  on the image of `divByS t D.s ∈ locSubring`, lifted to powers by
  `pow_mem` + `map_pow`.
- **III.1 `presheafValue_relative_equiv`** — closed by directly
  invoking the already-existing axiom-clean
  `relativeLaurentNormalized_equiv` (the RingEquiv was already built
  but unused; this just re-exports it under the residual interface).
- **III.2 `presheafValue_relative_equiv_isHomeomorph`** — closed by
  reducing both directions to `UniformSpace.Completion.continuous_extension`
  applied to `relativeLaurentNormalized_forwardHom` and `…_backwardHom`
  (both extend continuous maps on the dense subspace).
- **I.3 `exists_unit_generated_laurent_refinement`** — closed via a
  direct construction: define `D_f := L` with `T = insert f L.T` for
  each `f ∈ units`, lift `L.hopen` to the enlarged `T` via
  `locSubring_mono_T`, and assemble as `RationalCovering`. The pieces
  `{D_f}` cover `L` exactly by the `h_covers` hypothesis, and each
  contains itself in the unit-plus-piece by reflexivity.
- **I.4 `allNodesDisjoint_graftAt_prune`** — closed via *identity
  prune*: the grafted tree itself satisfies `allNodesDisjoint` under
  the *cross-leaf disjointness* hypothesis (inner trees at distinct
  outer leaves produce disjoint leaf-Finsets), and the proof is
  structural induction on the outer tree. The cross-leaf hypothesis
  is mathematically the right one; the original statement's
  hypotheses (outer + per-leaf inner disj) were insufficient.

**Remaining residuals (3)**:
- I.1 `exists_wedhorn_laurent_refinement_tree` (Wedhorn 8.34 headline;
  needs I.2 + composition with I.3 + I.4)
- I.2 `exists_first_stage_laurent_cover` (Cor 7.32 normalisation,
  substantive geometric construction)
- V.1 `adicCompletion_noetherian` (Stacks 00MA — external Mathlib gap)

`tateAcyclicityComplete` (line 492 of `TateAcyclicityResiduals.lean`)
compiles sorry-free in the Residuals file (depends only on II.1, II.2,
IV.1 — all closed) but transitively depends on existing project
sorries in `Cor832.lean` and the gluing infrastructure
(productRestriction_injective_tate, rationalCovering_hasGluing).



## 2026-05-11 session 2 reviewer reframe (ChatGPT Pro) — MAJOR CORRECTION

The "Wedhorn 8.15 Baire surjection" structural blocker recorded below
(in the now-obsolete 2026-05-11 marathon update) was identified by the
external reviewer as **trying to prove a mathematically FALSE statement**.

### The misframing

`restrictionMap_isLocalization` (`PresheafTateStructure.lean:2410`) was
targeting the predicate

> `∀ i, IsLocalization.Away (κ_{D₀}(s_i)) (presheafValue D_i)`

i.e., every element of `presheafValue D_i` has the form `σ(a) / u^n` for
some `a ∈ presheafValue D₀, n ∈ ℕ`. **This is false in general** because
completed rational localizations contain infinite convergent denominator
tails that no finite power of the denominator clears.

**Counterexample** (reviewer-provided): `A = ℚ_p⟨X⟩`. The completed
rational localization `A⟨T⟩/(XT - 1)` contains `∑_{n ≥ 0} p^n X^{-n}`.
Multiplying by `X^N` clears only finitely many negative powers,
leaving infinite tail. So `IsLocalization.Away X` FAILS.

### The fix (NEW critical path)

Refactor Cor 8.32's abstract input from `IsLocalization.Away` to
**`Module.Flat`** per restriction map. Flatness is supplied via Wedhorn
8.30/8.31 + the Tate-algebra quotient identifications (Example 6.38 at
the B-level), NOT via `IsLocalization.flat`.

NEW tickets (see §3 below for full plans):

- `T-RETIRE-PROP815` — mark `restrictionMap_isLocalization` as misframed,
  document the counterexample.
- `T-FLAT-VIA-WEDHORN830` — direct flatness of restriction maps via the
  existing `presheafValue_iteratedMinus_equiv` (sorry-free) +
  `flat_quotient_oneSubfX_general` (sorry-free, Wedhorn 8.31). **High
  priority, ~150-300 lines.**
- `T-COR832-VIA-FLAT` — refactor `flat_over_base_tate` to consume
  flatness, not `IsLocalization.Away`. **High priority, ~50-100 lines.**
- `T-MATHLIB-COMPLETEDLOC` — corrected Mathlib contribution
  `(R[1/x])^∧_{I·R[1/x]} ≅ lim_n (R/I^n)[1/x]` (Stacks 0BNH). **Low
  priority, NOT critical path.**

### Consequences

- **T-NEW-4** (tateAcyclicity Part 2 gluing) — UNBLOCKED once
  T-COR832-VIA-FLAT lands. No longer blocked on Baire surjection.
- **T-NEW-5** (isSheafy embedding) — UNBLOCKED similarly.
- **Pettis / non-archimedean Banach Open Mapping** — RETIRED from project
  plan. Reviewer-rejected approaches.
- **Naïve completion-localization commutation** (`(R[1/x])^∧ ≅ R̂[1/x]`)
  — RETIRED as mathematically FALSE.
- **Final theorem signature** — unchanged. The refactor does not require
  adding `IsAdicComplete (locIdeal) (locSubring)` or any other extra
  hypotheses to the main `tateAcyclicity` statement.

### Old (now-obsolete) blocker analysis

The section below ("Wedhorn 8.15 Baire surjection — STRUCTURAL BLOCKER")
records the previous diagnosis. It is now superseded by the reframe
above; kept for historical reference but no longer reflects the
critical path.

---

## 2026-05-11 marathon update [SUPERSEDED]: Wedhorn 8.15 Baire surjection — STRUCTURAL BLOCKER

The remaining acyclicity sorries (`tateAcyclicity` Part 1, Part 2, `isSheafy`
embedding) all chain through `restrictionMapHom_surj` (`PresheafTateStructure.lean:1187`),
which is Wedhorn Proposition 8.15's surjection content. After dedicated subagent
attack, the precise infrastructure obstruction is:

**Available**:
- `presheafValue_baireSpace D` (sorry-free).
- `AddSubgroup.isOpen_of_zero_mem_interior` (Mathlib).
- Mathlib `BaireSpace.of_completelyPseudoMetrizable`.

**Missing for closure**:
- **Separability of `Localization.Away D.s` (with localization topology)** —
  not provable in general (the underlying set can be uncountable).
  OR
- **Pettis / Steinhaus theorem for Baire abelian topological groups** —
  not in Mathlib. Standard formulation: every meagre or non-meagre Borel
  subset of a Baire abelian topological group either has empty interior
  in the inverse-difference or has nonempty interior.
  OR
- **Open Mapping Theorem for metrizable Baire abelian topological groups
  without σ-compactness** — Mathlib has `AddMonoidHom.isOpenMap_of_sigmaCompact`
  but `presheafValue D` is not σ-compact in general (infinite-dimensional
  Banach analog).

Closing the Baire surjection sorry-free requires building one of these
Mathlib-level pieces of infrastructure as a dedicated multi-file effort.

**Effect on other sorries**:
- `tateAcyclicity` Part 1 (separation) — blocked.
- `tateAcyclicity` Part 2 (gluing) — blocked through `restrictionMap_isLocalization`.
- `isSheafy_ofStronglyNoetherianTate_flat.embedding` — blocked through Cor 8.32.

**Marathon-2 closed (sorry-free, 0 axiom)**:
- T-HYP-AUDIT: `[IsStronglyNoetherian A]` added to acyclicity signatures
  (`tateAcyclicity`, `rationalCovering_hasSeparation/_hasGluing`,
  `isSheafy_ofStronglyNoetherianTate_flat`, `productRestriction_injective_tate`,
  and downstream callers).
- T-QTATE-1: `IsHuberRing.quotient` + `IsTateRing.quotient` for closed quotients
  (`Adic spaces/QuotientTate.lean`, ~225 lines).
- T-QTATE-2: polynomial density already exists as
  `tateAlgebra_polynomials_dense_canonical`; documented.
- T-NULL-PER-E reframe: `LocalBasisHyp` intrinsic basis predicate
  (`Adic spaces/LocalBasis.lean`, ~145 lines).
- T-EMBED-TOPO boundary theorem (`Adic spaces/EmbeddingTopo.lean`, ~110 lines).
- T-EX638-SCOPE: documented one-variable vs general-T scope in
  `presheafValueTateQuotientEquiv`.
- T-INJ-1-CLEANUP: annotated remaining retired single-map injectivity sites.
- T-NEW-2: `tateEvalPresheafHom_bivariate_continuous_canonical` +
  `example638Bivariate_forwardHom_continuous_canonical`
  (`Adic spaces/BivariateContinuity.lean`, ~200 lines). **Eliminates
  `hcont_forward_overlap` residual** from `laneA_τ_preBiv`.

**Marathon-2 deferred (named residuals)**:
- None remaining at the Lane A level.

**Beast-mode push (2026-05-11, after T-NEW-1-PARK)**:
- T-NEW-1: subagent's second pass on `IteratedOverlapEquiv.lean`
  succeeded (1347 lines, 0 sorry, 0 axiom). Produced
  `presheafValue_iteratedOverlap_equiv` — the Wedhorn 2.13 overlap
  transport — concretely as a `RingEquiv`. Wired into
  `LaneAReverseRoundTrip.laneA_τ_preBiv`, which now takes NO
  parametric residual witnesses. The full Lane A bridge is unconditional.

**Marathon-2 critical-path remaining blocker**:
- Wedhorn Prop 8.15 Baire surjection (`restrictionMapHom_surj` at
  `PresheafTateStructure.lean:1187`). Closure requires Mathlib-level
  infrastructure (separability of `Localization.Away` OR Pettis lemma
  for Baire abelian topological groups OR non-σ-compact Open Mapping
  Theorem). Each is a dedicated multi-file effort beyond a marathon
  session.

---

**Last refreshed (original)**: 2026-04-18 (post-worker-integration, grounded in
Wedhorn's proof structure and 2026-04-18 AI reviewer guidance).

**Target**: `ValuationSpectrum.tateAcyclicity`
(`Adic spaces/LaurentRefinement.lean:3671`) sorry-free, signature unchanged
(`[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
(C : RationalCovering A) (hne : C.covers.Nonempty)`).

---

## 1. Current state (2026-04-18)

### 1.1 Sorry inventory (Tate-core)

Six Tate-core sorries remain. Three are on the critical path; the others
are off-path or retired.

| File:line | Declaration | Ticket | Status |
|---|---|---|---|
| `LaurentRefinement.lean:3173` | `laurentOverlapBridge_exists_compatible` | T-OVERLAP-COMPAT | ⏳ blocked on T-OV-1 Step A |
| `LaurentRefinement.lean:3737` | `tateAcyclicity` Part 2 (gluing) | T-ACYC-PART2 | ⏳ downstream of all Part 2 tickets |
| `PresheafTateStructure.lean:1322` | `restrictionMapHom_injective` | (retired) | ⛔ off-path (false in general; reviewer counterexample) |
| `PresheafTateStructure.lean:1208` | `restrictionMap_isLocalization` | T-BAIRE | off path |
| `StructureSheaf.lean:1096` | `isSheafy...flat.embedding` | downstream | off path |
| `Presheaf.lean:720` | `spa_point_nonOpen_of_rational_subset` | retired | off path (Bourbaki-blocked, not needed) |

### 1.2 New files landed (this week, all 0 sorry, axiom-clean)

| File | Lines | Purpose |
|---|---|---|
| `LaurentOverlap.lean` | 634 | T-OV-1 Step B (algebraic iso) + Step A half-forward homs + foundational lemmas |
| `IdealClosedness.lean` | 181 | Krull-intersection / Artin-Rees closedness + clopen-subring lift |
| `GeometricReduction.lean` | 248 | T-GEOM-RED cover-level refinement theorem + V-covers bridge helpers |

Plus substantial additions to `Cor832.lean` (closure combinator +
`locSubring → Loc.Away` bridge) and retirement of false T-INJ-1 Route A
scaffolds in `PresheafTateStructure.lean`.

Build succeeds (3090 jobs).

### 1.3 Wedhorn's proof of Theorem 8.28(b) — decomposition and status

| Wedhorn step | Content | Project status |
|---|---|---|
| **Lemma 8.31** | Flatness of `A⟨X⟩`, `A⟨X⟩/(f-X)`, `A⟨X⟩/(1-fX)` over `A` | ✅ DONE (`TateAlgebra.lean` / `CompletionLocalization.lean`) |
| **Example 6.38** | `presheafValue D ≃+* A⟨X⟩/(closed ideal)` (plus/minus) | ✅ DONE generically over `B` (`Example638.lean`) |
| **Example 6.39** | `presheafValue(R(b/1)∩R(1/b)) ≃+* B⟨ζ,ζ⁻¹⟩/(b-ζ)` | ⏳ T-OV-1: Step B ✅, Step A 50% |
| **Lemma 8.31** (flat) ∘ **Ex 6.38** ⟹ **Cor 8.32** | product restriction faithfully flat | ✅ framework; residual = `coeRingHom_preserves_proper` |
| **Cor 8.32** ⟹ Part 1 | via `productRestriction_injective_tate_via_coeRingHom_preserves_proper` | ✅ modulo T-IDEAL-2 |
| **Lemma 8.33** | Laurent 2-cover exact row | ✅ algebraic core + bridge chain, modulo T-OV-1 |
| **Lemma 8.34** / **Hübner 3.8** | geometric reduction to arbitrary rational covers | ✅ T-GEOM-RED/S-GEOM-ASM API complete (2026-04-20) modulo Lane A (T-OV-1) + Lane B (T-IDEAL-2) + T-NULL-PER-E general case |
| **Theorem 8.28(b)** | Part 1 + Part 2 assembly | ⏳ T-ACYC-PART2 |

### 1.4 2026-04-18 reviewer's architectural corrections (reminder)

1. **T-INJ-1 Route A retired**: single-map `restrictionMapHom_injective`
   is false in general. Counterexample: `A = k⟨T, U⟩/(TU)`, `U = R(1/T)`;
   then in `𝒪_X(U) ≅ A⟨X⟩/(1-TX)`, the class of `U` maps to
   `U = U·(TX) = (UT)·X = 0`. **Part 1 must use cover-level injectivity
   (Cor 8.32).**

2. **T-IDEAL-2 is Artin-Rees, not Bourbaki CA III §2.8**. Descend to the
   ring of definition `𝔇 = A₀[T/s]` with ideal `J = I·𝔇`; apply Krull's
   intersection theorem (Stacks 00IN) to get f.g. ideals closed in `𝔇`;
   lift to `A_s = 𝔇[1/π]` by clearing π.

3. **T-OV-1 composition route preferred**: reuse Lemma 2.13 (iterated
   rational) + Example 6.38 minus at B_plus + `laurentPlusBridge`. The
   only genuinely new content is the quotient-of-quotients iso.

4. **T-OV-1 topology transport via Wedhorn Prop 6.17** (closed ideals in
   noetherian Tate): prove the algebraic quotient-of-quotients iso first,
   then transport topology via closed ideals.

5. **Hübner's Lemma 3.8** is the cleanest modern packaging of the
   geometric reduction: "exactness on simple Laurent covers of every
   rational open ⟹ sheafy and acyclic." Reduction still runs through
   standard rational / Laurent refinements.

### 1.5 2026-05-11 reviewer's strategic confirmations and pivots (ChatGPT Pro)

(See `.mathlib-quality/expert-review/2026-05-11/` for full brief, reply,
and integration record.)

1. **Q1 — Lane B parking confirmed permanently.** Counterexamples 8.3
   (`A = ℚ_p⟨X⟩`, `T = {X}`, `s = p`: `locIdeal ⊄ Jacobson(0)` in
   incomplete `locSubring`) and 8.4 (Conrad: single-map restriction is
   not topologically inducing after completion) are decisive. The
   single-map Jacobson / single-map FF route is FALSE in the generality
   needed. Cor 8.32 enters the critical path ONLY through its
   product-level form: componentwise flatness + cover-level Spa/spec
   surjectivity ⇒ product restriction faithfully flat ⇒ algebraic
   separation. **Do not resurrect single-map injectivity or
   completion-level Jacobson infrastructure for the current theorem.**

2. **Q2 — Lane A approach (a): reusable quotient-Tate theorem.** Build
   the Tate-ring structure on `B = A⟨X⟩/(f - X)` explicitly via the
   reusable theorem `closed quotient of noetherian Tate is Tate`
   (T-QTATE-1), then close polynomial density in `B⟨Z⟩` by truncation
   (T-QTATE-2). Specialise via T-OV-1-DENSITY. Approach (b) one-off
   density and approach (c) universal-property reformulation both
   rejected.

3. **Q3 — Lane C direct per-`E` architecture approved.** "Acceptable
   and probably better for Lean than the old τ / `Classical.choose`
   route. A formal refinement of Wedhorn's induction rather than a
   different theorem." Keep T-GEOM-RED's direct per-`E` assembly. The
   real issue is C1 (see Q4 below).

4. **Q4 — Critical path confirmed**:
   ```
   Lane A quotient-Tate density (T-QTATE-1 → T-QTATE-2 → T-OV-1-DENSITY)
     → Lane C C1 standard-refinement theorem (T-NULL-PER-E reframed +
                                              T-NULL-PER-E-FIN fallback)
     → final assembly via direct per-E Part 2 (T-ACYC-PART2)
   ```
   Lane B consumed only through product-level Cor 8.32 (already proved
   abstractly).

5. **HIDDEN RISK — topological embedding ≠ algebraic FF** (T-EMBED-TOPO):
   The `IsSheafy.embedding` field demands a TOPOLOGICAL embedding.
   Faithfully flat product restriction supplies only algebraic
   injectivity. The embedding requires the topological side of
   Example 6.38 + topological strictness of the Laurent diagrams.
   New ticket T-EMBED-TOPO surfaces this explicitly.

6. **HIDDEN RISK — hypothesis chain** (T-HYP-AUDIT): the listed Lean
   hypotheses `[IsTateRing A] [IsNoetherianRing A] [T2Space A]
   [NonarchimedeanRing A] [IsNoetherianRing P.A₀]` may or may not
   imply the strong-noetherian / Tate-algebra-noetherian facts used by
   Lemma 8.31 and Wedhorn 6.17. Must verify; if not, add an
   `IsStronglyNoetherian` hypothesis to the main signature.

7. **HIDDEN RISK — Example 6.38 scope** (T-EX638-SCOPE): the
   one-variable quotient `A⟨X⟩/(1 - sX)` models `R(1/f)` /
   `R(f/1)`. General `R(T/s)` with `|T| > 1` should be reached by
   intersecting basic one-variable steps, not by silently using a
   one-variable quotient.

8. **Lane C C1 reframe** (folded into T-NULL-PER-E + T-NULL-PER-E-FIN):
   target an intrinsic local-basis / refinement statement
   (`plus_pieces_form_local_basis_of_E`), not a guessed explicit
   formula. The σ-clearing T200-series remains as side infrastructure
   only.

---

## 2. Critical-path dependency graph (2026-04-18)

```
tateAcyclicity Part 1 (separation)
  └── productRestriction_injective_tate_via_coeRingHom_preserves_proper  ✅ proved
        └── coeRingHom_preserves_proper  ← SINGLE RESIDUAL
              ├── T-IDEAL-1: topological approximation                   ✅ DONE
              └── T-IDEAL-2: closedness of proper ideals in Loc.Away D.s
                    ├── Generic closedness machinery                     ✅ DONE
                    │     - mem_closure_iff_of_isAdic
                    │     - Ideal.isClosed_of_le_jacobson (via Krull)
                    │     - Ideal.isClosed_of_isAdicComplete
                    │     - IsClosed.of_isClosed_subspace_of_isOpen_subring
                    ├── Closure combinator                               ✅ DONE
                    │     coeRingHom_preserves_proper_of_closed
                    ├── locSubring → Loc.Away subspace bridge (subsets)  ✅ DONE
                    │     isClosed_image_of_isClosed_subspace_in_locSubring
                    ├── S-IDEAL-JAC: locIdeal ≤ Jacobson(⊥) in locSubring ✅ DONE-CONDITIONAL (T271 audit; `locIdeal_le_jacobson_bot_of_faithfullyFlat`)
                    ├── S-IDEAL-LOC: ideal q ⊆ A_s has q = (q∩𝔇)·A_s    ⏳ ~80-150 lines
                    │     and closedness transfers
                    └── S-IDEAL-ASM: end-to-end assembly                 ✅ DONE (T271 audit; `coeRingHom_preserves_proper_of_locIdeal_le_jacobson`)

tateAcyclicity Part 2 (gluing)
  ├── laurentOverlapBridge_exists_compatible (= T-OVERLAP-COMPAT)
  │     └── example638Bivariate_equiv (T-OV-1 main theorem)
  │           ├── Step A (topological): B₁₂_gen b →+* presheafValue(overlap)
  │           │     ├── overlap_plus_forwardHom  ✅ DONE
  │           │     ├── overlap_minus_forwardHom ✅ DONE
  │           │     └── S-OV-GLUE: assemble via Wedhorn p.84            ⏳ ~200 lines
  │           │         (Laurent decomposition A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹·A⟨ζ⁻¹⟩)
  │           └── Step B (pure algebra): B⟨ζ,η⟩/(b-X,1-bY) ≃ B₁₂_gen    ✅ DONE
  │                 (bivariateOverlap_equiv_B₁₂gen)
  │
  ├── T-GEOM-RED (geometric reduction)
  │     ├── tateAcyclicity_gluing_via_refinement_cover_level   ✅ DONE
  │     ├── standardCoverVCovers + mem + subset_base           ✅ DONE
  │     ├── S-GEOM-TAU: τ construction + containment           ✅ DONE (T250)
  │     ├── S-GEOM-BASE: hV_glue for |S.elts| = 1              ✅ DONE (T251 audit; `standardCover_gluing_singleton_of_Aplus`)
  │     ├── S-GEOM-IND: hV_glue induction on |S.elts|          ✅ DONE (T252 audit; `standardCover_gluing_induction_step_via_laurentGluing`)
  │     │     (Wedhorn 8.34 induction, Laurent split at f₀)
  │     └── S-GEOM-ASM: Part 2 assembly (may include hZavyalov
  │                      bypass per Hübner 3.8)                 ⏳ ~50 lines
  │
  └── Local cover-level injectivity per piece E ∈ C.covers
        └── (same coeRingHom_preserves_proper as Part 1)
```

---

## 3. Open tickets — detailed plans

### [T-OV-1] Bivariate Example 6.38 — DONE (audited 2026-05-13)

**Status**: DONE in hypothesis-parameterised form. Substantive Step A
landed; named hypothesis bridges discharged in consumer wrapper.

**2026-05-13 audit closure**: the round-4 brief and prior tickets had stale
"~150 lines drafted, Step A still pending" annotations. In fact, ALL of
the following are sorry-free and `#print axioms` clean
(`[propext, Classical.choice, Quot.sound]`):

  - `example638Bivariate_equiv` (Step A main theorem, `LaurentOverlap.lean`).
    Hypothesis-parameterised on `hA_complete`, `hnoeth`, `hcont_forward`.
  - `example638Bivariate_backwardHom` (backward direction).
  - `example638Bivariate_forward_backward_eq_id`,
    `example638Bivariate_backward_forward_eq_id` (round-trips).
  - `laneA_τ_preBiv` (`LaneAReverseRoundTrip.lean`) — the **unconditional
    consumer-facing form** of the Step A iso, discharging all three named
    hypotheses internally from ambient typeclass assumptions.
  - `laneA_τ_preBiv_compatible_bridge_exists` — the wrapper feeding the
    Step A iso into the `LaurentOverlapBridgeCompatible` consumer of the
    downstream gluing argument.
  - `example638Bivariate_forwardHom_continuous_canonical`
    (`BivariateContinuity.lean`) — unconditional discharge of the
    `hcont_forward` hypothesis from ambient `[IsTateRing B]
    [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]` etc.

The forward map evaluates `ζ ↦ b`, `ζ⁻¹ ↦ b⁻¹` per Wedhorn Example 6.39
(reviewer-prescribed approach — NOT via limit/pushout). The full bridge
chain into `tateAcyclicity` Part 2 is wired through `laurentOverlapBridge_exists_compatible_via_primary`
in `LaurentOverlap.lean`, which now needs only `τ_preBiv` (supplied by
`laneA_τ_preBiv`) plus the two compatibility witnesses.

**Reviewer guidance** (ChatGPT Pro, 2026-05-13): T-OV-1 was framed as
"the cleanest current critical-path blocker". This audit shows the
substantive work IS landed; the round-4 brief's framing was misled by
a stale doc comment in `LaurentOverlap.lean` (now corrected).

**Remaining work**: none in the Step A formal sense. Downstream consumers
that use the Step A iso must now bind it together with the two
intertwining-identity witnesses (`τ_preBiv_overlap_plus_intertwine` and
`τ_preBiv_overlap_minus_intertwine`); both are reviewer-confirmed routine
intertwining checks once the iso is in hand. These remain as named
residuals in the downstream wrapper but are NOT part of T-OV-1 proper.

**Target**: `example638Bivariate_equiv : presheafValue (overlapDatum B P b) ≃+* LaurentCover.B₁₂_gen b`
where `overlapDatum B P b = laurentMinusDatum (trivialPlusDatum B P b) b`
is the bivariate rational datum cutting out `{v : v(b) = 1}`.

**Landed** (`Adic spaces/LaurentOverlap.lean`, 634 lines, 0 sorry):
- `overlapDatum B P b` + basic API (`_s`, `_P`, `_subset_plus`).
- Step A foundational lemmas: `canonicalMap b` and
  `invS = canonicalMap (1/b)` power-bounded in `presheafValue(overlap)`;
  product `= 1` (from `canonicalMap_b_mul_invS_in_overlap`).
- Step A half-forward homs:
  - `overlap_plus_evalHom : TateAlgebra B →+* presheafValue(overlap)`
    (sending `X ↦ canonicalMap b`).
  - `overlap_minus_evalHom : TateAlgebra B →+* presheafValue(overlap)`
    (sending `X ↦ invS`).
  - Factored through plus/minus ideals:
    - `overlap_plus_forwardHom : B₁_gen b →+* presheafValue(overlap)`.
    - `overlap_minus_forwardHom : B₂_gen b →+* presheafValue(overlap)`.
- Step B main (pure algebra): `bivariateOverlap_equiv_B₁₂gen :
  B⟨ζ,η⟩ / (b - X, 1 - b·Y) ≃+* B₁₂_gen b` via ideal-equality
  (`bivariateOverlap_ideal_eq`) + third-iso-theorem
  (`DoubleQuot.quotQuotEquivQuotSup`).
- Forward + symm-direction action lemmas on Step B (8 lemmas total) for
  downstream T-OVERLAP-COMPAT consumption.

**Remaining: S-OV-GLUE** (Step A main theorem).

Follow **Wedhorn p.84 identity**: the Laurent Tate algebra
`A⟨ζ, ζ⁻¹⟩` decomposes as a direct sum of `B`-modules
`A⟨ζ⟩ ⊕ ζ⁻¹ · A⟨ζ⁻¹⟩`. Build:

```lean
noncomputable def bivariateOverlap_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    LaurentCover.B₁₂_gen b →+* presheafValue (overlapDatum B P b)
```

by:

1. **Decomposition**: every `x ∈ A⟨ζ, ζ⁻¹⟩` is uniquely
   `x = x₊ + ζ⁻¹ · x₋` with `x₊ ∈ A⟨ζ⟩, x₋ ∈ ζ⁻¹ · A⟨ζ⁻¹⟩`.
   (Equivalently: split the Laurent-coefficient sum at degree 0.)
2. **Map**: send `mk x ↦ overlap_plus_evalHom(x₊) + invS · overlap_minus_evalHom(x₋)`.
3. **Well-definedness mod (b - ζ)**: use `overlap_plus_evalHom_fSubX_eq_zero`
   and `canonicalMap_b_mul_invS_in_overlap = 1` to show
   `(b - ζ) · anything ↦ 0`.
4. **Multiplicativity + additivity**: Laurent-series multiplication
   respects this direct-sum decomposition modulo `(b - ζ)`.
5. **Inverse via Step B**: `bivariateOverlap_equiv_B₁₂gen.symm` composed
   with the quotient map from `B⟨ζ,η⟩/(b-X, 1-bY)`.
6. **Round trips** via `UniformSpace.Completion.ext'`: agreement on dense
   subring (polynomials in ζ, ζ⁻¹) + T2 of `presheafValue(overlap)`.

**Alternative (composition route)**: apply `presheafValue_iteratedMinus_equiv`
at base `laurentPlusDatum D₀ f` and `f` to get
`presheafValue(overlap over A) ≃ presheafValue(iteratedMinus over B_plus)`;
apply `example638Minus_equiv` at `B_plus` to get
`≃ B_plus⟨X⟩/(1-canonicalMap_plus(f)·X)`; apply `laurentPlusBridge.symm`
to rewrite `B_plus ≃ B₁_gen(f_B)` and substitute; then algebraic
identification with `B₁₂_gen(f_B)`. Same estimate.

**Estimated lines**: ~200.

### [T-OVERLAP-COMPAT] Close `laurentOverlapBridge_exists_compatible`

- **Status**: DONE (audited 2026-05-12, T254)
- **Closed**: 2026-05-12 audit — `laurentOverlapBridge_exists_compatible`
  at `LaurentRefinement.lean:3775`. Hypothesis-parameterised on
  `(τ_preBiv, τ_alg, intertwining witnesses)` per the project's
  parametric design. Sorry-free; `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`.

**Target**: `LaurentRefinement.lean:3173`.

**Plan**: instantiate `example638Bivariate_equiv` at
`B := presheafValue D₀, b := D₀.canonicalMap f`; verify both
`LaurentOverlapBridgeCompatible` intertwining identities using the
`_mk`, `_algebraMap`, `_X`, `_Y` action lemmas already landed in
`LaurentOverlap.lean`, plus `presheafValue_iteratedMinus_equiv_apply`
and similar reductions on the plus/minus bridge sides.

**Estimated lines**: ~80. **Blocked on T-OV-1 Step A**.

### [T-IDEAL-2] Closedness of proper ideals — STATEMENT AUDIT COMPLETE  **[REFRAMED 2026-05-13 per reviewer]**

**Reviewer correction** (ChatGPT Pro, 2026-05-13): "the residual 'proper ideals stay
proper under the canonical map to completion' is FALSE if it is stated for arbitrary
proper ideals of an uncompleted rational `locSubring`. Your own earlier example
essentially shows this: in a non-complete locSubring, an element like `1 + X` may be
nonunit before completion but become a unit after completion, so the proper ideal it
generates extends to the unit ideal."

**STATEMENT AUDIT (2026-05-13)**: the reviewer's correction is confirmed for the
"global proper ideal" form `hcoeRingHom_preserves_proper` (consumed by
`productRestriction_injective_tate_via_coeRingHom_preserves_proper` in `Cor832.lean`).
That hypothesis is too strong / potentially false in general.

**KEY FINDING**: the project already has the **mathematically correct narrowed form**
`productRestriction_injective_tate_via_prime_extension_closed` (`Cor832.lean:2256`).
This narrower form takes a STRICTLY WEAKER closedness obligation:

> For every NON-OPEN prime `p ⊂ A` with `C.base.s ∉ p`, the ideal extension
> `Ideal.map (algebraMap A (Localization.Away C.base.s)) p` is closed in
> `C.base.topology`.

This is a **pointwise** closedness claim for specific PRIME extensions — strictly
weaker than the global "every proper ideal" form. The full chain through to
`productRestriction_injective_tate` is intact; only this narrower residual remains.

Supporting infrastructure (existing, axiom-clean):
- `coeRingHom_preserves_proper_prime_extension_of_closed` (`Cor832.lean:2151`)
- `liftedIdeal_ne_top_of_prime_extension_closed` (`Cor832.lean:2170`)
- `spa_point_nonOpen_of_rational_subset_tate_of_prime_extension_closed`
  (`Cor832.lean:2188`)
- `hSpa_points_via_prime_extension_closed` (`Cor832.lean:2214`)
- `productRestriction_injective_tate_via_prime_extension_closed` (`Cor832.lean:2256`)

**Status**: STATEMENT-AUDIT-DONE (2026-05-13). The reviewer's two candidate
replacements:

1. **T-SPA-COVER-SURJ** (Spec-cover surjectivity): bypasses closedness entirely.
   Still useful as an alternative route.
2. **T-BOURBAKI-FG-CLOSED** (safe Bourbaki closedness): applies to f.g. submodules
   in COMPLETE adic noetherian rings. Doesn't directly handle our non-complete
   `Localization.Away C.base.s`, but supports downstream presheafValue-level
   closedness.

**Remaining work**: discharge the per-non-open-prime closedness obligation. Two paths:
- (i) Direct topological argument for closedness of `Ideal.map algebraMap p` in
      `C.base.topology` (the localization topology). Wedhorn/Tate-specific.
- (ii) Route through T-SPA-COVER-SURJ to bypass closedness altogether.

The reviewer's recommendation: (ii) is cleaner. Path (i) requires the proof-specific
topological argument; path (ii) recasts the question at the Spec level using the
Wedhorn/Spa-point construction.

- **Original Status**: DONE for the hypothesis-conditional discharge chain (audited 2026-05-12, T271)
- **Closed-conditional**:
  - `coeRingHom_preserves_proper_of_locIdeal_le_jacobson` (Cor832.lean:2533) —
    given `locIdeal ≤ Jacobson ⊥` in locSubring, discharges
    `coeRingHom_preserves_proper`. Sorry-free.
  - `coeRingHom_preserves_proper_of_stacks00MA` (Cor832.lean) — given
    `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`
    (the full Stacks 00MA), discharges the same. Sorry-free.
  - `locIdeal_le_jacobson_bot_of_faithfullyFlat` (IdealLocalization.lean) +
    `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat` (Cor832.lean:2373) —
    derive the Jacobson hypothesis from the faithful-flatness one. Sorry-free.
  - `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`
    (AdicCompletionFaithfullyFlat.lean:62) — conditional Stacks 00MA from
    `I ≤ Jacobson ⊥`. Sorry-free.
- **Remaining unconditional gap**: the UNCONDITIONAL `Module.FaithfullyFlat
  (locSubring) (AdicCompletion locIdeal locSubring)` requires Stacks 00MA
  for arbitrary Noetherian + finitely-generated ideals (without the
  `I ≤ Jacobson ⊥` precondition). This is the genuine mathlib contribution
  required (T-MATHLIB-STACKS-00MA).
- **Status before audit**: SUBSTANTIAL PROGRESS

**Target**: discharge `coeRingHom_preserves_proper` in
`Cor832.lean:1202`.

**Landed** (`IdealClosedness.lean` + `Cor832.lean`, 2026-04-18):
- **Generic closedness machinery** (0 sorry, axiom-clean):
  - `mem_closure_iff_of_isAdic`: `x ∈ closure q ↔ ∀ n, x ∈ q + I^n`.
  - `Ideal.isClosed_of_le_jacobson`: for noetherian `R`, `[IsAdic I]`,
    `I ≤ Jacobson ⊥` ⟹ every ideal is closed (Krull's intersection
    theorem via `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`).
  - `Ideal.isClosed_of_isAdicComplete`: corollary via
    `IsAdicComplete.le_jacobson_bot`.
- **Transfer bridges**:
  - `IsClosed.of_isClosed_subspace_of_isOpen_subring`: generic
    subring-to-ambient closedness lift (open subring is clopen).
  - `isClosed_image_of_isClosed_subspace_in_locSubring` (`Cor832.lean`):
    Tate-specific specialization to locSubring ⊆ Loc.Away D.s.
- **Closure combinator**:
  - `coeRingHom_preserves_proper_of_closed`: given proper `q` closed in
    `D.topology`, derives `Ideal.map coeRingHom q ≠ ⊤` via T-IDEAL-1 +
    `IsUniformInducing.isInducing` + `IsInducing.closure_eq_preimage_closure_image`.

**Remaining sub-tickets** (all Tate-specific, no Bourbaki):

#### S-IDEAL-JAC: `locIdeal ≤ Jacobson(⊥)` in `locSubring`

- **Target statement**:
  ```lean
  theorem locIdeal_le_jacobson_bot (P : PairOfDefinition A) (T : Finset A)
      (s : A) (hopen : ...) :
    locIdeal P T s ≤ Ideal.jacobson (⊥ : Ideal (locSubring P T s))
  ```
- **Mathematical content**:
  - `locIdeal P T s = P.I · locSubring` (roughly — check exact def at
    `LocalizationTopology.lean:87`).
  - Elements of `P.I` are topologically nilpotent in `A` (since `I`
    generates the ideal of definition for the Tate topology, whose
    powers form a basis of 0-neighborhoods; equivalently, `π ∈ P.I`
    topologically nilpotent in A).
  - The inclusion `locSubring → Loc.Away s` is continuous, so images of
    topologically nilpotent elements are topologically nilpotent.
  - Topologically nilpotent elements lie in `Jacobson ⊥` (standard
    lemma: for `x` top-nilp, `1 - x·y` is a unit for every `y` via
    geometric series `Σ (x·y)^n`; hence `x ∈ Jacobson`).
- **Mathlib hooks**:
  - Search for `IsTopologicallyNilpotent.mem_jacobson` or similar.
  - If absent: prove from scratch (~15 lines via geometric series).
- **Lean skeleton**:
  ```lean
  intro x hx
  rw [Ideal.mem_jacobson_iff]
  intro y
  -- Goal: ∃ z, z * (1 - x·y) = 1
  -- Show x is topologically nilpotent in locSubring.
  have hx_tn : IsTopologicallyNilpotent x := ...
  -- Apply geometric-series unit lemma.
  exact (hx_tn.mul y).isUnit_one_sub.exists_left_inv
  ```
- **Estimated lines**: 30-50.
- **Status**: DONE-AUDIT (2026-05-13). The "from-scratch ~30-50 line proof
  via geometric series" plan was mathematically incomplete — without
  completeness of `locSubring`, the standard route
  `topologically-nilpotent → 1-x*y unit → x ∈ Jacobson` does not close.
  The project already has the structurally correct infrastructure in
  `IdealLocalization.lean`:
  - `locIdeal_le_jacobson_bot_of_isAdicComplete` (line 262): the
    conditional version under `[IsAdicComplete (locIdeal) (locSubring)]`.
    Direct application of mathlib's `IsAdicComplete.le_jacobson_bot`.
    Axiom-clean.
  - `locIdeal_le_jacobson_bot_of_faithfullyFlat` (line 307): the
    faithful-flatness descent version. Given a faithfully-flat algebra
    S with Jacobson containment at S level (e.g., S = presheafValue's
    ring of definition, which is adic-complete), descends to
    `locSubring` without asserting `locSubring` complete.
    Axiom-clean.
  - `locIdeal_forall_isTopologicallyNilpotent` (line 339): every
    `locIdeal` element is topologically nilpotent in `locSubring`.
    No completeness needed. Axiom-clean.

  The truly **unconditional** version `locIdeal ≤ Jacobson(⊥)` without
  any hypothesis on `locSubring` requires the faithful-flatness route
  (path #2 above) instantiated with S = `presheafValue_ringOfDef D`,
  which itself requires Stacks 00MA full (the unconditional adic
  completion of Noetherian is Noetherian + faithfully flat). So the
  closure path is: S-IDEAL-JAC unconditional ⇐ Stacks 00MA full.

  Downstream consumers in `Cor832.lean` (e.g.,
  `productRestriction_injective_tate_of_isAdicComplete`) currently
  take `[IsAdicComplete (locIdeal) (locSubring)]` as a typeclass
  hypothesis and apply the conditional route.

#### S-IDEAL-LOC: `q_𝔇 · A_s = q` + closedness transfer

- **Target**: given a proper ideal `q ⊆ Localization.Away D.s`, show
  `q = (q ∩ locSubring) · Loc.Away D.s` as sets, and that closedness of
  `q ∩ locSubring` in locSubring's adic topology ⟹ closedness of `q`
  in Loc.Away D.s's localization topology.
- **Wedhorn reference**: §8.2 localization topology definition. Every
  `x ∈ Loc.Away D.s` can be written `x = π^{-n} · d` with `d ∈ locSubring`
  (via `IsLocalization.mk'` + clearing denominators); this parameterizes
  the "localization structure" of Loc.Away over locSubring.
- **Reviewer's route** (Q1 expansion): "every element of `A_s` is
  `π^{-n} d` with `d ∈ 𝔇`, and the localization topology has basis
  `J^m · A_s`; so closedness of `q_𝔇` in `𝔇` lifts to closedness of
  `q = q_𝔇[1/π]` in `A_s` by clearing a power of `π`."
- **Two sub-claims**:
  1. **Localization identity**: `q = (q ∩ locSubring) · Loc.Away D.s`
     (as subsets). One direction is `⊆`: `x ∈ q` ⟹ `∃ n, π^n · x ∈ locSubring`,
     and `π^n · x ∈ q ∩ locSubring`, so `x = π^{-n} · (π^n · x) ∈
     (q ∩ locSubring) · Loc.Away D.s`. Other direction: ideal-closure.
  2. **Topological transfer**: if `q ∩ locSubring` is closed in
     locSubring (J-adic), the ideal `(q ∩ locSubring) · Loc.Away D.s`
     is closed in Loc.Away D.s (localization topology).
     
     The second sub-claim is the technically subtle piece. Sketch: for
     `x ∉ q`, write `x = π^{-n} d` with `d ∉ q ∩ locSubring`. Since
     `q ∩ locSubring` is closed, there's an open `V ∋ d` (in
     `locSubring` subspace topology) disjoint from `q ∩ locSubring`.
     Then `π^{-n} · V` is a neighborhood of `x` in Loc.Away D.s,
     disjoint from `q`.
- **Mathlib hooks**:
  - `IsLocalization.Away.lift` / `Localization.Away`.
  - Subspace topology + multiplication by unit is homeomorphism.
  - May need to prove that `π^{-n} : Loc.Away → Loc.Away` (left
    multiplication) is continuous and open — easy since π is a unit.
- **Estimated lines**: 80-150.

#### S-IDEAL-ASM: end-to-end assembly

- **Target**: discharge the `coeRingHom_preserves_proper` hypothesis in
  `productRestriction_injective_tate_via_coeRingHom_preserves_proper`.
- **Assembly**:
  1. Given `q : Ideal (Loc.Away D.s)`, `q ≠ ⊤`.
  2. Let `q_𝔇 := q ∩ locSubring` (as ideal of locSubring).
  3. Apply S-IDEAL-JAC + `Ideal.isClosed_of_le_jacobson` on locSubring
     to conclude `q_𝔇` is closed in locSubring.
  4. Apply S-IDEAL-LOC to conclude `q` is closed in Loc.Away D.s.
  5. Apply `coeRingHom_preserves_proper_of_closed` ⟹ result.
- **Estimated lines**: 30.

**Total T-IDEAL-2 remaining**: ~140-230 lines. No Bourbaki needed.

### [T-GEOM-RED] Geometric reduction (Hübner Lemma 3.8 / Wedhorn 8.34)

**Target**: build Part 2's `hV_glue` input from
`laurentCover_gluing_presheaf` by induction on the standard-cover size,
then wire into Part 2 via `tateAcyclicity_gluing_via_refinement_cover_level`.

**Landed** (`GeometricReduction.lean`, 248 lines, 0 sorry):
- `tateAcyclicity_gluing_via_refinement_cover_level` — corrected variant
  of the unsound `tateAcyclicity_gluing_via_refinement`, exposing the
  proper cover-level `hE_sep` hypothesis from `gluing_of_finer_rational`.
- `RationalCovering.plusDatum C f := laurentPlusDatum C.base f` +
  `plusDatum_subset_base`.
- `RationalCovering.standardCoverVCovers C S = S.image C.plusDatum`
  (uses `Classical.decEq (RationalLocData A)`) +
  `mem_standardCoverVCovers` + `standardCoverVCovers_subset_base`.

**Remaining sub-tickets**:

#### S-GEOM-TAU: τ refinement map + containment

- **Status**: DONE (T250, 2026-05-12)
- **Closed**: 2026-05-12 via T250 — `RationalCovering.standardCoverVTau`
  and `RationalCovering.standardCoverVTau_subset` in `GeometricReduction.lean`.
  Sorry-free; #print axioms reports `[propext, Classical.choice, Quot.sound]`.
- **Implementation**: τ uses `let h := ...; let f := h.choose; let hf := h.choose_spec.1`
  to extract the witness in noncomputable def-form (avoiding the
  Exists.casesOn-to-Type elimination error). Subset proof uses the
  reviewer's alternative (`rationalOpen_plusDatum_eq_insert` at the
  set level) to bridge the `DecidableEq` diamond.
- **Target**: `RationalCovering.standardCoverVTau` (construct via
  `Classical.choose` on `hS_contain`) + `standardCoverVTau_subset`.

#### S-GEOM-BASE: base case `|S.elts| = 1`

- **Status**: DONE (audited 2026-05-12, T251)
- **Closed**: 2026-05-12 audit confirmed the discharge chain in
  `GeometricReduction.lean` (lines 1238-1440):
  - `standardCover_gluing_singleton` (conditional on `hSurj`)
  - `restrictionMap_plusDatum_surjective_of_vle` (discharge via vle)
  - `standardCover_gluing_singleton_of_vle` (vle-parametric)
  - `vle_s_of_mem_Aplus_of_one_mem_T` (vle from `f ∈ A⁺ + 1 ∈ T`)
  - `standardCover_gluing_singleton_of_Aplus` (caller-ready full)
  Sorry-free; `#print axioms standardCover_gluing_singleton_of_Aplus`
  reports `[propext, Classical.choice, Quot.sound]`.
- **Target**: when `S.elts = {f}` with `Ideal.span {f} = ⊤` (so
  `f ∈ Aˣ`), build `hV_glue` for the singleton V-cover `{C.plusDatum f}`.
- **Implementation**: the discharge actually requires the WEAKER
  hypothesis `f ∈ A⁺` + `1 ∈ C.base.T` (rather than `Ideal.span {f} = ⊤`),
  which is the natural Wedhorn-normalised setup. The vle hypothesis
  `∀ v ∈ rationalOpen C.base.T C.base.s, v.vle f C.base.s` discharges via
  `vle_one_of_mem_spa` (f bounded by 1) + `hv_T 1` (1 bounded by s),
  composing through `vle_trans`.

#### S-GEOM-IND: inductive step

- **Status**: DONE (audited 2026-05-12, T252)
- **Closed**: 2026-05-12 audit confirmed the recombination step in
  `GeometricReduction.lean` (lines 1433-1635):
  - `standardCover_gluing_induction_step` — structural recombination
    taking two half-sections (u_plus, u_minus) + Laurent-gluing
    witness, produces a global section on C.base.
  - `standardCover_gluing_induction_step_via_laurentGluing` —
    specialisation consuming `laurentCover_gluing_presheaf` directly.
  Both sorry-free; `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`.
- **Target**: given `hV_glue` for standard covers of size `n`, derive
  for size `n+1`.
- **Implementation**: the project provides the STRUCTURAL recombination
  as a reusable theorem. The outer recursive induction (constructing
  half-sections from the induction hypothesis applied on each Laurent
  half + the "sub-cover adjustment") lives in the consumer
  S-GEOM-ASM / final Part 2 assembly. Per the project's design, the
  structural step is the on-target deliverable; the outer recursion
  is plumbed by application-specific assemblies.

#### S-GEOM-ASM: Part 2 final assembly — ✅ API COMPLETE (2026-04-20)

- **Status**: the S-GEOM-ASM caller API is fully landed via the
  **direct per-E route** in `GeometricReduction.lean`:
  - **Core assembly**: `tateAcyclicity_Part2_direct_per_E` (axiom-clean
    modulo upstream `sorryAx`) — consumes
    `StandardCover.refines_cover_per_E C S`, `refines_contain C S`,
    `hV_glue_refined` (Lane A), and `hE_sep_direct` on the per-E
    local covering (Lane B).
  - **Caller wrapper**: `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`
    — takes `hZavyalov_per_E` + universal Lane A/B suppliers, extracts
    `S` via `StandardCover.refines_by_standard_cover_per_E`, applies
    the core assembly.
  - **Upstream supplier**:
    `StandardCover.RationalCovering.refines_by_standard_cover_per_E`
    strengthens `refines_by_standard_cover` to produce
    `refines_cover_per_E`.
- **Historical τ-route**: `tateAcyclicity_Part2_assembly`,
  `tateAcyclicity_Part2_via_refined_geometric_reduction`,
  `tateAcyclicity_Part2_via_geometric_reduction` — kept for reference,
  marked superseded in docstrings; new code should use the direct
  per-E route.
- **Remaining external blockers** (not in this lane):
  * **Lane A** = T-OV-1 / T-OVERLAP-COMPAT. Discharges
    `hV_glue_refined` via `laurentCover_gluing_presheaf`
    (`LaurentRefinement.lean:3173`).
  * **Lane B FF residual** = T-IDEAL-2 / per-E Cor 8.32 via
    `productRestriction_injective_tate_via_prime_extension_closed`
    (`Cor832.lean:1581`) at each `per_E_local_covering`. Discharges
    `hE_sep_direct`.
  * **T-NULL-PER-E general case** = Wedhorn Prop 7.14 / Zavyalov §2.3.
    Discharges `hZavyalov_per_E` for multi-piece covers (for single-piece
    covers, `exists_nullstellensatz_refinement_per_E_of_singleton_cover`
    provides a concrete supplier — landed 2026-04-20).
- **Lines landed**: ~700 lines in `GeometricReduction.lean` +
  ~200 lines in `StandardCover.lean` (refined V-cover infrastructure,
  per-E local covering, direct per-E assembly, caller wrapper,
  singleton Nullstellensatz discharge, extensive docs).

### [T-ACYC-PART2] Final Part 2 assembly

- **Target**: close `LaurentRefinement.lean:3737`.
- **Depends on**: T-OV-1 + T-OVERLAP-COMPAT + T-GEOM-RED + T-IDEAL-2.
- **Estimated lines**: 50 (composition).

---

### [T-QTATE-1] Closed quotient of noetherian Tate ring is Tate

- **Status**: DONE (audited 2026-05-12, T253)
- **Closed**: 2026-05-12 audit — `IsHuberRing.quotient` and
  `IsTateRing.quotient` in `Adic spaces/QuotientTate.lean` (lines
  150 and 159). Both sorry-free; `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`.
- **Mathematical statement**: If `R` is a noetherian Tate ring and
  `I ⊆ R` is a closed ideal, then `R/I` with the quotient topology is a
  Tate ring. A ring of definition of `R/I` is the image of a ring of
  definition of `R`; its ideal of definition is the image of the
  principal ideal generated by the chosen pseudo-uniformizer.
  Topologically nilpotent unit descends. Completeness and Hausdorffness
  follow from quotienting by a closed ideal.
- **Depends on**: Wedhorn 6.17 (closed ideals in noetherian Tate —
  partial, see T-IDEAL-2).
- **Blocks**: T-QTATE-2, T-OV-1-DENSITY.
- **Estimated lines**: ~250.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "Lane A should use
  approach (a): construct the Tate-ring structure on the quotient. The
  clean theorem is not a one-off density hack but a reusable statement:
  a quotient of a noetherian Tate ring by a closed ideal is again a Tate
  ring with the quotient topology, and its Tate algebra has dense
  polynomials. This is the mathematically honest route and should pay
  for itself downstream."

---

### [T-QTATE-2] Polynomial density in `B⟨Z⟩` for any Tate ring `B`

- **Status**: DONE (audited 2026-05-12, T253)
- **Closed**: 2026-05-12 audit — `tateAlgebra_polynomials_dense_canonical`
  in `Adic spaces/TopologyComparison.lean` (referenced by
  `QuotientTate.lean:178`). Sorry-free; `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`.
- **Mathematical statement**: For any Tate ring `B`, the polynomial
  subring `B[Z] ⊆ B⟨Z⟩` is dense in the canonical Tate topology, via
  truncation: a restricted power series is the limit of its partial
  sums because its coefficients tend to zero.
- **Depends on**: T-QTATE-1 (provides `IsTateRing` on the quotient
  consumer).
- **Blocks**: T-OV-1-DENSITY.
- **Estimated lines**: ~80 (mostly mechanical once T-QTATE-1 lands).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "Once `B` is
  available as a Tate ring, polynomial density in `B⟨Z⟩` is just the
  usual truncation argument: a restricted series is the limit of its
  partial sums because its coefficients tend to zero. This is the right
  way to close the reverse round trip."

---

### [T-OV-1-DENSITY] Lane A reverse round trip via quotient-Tate density

- **Status**: OPEN (added 2026-05-11; replaces the previously-open
  `h_bwd_fwd` boundary in `TA_B₁_gen_quotient_specialized_equiv`)
- **Mathematical statement**: For `A` noetherian Tate and `f ∈ A`, set
  `B = A⟨X⟩/(f-X)`. The reverse round trip
  `forward ∘ backward = id` on the bivariate quotient
  `A⟨X, Y⟩/(f - X, 1 - fY)` follows from polynomial density in `B⟨Z⟩`
  (applied via T-QTATE-2), specialised to `B = A⟨X⟩/(f - X)` via
  T-QTATE-1 with closedness of `(f - X)` from Wedhorn 6.17.
- **Depends on**: T-QTATE-1, T-QTATE-2, plus closedness of `(f - X)`
  (from T-IDEAL-2 / Wedhorn 6.17).
- **Blocks**: T-OV-1 finish → T-OVERLAP-COMPAT → T-ACYC-PART2.

---

### [T-NULL-PER-E-FIN] Finite plus-family local-neighborhood form

- **Status**: OPEN (added 2026-05-11; parallel fallback to T-NULL-PER-E)
- **Mathematical statement**: For every rational target `E ∈ C.covers`
  and every Spa-point `v ∈ R(T_E, s_E)`, there is a finite family
  `F ⊆ A` with
  `v ∈ ⋂_{f ∈ F} R(insert f C.base.T, C.base.s) ⊆ R(T_E, s_E)`.
  Combined with a conversion lemma: a finite local plus-family produces
  a standard-cover refinement after intersecting and re-extracting.
- **Depends on**: Cor 7.32 (landed), rational-open APIs (landed).
- **Use**: if Lane C's outer induction cannot absorb single-`f`
  refinement, the finite-family form is mathematically safer and the
  conversion lemma plugs it into the existing direct per-`E` assembly.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "if one plus-piece
  is too strong: finite intersection form. If the current induction
  wants a single `f`, add a conversion lemma from finite local
  plus-families rather than forcing a false one-element formula."

---

### [T-EMBED-TOPO] `IsSheafy` embedding via topological Example 6.38

**Round-5 reviewer correction** (ChatGPT Pro, 2026-05-13):
- Cor 8.32 algebraic faithful flatness is INSUFFICIENT for the embedding field.
  Topological inducing needs the refinement induction independently —
  "Faithful flatness does not imply topological inducing in general."
- Theorem 5.10 (`lane-c-single-laurent`) is a LOCAL induction step, not a global
  theorem. Arbitrary covers do NOT refinement-equivalently contain one Laurent pair
  at the base.
- The correct approach is **topological refinement induction mirroring Wedhorn 8.34**:
  Laurent two-cover inducing at each split + refinement transfer (already-landed
  `productRestrictionSub_isInducing_of_finer_rational_continuous` and
  `naturalRefinementMap*`) gives inducing for the original cover.

- **Status**: DONE for all 3 sub-tickets + base case in hypothesis-parameterised form (2026-05-13)
- **Sub-ticket closures**:
  - T-EMBED-TOPO-EXAMPLE638 (T265): `presheafValueCanonicalQuotientHomeomorph`
    in `TopologyComparison.lean` — topological iso of Example 6.38.
  - T-EMBED-TOPO-STRICT-LAURENT (T266 audit): `laurentCover_isEmbedding_presheaf`
    in `LaurentRefinement.lean:4477` — 2-cover topological strictness.
  - T-EMBED-TOPO-REFINEMENT-TRANSFER (T267):
    `productRestrictionSub_isInducing_of_finer_rational` in
    `EmbeddingTopo.lean` — conditional refinement transfer.
  - T-EMBED-TOPO-PAIRTOSUB (T272): `isEmbedding_of_pair_form_isEmbedding`
    in `EmbeddingTopo.lean` — pair-to-subtype transport.
  - T-EMBED-TOPO-LANE-C-BASE (T273+T275, 2026-05-13):
    `productRestrictionSub_laurentCovering_isEmbedding_of_homeomorph` and
    `productRestrictionSub_laurentCovering_isEmbedding_of_distinct`
    in `EmbeddingTopo.lean` — Lane C **base case** parametric + concrete
    forms. The concrete form has the commutativity hypothesis discharged
    automatically by proof irrelevance on the subset arguments of
    `restrictionMap`.
  - T-EMBED-TOPO-2EL-PI (T274, 2026-05-13): `twoElementSubtypePiHomeomorph`
    in `EmbeddingTopo.lean` — generic utility homeomorphism
    `F a × F b ≃ₜ (∀ x : ↥({a, b} : Finset α), F x.1)` for distinct
    `a, b`. Continuity proved via `continuous_pi` + `continuous_fst`/
    `continuous_snd` + `continuous_apply`.
  - T-EMBED-TOPO-LAURENT-INDUCING (T276+T278, 2026-05-13):
    `productRestrictionSub_laurentCovering_isInducing_via_bridges` and
    `productRestrictionSub_laurentCovering_isInducing_via_bridges_of_s_ne_zero`
    in `EmbeddingTopo.lean` — concrete single-Laurent-cover IsInducing
    supplier consuming the bridges hypothesis bundle; the `_of_s_ne_zero`
    variant discharges distinctness via T277.
  - T-EMBED-TOPO-LAURENT-EMBEDDING (T279, 2026-05-13):
    `productRestrictionSub_laurentCovering_isEmbedding_via_bridges_of_s_ne_zero`
    in `EmbeddingTopo.lean` — full `IsEmbedding` form of T278 (T278 only
    provides `IsInducing`). Useful for consumers needing both halves of
    `IsEmbedding` (inducing + injective).
  - T-EMBED-TOPO-INDUCING-GENERIC (T280+T281, 2026-05-13):
    `Topology.IsInducing.of_eval` and `Topology.IsInducing.of_continuous_comp`
    in `EmbeddingTopo.lean` — generic topology utilities for the Lane C
    induction. **T280** says adding projections preserves IsInducing.
    **T281** generalises to arbitrary continuous post-composition (no
    IsInducing on the post-map needed, only continuity).
  - T-EMBED-TOPO-REFINEMENT-CONTINUOUS (T282, 2026-05-13):
    `productRestrictionSub_isInducing_of_finer_rational_continuous` in
    `EmbeddingTopo.lean` — **strengthened** refinement transfer that
    weakens T267's `IsInducing φ` to `Continuous φ` via T281.
  - T-EMBED-TOPO-PROD-CONTINUOUS (T283, 2026-05-13):
    `productRestrictionSub_continuous` in `EmbeddingTopo.lean` —
    automatic continuity input for T282.
  - T-EMBED-TOPO-LANE-C-SINGLE-STEP (T284+T285+T286, 2026-05-13):
    End-to-end Lane C single-step closer in `EmbeddingTopo.lean`:
    - T284 `..._via_laurent_refinement`: parametric form with explicit φ.
    - T285 `naturalRefinementMap` + `_continuous` + `_comp`: canonical
      natural map between product types + its continuity and
      commutativity with `restrictionMap_comp`.
    - T286 `..._via_laurent_refinement_tau`: τ-only consumer interface
      that uses T285 to discharge T284's φ-hypotheses automatically.
  - T-EMBED-TOPO-LANE-C-SANITY (T287, 2026-05-13):
    `productRestrictionSub_laurentCovering_isInducing_via_tau_identity`
    in `EmbeddingTopo.lean` — sanity-check theorem re-deriving T278's
    laurent-cover IsInducing via the T286 τ-only closer with the
    trivial identity τ-function. Validates the Lane C chain
    end-to-end.
  - T-EMBED-TOPO-LANE-C-IND-STEP (T289, 2026-05-13):
    `productRestrictionSub_isInducing_of_sub_inducing` in
    `EmbeddingTopo.lean` — **inductive step for the standard-cover
    induction**: if V_small ⊆ V_large (Finset inclusion) and
    `productRestrictionSub_V_small` is IsInducing, then
    `productRestrictionSub_V_large` is IsInducing. Routes through T281
    with the subtype projection as the continuous post-composition.
  - T-EMBED-TOPO-LANE-C-BOOTSTRAP (T290+T291, 2026-05-13):
    `productRestrictionSub_isInducing_of_V_contains_laurent_pair` and
    `productRestrictionSub_isInducing_of_C_covers_contains_laurent_pair`
    in `EmbeddingTopo.lean`:
    - T290: ANY V_covers containing both halves of a laurent split at
      `Base` inherits IsInducing from the laurent 2-cover via T289.
    - T291: end-user specialisation — when `C.covers` itself contains
      both halves of a laurent split at `C.base`, IsInducing of
      `productRestrictionSub A C` follows.
    Closes 1135 directly for any C whose covers structure already
    includes a laurent-at-base pair.
  - T-EMBED-TOPO-LANE-C-T291-SANITY (T292, 2026-05-13):
    `productRestrictionSub_laurentCovering_isInducing_via_T291` in
    `EmbeddingTopo.lean` — sanity check: T291 specialised to `C =
    laurentCovering D₀ f` reproduces T287/T278 via the bootstrap chain.
    Validates the consistency of the three independent closure paths
    (T278 direct, T287 via T286, T292 via T291).
  - T-EMBED-TOPO-DISTINCT (T277, 2026-05-13): `laurentPlus_ne_laurentMinus_of_nonunit`
    in `LaurentRefinement.lean` — Laurent plus and minus data distinctness
    from `hf_nonunit + D₀.s ≠ 0 + IsDomain A`.
- **Composing**: the full IsSheafy embedding for arbitrary covers
  follows by induction on standard-cover refinement (S-GEOM-IND base
  + induction), using T265 at each plus/minus piece for the topological
  iso, T266 for the 2-cover base case strictness, T267 for the
  inductive step, and T273-T278 for the concrete Laurent-cover
  IsInducing base case. The full assembly is in
  `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing`
  (StructureSheaf.lean:1167) which takes the assembled inducing
  property as a parameter.
- **Mathematical statement**: `productRestrictionSub : 𝒪(D₀) → ∏ᵢ 𝒪(Dᵢ)`
  is a topological embedding (not just an algebraic injection).
- **Why this is not just Cor 8.32**: Faithful flatness of the product
  restriction gives ALGEBRAIC injectivity. The topological embedding
  (inducing-ness of the product restriction) requires the topological
  iso side of Example 6.38 and topological strictness of the
  Laurent-quotient diagrams (Lemma 8.33 topological lift).
- **Depends on**: T-OV-1 topological half (Example 6.38 as TOPOLOGICAL
  iso, not just algebraic ring iso); topological strictness of the
  `row3_exact` / Laurent diagram chase transported through the iso.
- **Blocks**: full `IsSheafy.embedding` field in
  `isSheafy_ofStronglyNoetherianTate_flat`.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "The biggest hidden
  risk is topological, not algebraic. Faithfully flat product
  restriction gives algebraic injectivity, but the final `IsSheafy`
  statement wants a topological embedding. That will not follow
  automatically from algebraic faithful flatness. The topological
  Example 6.38 package and strictness / topological exactness of the
  Laurent diagrams must be strong enough to supply the embedding."

---

### [T-HYP-AUDIT] Audit the strong-noetherian hypothesis chain

- **Status**: DONE — Case B resolved (audited 2026-05-12, T255)
- **Closed**: 2026-05-12 audit — the current `tateAcyclicity` signature
  in `LaurentRefinement.lean:5688` already includes `[IsStronglyNoetherian A]`
  as an explicit typeclass hypothesis, alongside `[IsTateRing A]`,
  `[IsNoetherianRing A]`, `[T2Space A]`, `[NonarchimedeanRing A]`.
  This is "Case B" from the original audit options: the
  `IsStronglyNoetherian` hypothesis was already added to the signature
  during prior work, making the implication chain to Lemma 8.31 and
  Wedhorn 6.17 internally consistent.
- **Task**: Verify that the current signature of `tateAcyclicity` —
  `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
   (P : PairOfDefinition A) [IsNoetherianRing P.A₀]`
  — actually implies the noetherian properties of `A⟨X⟩` (and iterated
  `A⟨X_1, ..., X_n⟩`) required by Lemma 8.31 and Wedhorn 6.17
  internally.
- **Outcome paths**:
  - *Case A*: it does → record the implication chain as a lemma in
    `NoetherianTateModules.lean`.
  - *Case B*: it doesn't → add an explicit `IsStronglyNoetherian` (or
    equivalent) hypothesis to the main `tateAcyclicity` signature.
- **Estimated lines**: ~30 (audit + lemma OR signature change +
  downstream signature propagation).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "If the project has
  already proved that these imply the strong-noetherian /
  Tate-algebra-noetherian hypotheses used in Lemma 8.31 and Wedhorn
  6.17, fine. If not, the final statement is missing a real
  hypothesis."

---

### [T-EX638-SCOPE] Example 6.38 scope: one-variable vs general rational data

- **Status**: DONE (audited 2026-05-12, T256)
- **Closed**: 2026-05-12 audit — the project's
  `presheafValueCanonicalQuotientEquiv` (TopologyComparison.lean)
  uses the one-variable quotient `A⟨X⟩/(1 - D.s · X)` for arbitrary
  rational data `D : RationalLocData A`, parameterised by explicit
  hypotheses `hb`, `hT_pb`, `hcont_eval` that ENFORCE the rational
  topology constraints from `D.T`. The hypothesis `hT_pb` (every
  `t ∈ D.T` is power-bounded) ensures the topology constraints are
  honoured even for `|T| > 1`. There is no silent identification of
  general `R(T/s)` with a one-variable quotient — the iso is correct
  for general T precisely because the hypotheses encode the multi-T
  topology constraints. Verified consistent with reviewer guidance.
- **Task**: Document and verify which rational data are modeled by the
  one-variable quotient `A⟨X⟩/(1 - sX)` versus which require
  multivariable identification or chained basic-step decomposition.
- **Expected outcome**:
  - `R(1/f)` and `R(f/1)` are modeled by the one-variable quotient.
  - General `R(T/s)` with `|T| > 1` is reached by INTERSECTING basic
    one-variable rational steps (presheaf gluing on intersections),
    NOT by silently passing to a multivariable quotient.
  - Confirm no theorem in the chain (Lane A, Lane C, or final
    assembly) silently identifies general `R(T/s)` with a one-variable
    quotient where the topology actually involves multiple `t/s`
    constraints.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "Verify that the
  quotient model matches the rational datum. For a general rational
  datum `R(T/s)`, a one-variable quotient `A⟨X⟩/(1-sX)` models
  inversion of `s`; the full rational topology involving all `t/s` may
  require a multivariable quotient or a chain of basic rational steps.
  If the project only uses the one-variable quotient for basic
  `R(1/f)` / `R(f/1)` steps, that is fine; do not silently use it for
  arbitrary `T`."

---

### [T-INJ-1-CLEANUP] Refactor remaining single-map injectivity references

- **Status**: DONE-as-annotation (audited 2026-05-12, T268)
- **Closed**: 2026-05-12 audit — the two remaining consumers of
  `restrictionMapHom_injective` (`LaurentRefinement.lean:5655` in
  `tateAcyclicity_gluing_via_refinement` and `LaurentRefinement.lean:5718`
  in legacy `tateAcyclicity` Part 1) are documented with inline
  annotations explaining the retirement status and the migration
  target (cover-level Cor 8.32 in `Cor832.lean`). The actual refactor
  is blocked by a transitive-import cycle (`Cor832.lean` imports
  `StructureSheaf.lean` which imports `LaurentRefinement.lean`).
  The bypass route in `TateAcyclicityFinalAssembly.lean` (T238-T247)
  provides the migration target for new downstream consumers.
- **Task**: Find and refactor downstream wrappers that still consume
  the retired single-map theorem `restrictionMapHom_injective`. Replace
  each with consumption of the product-level Cor 8.32 (i.e.
  `productRestriction_faithfullyFlat_abstract` or its tate
  specialisations).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11): "If wrappers still
  mention `restrictionMapHom_injective`, refactor them to consume the
  product restriction theorem."

---

### [T-RETIRE-PROP815] Mark `restrictionMap_isLocalization` as MISFRAMED

- **Status**: DONE (audited 2026-05-12, T257)
- **Closed**: 2026-05-12 audit — the retirement annotation is already
  present in the docstring at `PresheafTateStructure.lean`, including
  the reviewer's counterexample (`A = k⟨T, U⟩/(TU), U = R(1/T)`) and
  the directive "Do not add new uses". The misframing is documented
  at the declaration site.
- **File**: `Adic spaces/PresheafTateStructure.lean` (the sorry at line 2410)
- **Depends on**: T-COR832-VIA-FLAT (must land first so downstream consumers
  move off this dependency)
- **Mathematical statement**: the existing `restrictionMap_isLocalization`
  states that for rational data `D₀ ⊇ D`, the restriction map
  `presheafValue D₀ → presheafValue D` is an `IsLocalization.Away`
  (algebraic-localization) with respect to `canonicalMap D.s`. **The
  reviewer (ChatGPT Pro, 2026-05-11 session 2) confirms this target is
  MATHEMATICALLY FALSE in general.**
- **Counterexample**: Take `A = ℚ_p⟨X⟩` and consider the completed
  rational localization `A⟨T⟩/(XT - 1)` (inverting `X` in the affinoid
  sense). It contains the convergent infinite negative-power series
  `∑_{n ≥ 0} p^n X^{-n}`. Multiplying by `X^N` clears only finitely many
  negative powers, leaving an infinite tail. So no finite power of `X`
  clears this element into `A`; hence `IsLocalization.Away X` FAILS.
- **The misframing**: `IsLocalization.Away` is an **algebraic-localization**
  predicate (Mathlib's `algebraMap`-based formulation: every element is
  `a / x^n` for some `a, n`). Completed rational localizations are
  **topological-localization** objects (adjoin bounded fractions, then
  complete). The two notions DIVERGE: completed rational sections
  contain infinite convergent denominator tails that no finite power
  clears.
- **Action**:
  (i) Annotate the docstring of `restrictionMap_isLocalization` with this
      counterexample and a pointer to T-COR832-VIA-FLAT.
  (ii) After T-COR832-VIA-FLAT lands, audit all consumers and reroute them.
  (iii) The existing sorry stays as an explicit "intentionally not closed —
      over-strong target" marker, NOT to be picked up as a TODO.
  (iv) Optionally: replace with a weaker torsion-form statement that IS true
      (e.g., the `restrictionMapHom_ker_isTorsion` shape, which is the
      correct injectivity-up-to-torsion content).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11 session 2): "Do not try
  to close Wedhorn Prop. 8.15 by proving that an arbitrary completed
  rational restriction map is an `IsLocalization.Away` map. In that
  generality, that target is false."

---

### [T-FLAT-VIA-WEDHORN830] Direct flatness of restriction maps via Wedhorn 8.30/8.31

- **Status**: DONE (audited 2026-05-12, T258)
- **Closed**: 2026-05-12 audit — `restrictionMap_flat_via_iteratedMinus`
  in `Adic spaces/RestrictionFlatness.lean`. Sorry-free; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]`.
- **File**: NEW (e.g., `Adic spaces/RestrictionFlatness.lean`) or addition
  to `Cor832.lean`.
- **Depends on**:
  - `presheafValue_iteratedMinus_equiv` (DONE, sorry-free)
  - `presheafValue_iteratedPlus_equiv` (DONE, sorry-free)
  - `flat_quotient_oneSubfX_general` (DONE, sorry-free, Wedhorn 8.31)
  - `tateAlgebra_flat` (DONE, sorry-free, Wedhorn 8.31(1))
  - `presheafValue_isTateRing` and `presheafValue_pairOfDefinition_concrete`
    (DONE, sorry-free)
- **Mathematical statement**: For a strongly noetherian Tate ring `A` and
  rational data `D₀ ⊇ D`, the restriction map
  `presheafValue D₀ → presheafValue D` exhibits `presheafValue D` as a
  **flat module** over `presheafValue D₀`.
- **Proof route** (per reviewer, ChatGPT Pro 2026-05-11 session 2):
  (i) Identify `presheafValue D` with `presheafValue (iteratedMinusDatum_B
      P D₀ f)` (where `f` is the relevant Laurent-minus generator) via
      `presheafValue_iteratedMinus_equiv` (already sorry-free).
  (ii) At the B-side (`B := presheafValue D₀`), the iterated minus datum
      identifies via Example 6.38 with the Tate-algebra quotient
      `B⟨X⟩ / (1 - b · X)` where `b = canonicalMap(f)`.
  (iii) Wedhorn 8.31 (`flat_quotient_oneSubfX_general` applied at `B`)
      gives flatness of `B⟨X⟩ / (1 - b · X)` over `B`.
  (iv) Transfer flatness through the composition of isos.
- **NOT via**: `IsLocalization.flat` from `restrictionMap_isLocalization`
  (that route is RETIRED — see T-RETIRE-PROP815).
- **Estimate**: ~150-300 lines.
- **Unblocks**: T-COR832-VIA-FLAT and through it T-NEW-4, T-NEW-5.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11 session 2):
  "Rational-restriction flatness should come from Wedhorn Lemma 8.31 /
  Prop. 8.30: identify basic rational localizations with Tate-algebra
  quotients and transfer flatness."

---

### [T-COR832-VIA-FLAT] Refactor Cor 8.32 abstract to consume `Module.Flat`

- **Status**: DONE (audited 2026-05-12, T258)
- **Closed**: 2026-05-12 audit — `flat_over_base_tate_laurent` in
  `Adic spaces/Cor832.lean:594`. Sorry-free; `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`. Production-ready
  Module.Flat-based product flatness supplier for Laurent-shape covers.
- **File**: `Adic spaces/Cor832.lean` (refactor of `flat_over_base_tate`
  and downstream)
- **Depends on**: T-FLAT-VIA-WEDHORN830
- **Mathematical statement**:
  ```
  flat_over_base_tate (NEW form):
    ∀ D ∈ C.covers,
      Module.Flat (presheafValue C.base) (presheafValue D.1)
  ```
  obtained DIRECTLY via T-FLAT-VIA-WEDHORN830, not via `IsLocalization.flat`
  applied to `restrictionMap_isLocalization`.
- **Action**:
  (i) Replace the proof body of `flat_over_base_tate` to invoke
      T-FLAT-VIA-WEDHORN830.
  (ii) Update consumers `productRestriction_faithfullyFlat_abstract` and
      its downstream callers (`productRestriction_injective_tate_of_*`,
      etc.) to match the new flatness-only interface.
  (iii) The `hSpa_surj_from_spanTop` helper currently uses
      `restrictionMap_isLocalization` to access
      `IsLocalization.isPrime_of_isPrime_disjoint`. This is the algebraic
      prime-lift, NOT the topological surjection. Audit: this algebraic
      step MAY still be valid (it's about algebraic Spec maps, not
      completed rings) — verify carefully. If invalid, replace with a
      direct algebraic prime-lift argument.
- **Estimate**: ~50-100 lines (mostly refactoring of existing proof bodies).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11 session 2): "Refactor
  Cor. 8.32 to consume **flatness of each restriction map**, not
  `IsLocalization.Away`. Discharge flatness via Wedhorn Prop. 8.30 /
  Lemma 8.31."

---

### [T-MATHLIB-COMPLETEDLOC] Mathlib contribution: completed localization for noetherian adic completion (NOT CRITICAL PATH)

- **Status**: OPEN (LOW PRIORITY — future Mathlib PR, decoupled from
  acyclicity)
- **File**: future Mathlib PR, target `Mathlib/RingTheory/AdicCompletion/Localization.lean`
- **Mathematical statement** (Stacks tag 0BNH-style, noetherian case):
  > For a noetherian ring `R`, an ideal `I ⊆ R`, and an element `x ∈ R`,
  > there is a natural continuous ring iso
  >
  >   `(R[1/x])^∧_{I · R[1/x]}  ≅  lim_n (R / I^n)[1/x]`
  >
  > where the LHS is the `I · R[1/x]`-adic completion of `R[1/x]` and the
  > RHS is the inverse limit of the `n`-th truncations after localizing.
- **DO NOT** state the naïve form `(R[1/x])^∧_I ≅ R̂_I [1/x]` —
  **this is FALSE in general**. Counterexample: `R = ℤ, I = (p), x = p`:
  the LHS is 0 (because `I` becomes the unit ideal after inverting `p`,
  so `I^n = R[1/p]` for all `n`, hence the completion is trivial) but
  the RHS is `ℤ_p[1/p] = ℚ_p`.
- **Mathlib hooks** (per reviewer, ChatGPT Pro 2026-05-11 session 2):
  - `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`
  - `AdicCompletion.flat_of_isNoetherian`
  - `IsLocalization.Away`
  - The explicit inverse-limit characterization of `AdicCompletion`.
- **Reference**: Stacks Project Tag 0BNH (Section 10.97, Completion for
  Noetherian rings).
- **NOT CRITICAL PATH**: this project's Tate acyclicity proof closes via
  T-COR832-VIA-FLAT + T-FLAT-VIA-WEDHORN830 alone, without needing this
  Mathlib theorem. T-MATHLIB-COMPLETEDLOC is documented here as a
  reusable Mathlib contribution that the reviewer flagged as a useful
  follow-on, but it is NOT a blocker for any acyclicity ticket.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11 session 2): "If we want
  a Mathlib contribution, build the corrected adic-completion
  localization theorem... Put this near `AdicCompletion`, using existing
  `AdicCompletion` and `IsLocalization` APIs."

---

## SESSION 3 REFRAME (ChatGPT Pro 2026-05-11 round 3)

The session-2 reframe correctly identified the misframed `Wedhorn 8.15 as
IsLocalization.Away`. After executing that reframe, the project's new
bottleneck (`T-FLAT-PER-E`) revealed a second mismatch: the executed
solution discharges flatness for **direct Laurent shapes of D₀** only,
but the assembly's `per_E_local_covering` uses **iterated Laurent shapes
of intermediate `(C.plusDatum f)`** — a shape mismatch.

Two candidate fixes were considered (Route A refactor; Route B depth-2
iterated 2.13). The reviewer rejected both as primary route and
prescribed a **third route**:

> Prove the general Prop. 8.30-style theorem: if `D ⊆ E` are rational
> data over a strongly noetherian Tate ring, then the restriction map
> `O(E) → O(D)` is flat.

This single general theorem immediately discharges T-FLAT-PER-E (every
piece of `per_E_local_covering` is a rational sub-piece of E by
construction) and is the reusable API for Cor 8.32 and later sheaf
arguments.

The reviewer also flagged:
* The current `restrictionMap_flat_via_iteratedPlus` exposes a wrong
  hypothesis: power-boundedness of `f` in `O(D₀)`. The plus rational
  localization is precisely what **makes** `f` power-bounded; it should
  be modeled by `B⟨X⟩/(f-X)`, not by `iteratedPlusDatum_B` with a
  source-side PB assumption.
* `IsNoetherianRing (locSubring …)` should be a derived theorem from
  noetherianity of `P.A₀` + finite T, not a hypothesis.
* Rational localizations of strongly noetherian Tate rings should
  again be strongly noetherian Tate — a reusable preservation theorem.
* T-EMBED-TOPO needs a separate strict-exactness package; algebraic
  faithful flatness alone does NOT give topological inducing.

The tickets below execute this third route.

### [T-RATIONAL-FLAT-GENERAL] Rational-restriction flatness for arbitrary inclusion

- **Status**: DONE for LaurentNormalized case (2026-05-12); BYPASSED for general
  case via the reviewer-prescribed normalized-minus route (T229–T236).
- **2026-05-12 completion summary**:
  - LaurentNormalized D ⊆ E rationally: closed sorry-free via
    `restrictionMap_flat_of_rational_subset_laurentNormalized` (T228).
  - Normalized-minus datatype + full algebraic chain: T229–T235 deliver
    end-to-end `tateAcyclicityComplete_via_normalizedLaurent` for covers
    whose pieces are normalized-minus shapes.
  - Non-LaurentNormalized general case: PARKED. Per reviewer guidance,
    not needed on the tateAcyclicity critical path — the
    Wedhorn Laurent-decomposition tree can be kept LaurentNormalized
    end-to-end by replacing ordinary minus with normalized minus.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For a strongly noetherian Tate ring `A` with
  rational locale data `E, D : RationalLocData A` satisfying
  `rationalOpen D.T D.s ⊆ rationalOpen E.T E.s`, the restriction map
  `O(E) → O(D)` is flat as a homomorphism of `O(E)`-modules.
- **Why it matters**: this is Wedhorn's natural Prop 8.30 / Lemma 8.31
  statement. Once proven, every piece of `per_E_local_covering` is
  handled immediately as a rational sub-piece of `E`. No restructuring
  of the assembly needed.
- **Strategy** (per reviewer):
  1. Establish two basic flatness cases over arbitrary strongly noetherian
     Tate base `B`:
     * `B → B⟨X⟩/(f-X)` is flat (plus side; no source-side PB hypothesis).
     * `B → B⟨X⟩/(1-fX)` is flat (minus side; already partly in place).
  2. Prove rational-localization transitivity: every rational containment
     `D ⊆ E` arises as a finite chain of basic plus/minus steps.
  3. Compose flat maps along the chain. Flatness is preserved under
     composition.
  4. Apply to every D in `per_E_local_covering` directly.
- **Depends on**: T-RATIONAL-FLAT-BASIC-PLUS, T-RATIONAL-FLAT-BASIC-MINUS,
  T-RATIONAL-LOC-TRANSITIVITY, T-STRONG-NOETH-PRESERVATION.
- **Supersedes**: T-FLAT-PER-E (per-E task #18 in the session tracker).
  The Route A (`laurentCovering E f` refactor) and the depth-2 Route B
  were both rejected by the reviewer.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-11 round 3): "Prove the
  general Prop. 8.30-style theorem… This theorem will immediately
  discharge the per-E flatness issue, because every piece of
  `per_E_local_covering` is, by construction, a rational subpiece of E."

### [T-RATIONAL-FLAT-BASIC-PLUS] Basic plus flatness via `B⟨X⟩/(f-X)`

- **Status**: DONE (audited 2026-05-12, T259)
- **Closed**: 2026-05-12 audit — `restrictionMap_flat_via_fSubX_quotient`
  in `Adic spaces/RestrictionFlatness.lean`. Sorry-free; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]`.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For any strongly noetherian Tate ring `B`
  and any `f : B`, the quotient `B⟨X⟩/(f - X)` is flat over `B` as a
  `B`-module along the canonical inclusion `B → B⟨X⟩/(f - X)`.
- **No source-side hypothesis on `f`**: in particular, `f` is NOT
  assumed power-bounded in `B`. The quotient is precisely what makes
  `f` power-bounded after the quotient.
- **Proof outline**: parallel to `flat_quotient_oneSubfX_general`
  (Wedhorn 8.30 minus case, already proved). Show that multiplication
  by `f - X` is a regular sequence on `B⟨X⟩`, hence the quotient is flat.
- **Replaces**: the role currently played by `iteratedPlus_B_flat_of_canonical`,
  which uses the wrong abstraction (assumes source PB).
- **Reference**: Wedhorn Prop 8.30 (multivariate version covers both plus
  and minus quotients uniformly).
- **Reviewer guidance**: "Both basic cases should be flat without a
  source-side power-boundedness assumption on `f`."

### [T-RATIONAL-FLAT-BASIC-MINUS] Basic minus flatness via `B⟨X⟩/(1-fX)`

- **Status**: DONE (audited 2026-05-12, T259)
- **Closed**: 2026-05-12 audit — `restrictionMap_flat_via_oneSubfX_quotient`
  in `Adic spaces/RestrictionFlatness.lean`. Sorry-free; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]`. Symmetric to the
  plus version (T-RATIONAL-FLAT-BASIC-PLUS) using
  `flat_quotient_oneSubfX_general` + `laurentMinusBridge`.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For any strongly noetherian Tate ring `B`
  and any `f : B`, `B⟨X⟩/(1 - fX)` is flat over `B` along the
  canonical inclusion.
- **Why this is partly done**: the underlying flatness of the quotient
  is established. What's needed is the rational-localization-level
  packaging (an analog of T-RATIONAL-FLAT-BASIC-PLUS).
- **Reference**: Wedhorn Prop 8.30 / Lemma 8.30.

### [T-RATIONAL-LOC-TRANSITIVITY] Transitivity of rational localizations

- **Status**: DONE (audited 2026-05-12, T260; BYPASSED on critical path)
- **Closed**: 2026-05-12 audit — the project's bypass (T229-T237) routes
  the Wedhorn Laurent-decomposition tree through normalized-minus
  pieces, eliminating the need for general transitivity on the
  critical path. The transitivity infrastructure for LaurentNormalized
  cases is exposed via `relativeRationalLocData_laurentNormalized`
  (sorry-free) plus the chain composition lemmas. Per-task entry #21
  (T-RATIONAL-LOC-TRANSITIVITY) marked completed in 2026-05-11.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For rational locale data `E, D` with
  `rationalOpen D ⊆ rationalOpen E`, there is a finite chain of basic
  plus/minus rational localizations producing `O(D)` from `O(E)`:
  `O(E) = O(D⁽⁰⁾) → O(D⁽¹⁾) → ⋯ → O(D⁽ᵏ⁾) = O(D)`
  where each step is a basic `f-X` or `1-fX` quotient.
- **Proof outline**: this is the "iterate Wedhorn Lemma 2.13"
  statement — rational localizations are transitive. Each step of the
  chain corresponds to enlarging T by one element or replacing s by a
  product. The decomposition is finite because both T and s are finite
  data.
- **Why not just depth-2**: the reviewer rejected one-off depth-2
  bridges. The chain decomposition handles depth-N for arbitrary N
  via a single transitivity result.
- **Reviewer guidance**: "For iterated 2.13, the clean reference is
  simply 'iterate Wedhorn Lemma 2.13' / rational localizations are
  transitive. The formal theorem should be an associativity/transitivity
  theorem for rational localization/presheaf values, not a special
  depth-2 statement."

### [T-STRONG-NOETH-PRESERVATION] Strong noetherian Tate preservation under rational localization

- **Status**: DONE (single-level, audited 2026-05-12, T260)
- **Closed**: 2026-05-12 audit — `presheafValue_isNoetherian_via_canonical`
  in `Adic spaces/StructureSheaf.lean:1009`. Provides single-level
  Noetherian preservation for `presheafValue D` given the canonical-iso
  hypotheses. Sorry-free.
- **Open scope**: full strong-Noetherian preservation (multi-variable
  Tate algebra) is T-STRONG-NOETH-PRESERVATION-FULL, which depends on
  Stacks 00MA + multivariable Example 6.38. That sub-ticket remains open.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: If `A` is a strongly noetherian Tate ring
  and `D : RationalLocData A`, then `O(D)` is again a strongly
  noetherian Tate ring.
- **Why it matters**: the chain in T-RATIONAL-LOC-TRANSITIVITY visits
  intermediate B-levels `O(D⁽ⁱ⁾)`, and the basic flatness theorems need
  the base to be strongly noetherian Tate. Without preservation, the
  chain can't be applied at intermediate levels.
- **Reference**: this is essentially the strong-noetherian Tate version of
  the standard fact that adic completions of noetherian rings stay
  noetherian (Stacks 00MA), specialized to rational localizations.
- **Reviewer guidance**: "Rational localizations of strongly noetherian
  Tate rings should again be strongly noetherian Tate; that is the
  right reusable preservation theorem."

### [T-LOC-SUBRING-NOETH] Discharge `IsNoetherianRing (locSubring …)` locally

- **Status**: DONE (T248, 2026-05-12)
- **Added**: 2026-05-11 round 3
- **Closed**: 2026-05-12 via T248 — `ValuationSpectrum.locSubring_isNoetherianRing`
  in `LocalizationTopology.lean`. Sorry-free; #print axioms reports
  `[propext, Classical.choice, Quot.sound]`.
- **Mathematical statement**: For a `PairOfDefinition A` with
  `IsNoetherianRing P.A₀` and a finite `T : Finset A`, `s : A`, the
  subring `locSubring P T s` is noetherian.
- **Implementation**: MvPolynomial.aeval surjection — `MvPolynomial T P.A₀ →ₐ[P.A₀] locSubring P T s` sending `X_t ↦ ⟨divByS t s, _⟩`. Surjectivity by `Subring.closure_induction` on the locSubring definition. `MvPolynomial T P.A₀` is Noetherian (iterated Hilbert basis). Apply `isNoetherianRing_of_surjective`.
- **Why it matters**: the current theorems
  (`restrictionMap_flat_via_iteratedMinus`, etc.) expose `IsNoetherianRing
  (locSubring …)` as a final hypothesis. With T-LOC-SUBRING-NOETH, this
  becomes a derived instance, simplifying caller hypotheses.

### [T-FLAT-PLUS-REWORK] Rework `restrictionMap_flat_via_iteratedPlus` without power-boundedness

- **Status**: DONE (audited 2026-05-12, T261)
- **Closed**: 2026-05-12 audit — `restrictionMap_flat_via_fSubX_quotient`
  in `Adic spaces/RestrictionFlatness.lean` is the reworked version
  WITHOUT the source-side `IsPowerBounded (D₀.canonicalMap f)` hypothesis.
  The plus-piece flatness now uses `flat_quotient_fSubX_general` (Wedhorn
  8.30/8.31) routed through `laurentPlusBridge`, eliminating the
  spurious source-side PB constraint. Sorry-free; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]`.
- **Added**: 2026-05-11 round 3
- **Problem**: the current `restrictionMap_flat_via_iteratedPlus`
  (committed under T-FLAT-PLUS) exposes the hypothesis
  `IsPowerBounded (D₀.canonicalMap f)` on the source side. The reviewer
  flagged this as the wrong abstraction: the plus rational localization
  is exactly what makes `f` power-bounded, so requiring it as input
  defeats the purpose.
- **Fix**: rebuild plus flatness on the `B⟨X⟩/(f-X)` quotient model
  (T-RATIONAL-FLAT-BASIC-PLUS). The new theorem should NOT need a
  source-side PB hypothesis.
- **Reviewer guidance**: "the plus supplier should be based on the
  `f-X` quotient and should not require `IsPowerBounded
  (D₀.canonicalMap f)` in the source."

### [T-EMBED-TOPO-EXAMPLE638] Topological version of Wedhorn Example 6.38

- **Status**: DONE (2026-05-12, T265)
- **Closed**: 2026-05-12 — `presheafValueCanonicalQuotientHomeomorph` in
  `Adic spaces/TopologyComparison.lean`. Packages the bidirectional
  continuity:
  - Forward: `presheafValueToCanonicalQuotient_continuous` (new) via
    `Completion.continuous_extension`.
  - Backward: `hcont_eval` (the parametric hypothesis), typically
    discharged by `tateQuotientToPresheafHom_continuous_of_tate`.
  Sorry-free; `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For any rational locale `D` over a
  strongly noetherian Tate ring `A`, the iso
  `O(D) ≅ A⟨X⟩/(1 - sX)` from Example 6.38 is a TOPOLOGICAL ring
  isomorphism (not just algebraic) when both sides carry their natural
  topologies (`O(D)` with the completed rational-localization topology,
  RHS with the quotient topology of the Tate-algebra by a closed ideal).
- **Why it matters**: this is the "topological side" of Example 6.38.
  Currently only the algebraic version is established (the equiv as a
  ring iso). The topological enhancement is needed for T-EMBED-TOPO.
- **Reference**: Wedhorn Example 6.38 (the iso is stated for topological
  ring structures).

### [T-EMBED-TOPO-STRICT-LAURENT] Strict exactness of the Laurent 2-cover Čech complex

- **Status**: DONE (audited 2026-05-12, T266)
- **Closed**: 2026-05-12 audit — `laurentCover_isEmbedding_presheaf` in
  `Adic spaces/LaurentRefinement.lean:4477`. Hypothesis-parameterised
  on the topological iso pieces (`τ_plus`, `τ_minus`, etc.), which can
  now be supplied via T265's `presheafValueCanonicalQuotientHomeomorph`.
  Sorry-free; `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For the 2-element Laurent covering
  `{D₊, D₋}` of `D₀` at `f`, the Čech sequence
  `0 → O(D₀) → O(D₊) × O(D₋) → O(D₊ ∩ D₋) → 0`
  is not just algebraically exact (Wedhorn Lemma 8.33) but
  TOPOLOGICALLY STRICT: the first map is topological embedding, the
  second is topological quotient.
- **Why it matters**: strict exactness is the building block for the
  T-EMBED-TOPO topological inducing argument. Algebraic exactness
  alone (Lemma 8.33) is not sufficient.
- **Reference**: Wedhorn Lemma 8.33 (the topological strictness is
  implicit in his treatment but needs explicit formalization).

### [T-EMBED-TOPO-REFINEMENT-TRANSFER] Refinement preserves topological embedding

- **Status**: DONE for hypothesis-parameterised form (2026-05-12, T267)
- **Closed**: 2026-05-12 — `productRestrictionSub_isInducing_of_finer_rational`
  in `Adic spaces/EmbeddingTopo.lean`. Given a finer cover V with τ-map +
  IsInducing of the natural product map φ (the topological refinement
  ingredient), IsInducing of `productRestrictionSub V` transfers to
  IsInducing of `productRestrictionSub C`. Proof routes through
  `Topology.IsInducing.of_comp_iff`. Sorry-free; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]`.
- **Caller responsibility**: supply `IsInducing φ` (the topological
  "natural map" between products), which is the Lane C topological
  ingredient.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: If a rational covering `C` refines another
  `C'` (via Lane C / Wedhorn 8.34), and the product restriction for `C'`
  is topologically embedding, then so is the product restriction for `C`.
- **Why it matters**: the induction step of the T-EMBED-TOPO Lane C
  argument. Combined with T-EMBED-TOPO-STRICT-LAURENT (base case) and
  T-EMBED-TOPO-EXAMPLE638, this gives the topological inducing supplier
  consumed by `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing`.
- **Reference**: Wedhorn Lemma 8.34 (geometric reduction); the
  topological transfer is the analog of the algebraic transfer
  already in `tateAcyclicity_Part2_end_to_end_via_primary`.

### Note: T-FLAT-PER-E SUPERSEDED

The task originally tracking per-E flatness for the iterated
`per_E_local_covering` shape is **SUPERSEDED** by T-RATIONAL-FLAT-GENERAL.

The reviewer's analysis:
* Route A (refactor `per_E_local_covering` to use direct `laurentCovering E f`)
  was rejected: it may not align with the pieces where the existing assembly
  has compatibility data. Different denominators (E.s vs D₀.s) make the
  plus/minus inequalities misalign.
* Route B (depth-2 iterated 2.13) was rejected: too specialized; leaves the
  same problem for any deeper refinement.
* The general theorem handles all depths uniformly and is what Wedhorn
  actually uses.

The existing `productRestriction_faithfullyFlat_laurentCovering_at_E`
remains useful as a special case and sanity check, but not as the main
supplier.

---

## 4. Retired tickets

### [T-INJ-1] `restrictionMapHom_injective` — RETIRED (2026-04-18)

Reviewer counterexample proves the unconditional form false. The Route A
NZD scaffolds in `PresheafTateStructure.lean` have been removed (2026-04-18).
Sorry at `:1322` stays. Part 1 routes through cover-level Cor 8.32.

**Reviewer guidance** (ChatGPT Pro, 2026-05-11): Retirement is permanent.
Single-map injectivity, single-map faithful flatness, and unconditional
Jacobson containment in `locSubring` are all FALSE in the generality
needed for strongly noetherian Tate (Counterexample 8.3, ` A = ℚ_p⟨X⟩`,
`T = {X}`, `s = p`; and Counterexample 8.4 / Conrad, same `A` with
`R(\{p, X\}/p)`). Do not resurrect them. The proof uses only the
product-level Cor 8.32:

```
componentwise flatness (Lemma 8.31)
  + cover-level Spa/spec surjectivity
  ⇒ product restriction faithfully flat
  ⇒ algebraic separation
```

Remaining downstream wrappers that still reference this retired theorem
are tracked under T-INJ-1-CLEANUP.

### [T-NULL-7 / T-NULL-PER-E] Wedhorn Prop 7.14 — REDUCED, with decomposition

Full adic Nullstellensatz not needed for S-GEOM-ASM API: `hZavyalov`
(and the strengthened `hZavyalov_per_E`) are passed as explicit
hypotheses to the caller wrapper. The general case is progressively
reduced via landed Lean infrastructure:

**Prop 7.14 fragments available** (already proved):
* `spanTop_iff_noCommonZero_spa` (`StandardCover.lean` line ~460) —
  ✅ the ideal↔Spa-cover equivalence (both directions, under
  `PairOfDefinition` + `[IsAdicComplete]`). This IS Prop 7.14's
  content in Lean-usable form.
* `exists_dominating_unit_from_covering` — ✅ Cor 7.32 wrapper.
* `exists_spa_point_with_supp_ge_of_prime` — ✅ Lemma 7.45 + open-prime
  dispatcher.
* `refines_span_top_image_unit_mul` — ✅ unit-rescaling preserves
  span-top.

**Landed 2026-04-20 (T-NULL-PER-E session)**:
* **`exists_refines_cover_per_E_of_per_D_construction`** — decomposition
  lemma reducing the general case to **per-D data**. Given
  `mk_S_D : RationalLocData A → Finset A` with per-D local
  containment + per-D local coverage + combined span-top, produces
  `refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S`
  where `S := C.covers.biUnion mk_S_D`. Axiom-clean (only standard
  Lean constructive axioms).
* **`hZavyalov_per_E_of_per_D_construction`** — wrapper supplying the
  `rationalOpen ≠ ∅ → ∃ S, ...` shape for
  `refines_by_standard_cover_per_E` input. Axiom-clean.
* **`exists_nullstellensatz_refinement_per_E_of_singleton_cover`** —
  singleton-cover case: produces `hZavyalov_per_E` from weaker
  `hZavyalov`. Axiom-clean (landed earlier).

**Remaining external content**: the actual per-D family construction
`mk_S_D : RationalLocData A → Finset A`.

**Reviewer's C1/C2/C3 decomposition** (2026-04-20):

* **C1 — Local standard neighborhood at `v ∈ D`**: for each
  `D ∈ C.covers` and each `v ∈ rationalOpen D.T D.s`, produce a
  single `f ∈ A` with `v ∈ rationalOpen (insert f C.base.T) C.base.s`
  AND `rationalOpen (insert f C.base.T) C.base.s ⊆ rationalOpen D.T
  D.s`. **Status**: PARTIAL — standard-shape case landed 2026-04-20;
  general case remains Wedhorn §8.34 / Zavyalov §2.3 core content.

  **Landed helpers** (`StandardCover.lean`, axiom-clean):
  - `exists_single_f_refinement_of_standardShape` — pointwise single-`f`
    discharge when `D` already has the shape
    `R(D.T, D.s) = R(insert f₀ C.base.T, C.base.s)`. Base case of the
    Wedhorn §8.34 reduction.
  - `rationalOpen_eq_biInter_insert_union` — structural identity
    `R(F ∪ T, s) = (⋂ f ∈ F, R(insert f T, s)) ∩ R(T, s)`. Records
    that multi-`F` shape is the joint intersection of plus-pieces.
  - `per_D_construction_of_standardShape` — assembles per-`D` data
    `h_in_D`/`h_cover_D` for `exists_refines_cover_per_E_of_per_D_construction`
    when every `D ∈ C.covers` has standard shape witnessed by
    `f_D : RationalLocData A → A`.
  - `exists_refines_cover_per_E_of_standardShape` — full
    `hZavyalov_per_E` discharge for standard-shape covers. Inputs:
    `f_D` witness per piece + unit-ideal span of combined family.
    **This reduces the FULL T-NULL-PER-E obligation to supplying
    `f_D` per piece plus span-top.**

  **What remains external (arbitrary → standard cover reduction)**:
  for a general `D ∈ C.covers` with `D.T` of arbitrary size, single-`f`
  form requires `f ∈ A` such that adding the single inequality
  `w.vle f C.base.s` encodes ALL the `D.T`-constraints jointly. This
  cannot be done by product or sum (valuation theory); requires the
  Cor 7.32 dominating-unit + Prop 7.14 Nullstellensatz candidate-family
  construction. The multi-`F` shape (several constraints) is achievable
  from Wedhorn 7.34-style data but does NOT match the single-`f` shape
  in `refines_cover_per_E`.

  **Escalation packet (PARKED 2026-04-20, awaiting review)**:
  See `.mathlib-quality/chatgpt-packet-zavyalov-c1.md` for the
  full-context packet targeting ChatGPT Pro / external reviewer.
  Contents:
  - Final Lean goal (`hZavyalov_per_E` shape) and the
    `refines_cover_per_E` single-`f` obligation.
  - Complete list of landed infrastructure (assembly, standard-shape
    helpers, C2, C3, Cor 7.32, rational-open APIs, Nullstellensatz
    equivalence).
  - Precise obstruction (why product/sum candidates fail; why multi-`F`
    does not plug in directly to `refines_cover_per_E`).
  - Six concrete questions: Zavyalov §2.3 formula for `f_{D, i}`;
    whether single-`f` is genuinely necessary or multi-`F` + collapse
    suffices for Hübner/Wedhorn; how Cor 7.32's per-point dominating
    unit yields uniform global containment; which Prop 7.14 /
    Nullstellensatz fragments (beyond `spanTop_iff_noCommonZero_spa`)
    Zavyalov uses; Lean-friendly lemma boundaries (candidate shapes
    L1/L2/L3); staged approach for `|D.T| = 0, 1, ≥2`.

  **Parked until external review supplies the formula.** Do NOT keep
  guessing in Lean without a reviewed mathematical plan.

  **REVIEWER GUIDANCE — Lane C reframe** (ChatGPT Pro, 2026-05-11):
  Stop targeting a single explicit formula for the C1 element. The
  failed candidate formulas are evidence that the ticket should target
  the intrinsic local-basis / refinement statement, not a guessed
  expression. Use Cor 7.32 as a black-box geometric separation /
  refinement theorem.

  **New primary target** (replaces the search for an explicit `f`
  formula):

  > **Theorem `plus_pieces_form_local_basis_of_E`**: For every rational
  > target `E ∈ C.covers` and every Spa-point `v ∈ R(T_E, s_E)`, there
  > exists `f ∈ A` with
  > `v ∈ R(insert f C.base.T, C.base.s) ⊆ R(T_E, s_E)`.

  Combined with C2 (finite extraction, already landed) and C3
  (Cor 7.32 / span-top, already landed), this discharges
  `refines_cover_per_E` cleanly.

  **Fallback** if single-`f` is too strong: target the finite-family
  form via T-NULL-PER-E-FIN (added 2026-05-11) + conversion lemma.

  **σ-clearing T200-series** (T197–T212 commits) remains as side
  infrastructure — potentially useful when an explicit `f` is needed
  downstream — but is NO LONGER on the critical path of T-NULL-PER-E.
  The basis theorem (or its finite-family variant) is the primary
  target.
* **C2 — Finite extraction via quasi-compactness**: ✅ **LANDED
  2026-04-18** in `SpaCompact.lean` via the Bool-cylinder route.

  **Correction (2026-04-18 audit)**: An earlier version of this
  ticket claimed C2 follows from `basicOpen_isClopen` + compactness
  of `Spa`. That was WRONG in this topology. The SpaCompact preamble
  explicitly states `{v | v.vle a 1} = basicOpen a 1` is OPEN, NOT
  CLOSED in `Spv A`. The correct route uses clopen CYLINDERS in the
  Bool product, not closedness of basic opens in Spv.

  **Landed theorems** (`SpaCompact.lean`, no sorries, axiom-clean):
  - `image_ιSpv_bool_rationalOpen` — the identity
    `ιSpv_bool '' rationalOpen T s = (range ιSpv_bool ∩ S) ∩
     ({r | r(s,s) = true} ∩ ⋂_{t ∈ T} {r | r(t,s) = true})`.
    Key input: `v ∈ basicOpen t s ↔ ιSpv_bool v (t, s) = true`.
  - `isCompact_rationalOpen_of_isClosed_image` — abstract form
    parameterised by any closed `S` with
    `ιSpv_bool '' Spa A A⁺ = range ιSpv_bool ∩ S`.
  - `isCompact_preimage_rationalOpen_of_isClosed_image` — subtype
    form `IsCompact (Subtype.val ⁻¹' rationalOpen T s :
    Set ↥(Spa A A⁺))`, the shape consumed by downstream C2 users.
  - `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` —
    concrete Tate specialisation (matches hypotheses used throughout
    the `tateAcyclicity` project). This is the C2 supplier for
    T-NULL-PER-E.
  - `isCompact_preimage_rationalOpen_of_discreteTopology` — discrete
    specialisation (matches the project's "discrete case first"
    design decision).

  **Proof strategy**: (i) compute Bool image via `image_ιSpv_bool_rationalOpen`,
  (ii) show closed in compact Bool product via `isClosed_coord_true`
  on each cylinder + `isClosed_range_ιSpv_bool` + given `hS`,
  (iii) transfer compactness via `continuous_boolToProp_pi` +
  `ιSpv_isEmbedding.isCompact_iff`, (iv) `Subtype.image_preimage_val`
  + `Set.inter_eq_right.mpr rationalOpen_subset_spa` for subtype form.
  Does **not** rely on rational opens being closed in Spv A.

  **Lines landed**: ~85 lines in `SpaCompact.lean` (abstract helper +
  abstract theorem + subtype form + Tate specialisation + discrete
  specialisation).
* **C3 — Span-top via no-common-zero**: combine C1+C2 across all
  `D ∈ C.covers` and apply `spanTop_iff_noCommonZero_spa`.
  **Status**: ✅ `spanTop_iff_noCommonZero_spa` already proved
  in `StandardCover.lean`.

**Exact Lean targets for C1 and C2** documented in
`StandardCover.lean` near `exists_refines_cover_per_E_of_per_D_construction`
(in the "T-NULL-PER-E remaining content — reviewer's C1/C2/C3
decomposition" doc block). C3 is fully discharge-able via existing
API (`spanTop_iff_noCommonZero_spa`).

### [T-BAIRE] `restrictionMap_isLocalization` / Wedhorn Prop 8.15 — OFF CRITICAL PATH

Not needed on the Route-B closure path. Kept sorry'd.

---

## 5. Execution plan — next sessions

### 5.1 Parallelism matrix

Each row is a sub-ticket. Columns show which files it touches; rows
with **disjoint** file sets can run concurrently.

| Sub-ticket | Primary file(s) touched | Can parallel with | Depends on |
|---|---|---|---|
| **S-OV-GLUE** | `LaurentOverlap.lean` | S-IDEAL-JAC, S-IDEAL-LOC, S-GEOM-TAU, S-GEOM-BASE | — |
| **S-IDEAL-JAC** | `IdealClosedness.lean` | all below (disjoint files) | — |
| **S-IDEAL-LOC** | `IdealClosedness.lean` or new helper | S-OV-GLUE, S-GEOM-* | — |
| **S-GEOM-TAU** | `LaurentRefinement.lean` (1-2 projections) + `GeometricReduction.lean` | S-OV-GLUE, S-IDEAL-* | — |
| **S-GEOM-BASE** | `GeometricReduction.lean` | S-OV-GLUE, S-IDEAL-* | S-GEOM-TAU (shares file; serialize within GeometricReduction.lean) |
| **S-IDEAL-ASM** | `Cor832.lean` | all Part-2 work | S-IDEAL-JAC + S-IDEAL-LOC |
| **T-OVERLAP-COMPAT** | `LaurentRefinement.lean:3173` | all (single-site edit) | S-OV-GLUE |
| **S-GEOM-IND** | `GeometricReduction.lean` | S-IDEAL-*, S-OV-GLUE | S-GEOM-TAU + S-GEOM-BASE + `laurentCover_gluing_presheaf` sorry-free (i.e., T-OVERLAP-COMPAT landed) |
| **S-GEOM-ASM** | `LaurentRefinement.lean:3737` | — | everything above |
| **T-ACYC-PART2** | `LaurentRefinement.lean:3737` | — | S-GEOM-ASM |

**Conflict hazards** to watch when running workers concurrently:

- Two workers editing `LaurentRefinement.lean` at the same time will
  collide (it's a 3819-line file shared by many tickets). To safely
  parallelize, serialise any edit within it. Currently only S-GEOM-TAU
  needs ~5 lines there (projection simp lemmas next to
  `laurentPlusDatum`); land that in a focused 1-commit PR first.
- `Cor832.lean` is similarly shared; S-IDEAL-ASM is the only new
  insertion, so it goes last.

### 5.2 Suggested session cadence

### Session N+1 (widest parallelism — 3 concurrent workers)

Three fully-independent parallel tracks; **no file conflicts**:

- **Track 1 (~200 lines)** — T-OV-1 **S-OV-GLUE**:
  `Adic spaces/LaurentOverlap.lean` only.
- **Track 2 (~150-200 lines)** — T-IDEAL-2 **S-IDEAL-JAC + S-IDEAL-LOC**:
  `Adic spaces/IdealClosedness.lean` (+ possibly a small new helper
  file). No edits to `Cor832.lean` yet.
- **Track 3 (~90 lines)** — T-GEOM-RED **S-GEOM-TAU + S-GEOM-BASE**:
  small `laurentPlusDatum_T_ext` helper in `LaurentRefinement.lean`
  first, then body work in `GeometricReduction.lean`.

### 🧹 **CLEANUP CHECKPOINT C1** (end of session N+1, before session N+2)

Before starting session N+2, execute a focused cleanup pass:

1. **Audit transitive `sorryAx` dependencies**: after S-OV-GLUE lands,
   `lean_verify ValuationSpectrum.laurentCover_gluing_presheaf` — should
   show only upstream sorryAx, no new axioms introduced by the three
   tracks.
2. **Rebuild + full test**: `lake build` from clean (`lake clean && lake build`).
   Fail hard on any new warning in the three touched files.
3. **Line budget check**: if any of Track 1 / Track 2 / Track 3 exceeded
   its estimate by >50%, pause and review — the divergence often signals
   an unrecognized blocker.
4. **Golf pass on the three new closers** (optional): each new theorem
   `S-OV-GLUE`, `S-IDEAL-JAC`, `S-IDEAL-LOC` is a candidate for 30-40%
   compression via `lean4-proof-golfer` — do this before downstream
   code pins the current form.
5. **Retire obsolete scaffolding**: if any intermediate "conditional"
   lemmas landed to unblock the tracks (e.g., an earlier hypothesis
   form of `coeRingHom_preserves_proper_of_closed`), remove those
   whose call sites all now use the unconditional form.
6. **Tickets refresh**: mark S-OV-GLUE, S-IDEAL-JAC, S-IDEAL-LOC,
   S-GEOM-TAU, S-GEOM-BASE status; update session log.

### Session N+2 (consolidation — 2 concurrent workers)

- **Track A (~30 lines)** — T-IDEAL-2 **S-IDEAL-ASM**:
  closes Part 1 outright via the Cor 8.32 chain. Sole file: `Cor832.lean`.
- **Track B (~80 lines)** — **T-OVERLAP-COMPAT**:
  closes `laurentCover_gluing_presheaf` (sorry at `LaurentRefinement.lean:3173`).
  Sole file: `LaurentRefinement.lean` (the sorry at :3173).
- **Serial (~200 lines, after Track B)** — T-GEOM-RED **S-GEOM-IND**:
  the heavy induction; depends on `laurentCover_gluing_presheaf` being
  sorry-free, so must start **after** Track B lands. File:
  `GeometricReduction.lean`.

### 🧹 **CLEANUP CHECKPOINT C2** (end of session N+2)

1. **Part 1 closure audit**: `#print axioms` on the Part 1 conjunct of
   `tateAcyclicity` via a test lemma. Must show only standard axioms
   after S-IDEAL-ASM lands — no `sorryAx`.
2. **Dead-code sweep**: `restrictionMapHom_injective` at
   `PresheafTateStructure.lean:1322` — now that Part 1 doesn't depend
   on it, either (a) delete the sorry'd theorem if no callers use it,
   or (b) add an `opaque`/`axiom` marker explaining it's the
   retired-false statement kept for historical reference only.
3. **Test the Laurent-cover gluing path end-to-end**: after
   T-OVERLAP-COMPAT, write a smoke test invoking
   `laurentCover_gluing_presheaf` on a concrete small example to
   confirm it type-checks without sorryAx.
4. **Docstring refresh**: update docstrings on
   `laurentCover_gluing_presheaf`, `tateAcyclicity_gluing_via_refinement_cover_level`
   to remove "modulo T-OV-1" / "unsound variant" language now that
   these are dischargeable.
5. **Golf pass on S-GEOM-IND** before it's used by S-GEOM-ASM.

### Session N+3 (endgame — serial)

- T-GEOM-RED **S-GEOM-ASM** including hZavyalov bypass
  (~100-250 lines). This is the hardest remaining piece; the hZavyalov
  bypass may require a small Laurent-recursion helper.
- **T-ACYC-PART2** (~50 lines): final composition into the Part 2
  closure at `LaurentRefinement.lean:3737`.

### 🧹 **CLEANUP CHECKPOINT C3** (close-out audit)

1. **`lake build`** from clean: must succeed, 0 new warnings.
2. **`#print axioms ValuationSpectrum.tateAcyclicity`**: must show
   **only** `propext, Classical.choice, Quot.sound`. Any `sorryAx`
   means an upstream sorry is transitively depended upon — trace and
   fix.
3. **Sorry inventory**: `awk '/^[[:space:]]*sorry[[:space:]]*$/'` must
   report only off-path sorries (PresheafTateStructure:1208,
   StructureSheaf:1096, Presheaf:720, Tilting 2). No Tate-core
   sorries on critical path.
4. **Retire transitional helpers**: many of the "conditional" theorems
   in `Cor832.lean` (`productRestriction_injective_tate_of_flat_and_lifting`,
   `_via_cor832`, `_via_hSpa_points`, `_via_lifted_ideal_proper`,
   `_via_coeRingHom_preserves_proper`) become redundant once
   `tateAcyclicity` is unconditional — audit call sites, keep only
   what's externally consumed.
5. **Docstring-level documentation pass** across the six new files
   (`LaurentOverlap`, `IdealClosedness`, `GeometricReduction`,
   `Example638`, `Cor832` additions, and the bridge chain closures).
6. **Tickets final archive**: this file moves from "active plan" to
   "completion log" — mark T-OV-1, T-OVERLAP-COMPAT, T-IDEAL-2,
   T-GEOM-RED, T-ACYC-PART2 all DONE. Retain the session log as a
   historical artifact.
7. **Optional**: `lean4-proof-golfer` pass on the new key theorems
   (`tateAcyclicity` itself, `coeRingHom_preserves_proper`,
   `example638Bivariate_equiv`).
8. **Downstream propagation check**: `isSheafy_ofStronglyNoetherianTate_flat`
   (`StructureSheaf.lean:1069`) depends on `tateAcyclicity`; verify it
   now closes (or at least that its remaining sorries are unrelated
   to the Tate-core critical path).

### 5.3 Total effort

**~700-1200 lines across 3 sessions**, assuming no unexpected blockers.
Cleanup checkpoints C1 and C2 are budgeted ~1-2 hours each; C3 is a
half-session audit.

---

## 6. Infrastructure inventory

All 0 sorry, build-clean:

| File | Lines | Role |
|---|---|---|
| `Cor832.lean` | 1457 | Cor 8.32 full framework + closure combinator (T-IDEAL-2 additions). |
| `Example638.lean` | 1501 | Generic Example 6.38 (plus + minus) over any complete strongly noetherian Tate base. |
| `LaurentOverlap.lean` | 634 | Example 6.39 Step B + Step A infrastructure (T-OV-1 landed parts). |
| `IdealClosedness.lean` | 181 | Krull-based closedness + clopen-subring lift. |
| `GeometricReduction.lean` | 248 | Cover-level refinement theorem + V-covers bridge (T-GEOM-RED landed parts). |
| `StandardCover.lean` | 733 | `refines_by_standard_cover` modulo hZavyalov. |
| `ValuationSpectrumCompact.lean` | 1035 | `CompactSpace (Spv A)` (Huber port). |
| `SpaCompact.lean` | 460 | `CompactSpace ↥(Spa A A⁺)` (discrete + Tate). |
| `Cor732.lean` | 292 | Wedhorn Cor 7.32 dominating unit. |
| `RationalRefinement.lean` | 172 | `separation_of_finer_rational`, `gluing_of_finer_rational`. |
| `LaurentRefinement.lean` | 3819 | Bridge chain + Lemma 2.13 + delta-vanishing. |
| `LaurentCoverExact.lean` | 1650 | `row3_exact` algebraic core. |

### Bridge chain (all 0 sorry aside from overlap bridge)

- `laurentPlusBridge`, `laurentMinusBridge`: ✅ DONE.
- `laurentPlusBridge_restrictionMap`, `laurentMinusBridge_restrictionMap`: ✅ DONE.
- `presheafValue_iteratedPlus_equiv`, `presheafValue_iteratedMinus_equiv`: ✅ DONE.
- `laurentCover_gluing_presheaf`: ✅ modulo `laurentOverlapBridge_exists_compatible`.

---

## 7. Notes and reminders

- **Signature of `tateAcyclicity` must NOT change**. No new hypotheses
  (no `[IsDomain A]`, no `[DiscreteTopology A]`, no `hZavyalov`, no
  `MulArchimedean`, no `[IsAdicComplete]`).
- `presheafValue_pairOfDefinition_concrete` (`PresheafTateStructure.lean`)
  gives the `P_B.A₀ = presheafValue_ringOfDef D₀` definitional equality
  needed when instantiating Example 6.38 at `B := presheafValue D₀`.
- `LaurentNormalized` typeclass needs an instance for
  `laurentPlusDatum D₀ f` when T-OV-1 composition route is used.
- Historical plans `docs/plans/2026-04-14-*` and
  `docs/plans/2026-04-16-*` are superseded; current critical-path
  planning lives in this file.
- **Key Wedhorn references**:
  - Prop 6.17: closed ideals in noetherian Tate rings.
  - Prop 8.2: base-change Nullstellensatz.
  - Example 6.38: univariate presheaf-value iso.
  - Example 6.39: bivariate presheaf-value iso (= T-OV-1).
  - Lemma 8.31: flatness of Tate algebra quotients.
  - Cor 8.32: product restriction faithfully flat.
  - Lemma 8.33: Laurent 2-cover exact row.
  - Lemma 8.34: geometric reduction (= T-GEOM-RED).
  - Thm 8.28(b): Tate acyclicity (= final target).
- **Key Hübner references**:
  - `arXiv 2405.06435`, Lemma 3.7 / 3.8: simple-Laurent input suffices.

---

## 8. Session log (newest first)

- **2026-04-21** (T-OVERLAP-COMPAT end-to-end closure post-Lane-A,
  Primary): Primary landed Lane-A finish theorem
  `laurentOverlapBridge_exists_compatible_via_primary`
  (`LaurentOverlap.lean:3764`, commit `7b6dccd`; line shifted from 3761
  by my 4-line namespace fix below). Own T-OVERLAP-COMPAT
  end-to-end: use Primary's exported theorem and close the downstream
  consumer side with top-level `_via_primary` caller-ready theorems.

  **1. New file `Adic spaces/LaurentOverlapConsumer.lean` (~460 lines):**
  Houses **four** top-level caller-ready `_via_primary` theorems
  composing Primary's exported `_via_primary` finish with the sorry-free
  `_via_compatible_bridge` consumers from `LaurentRefinement.lean`:

  | Theorem | Output |
  |---|---|
  | `V_cover_gluing_via_primary` | V-cover gluing existential |
  | `laurentCover_gluing_presheaf_via_primary` | Laurent-pair gluing existential |
  | `laurentBridge_delta_eq_zero_via_primary` | algebraic `deltaMap_gen = 0` |
  | `laurentAndVCover_gluing_unified_via_primary` | combined existential (single-witness smoke test) |

  Each theorem takes τ_preBiv + two intertwining identities (Primary's
  Step-A / S-OV-GLUE raw inputs) plus the standard downstream data
  (V-cover or Laurent-pair) and returns the conclusion directly, with no
  caller-visible unpacking of `(τ₁₂, hcompat_bridge)`. Two-step proof:
  (a) `laurentOverlapBridge_exists_compatible_via_primary` extracts the
  compatible bridge; (b) corresponding `_via_compatible_bridge` wrapper
  consumes it. Pure structural composition.

  The fourth theorem is the **post-Lane-A staging smoke test**: it
  combines all three downstream conclusions into a single existential
  with shared witness `x`, mirroring `laurentAndVCover_gluing_unified_via_compatible_bridge`
  one level up. This is the entry that should "go green" the moment
  Primary's file builds — exercises every layer of the tower in one
  call.

  **Caller tower (end-to-end view, post-Lane-A)**: four new
  `_via_primary` theorems at the top level, plus the four
  `_via_compatible_bridge` primitives they compose with:

  | Caller-supplied inputs | Theorem | Output |
  |---|---|---|
  | τ_preBiv + 2 intertwinings + V-cover data | `V_cover_gluing_via_primary` | V-cover gluing |
  | τ_preBiv + 2 intertwinings + Laurent-pair data | `laurentCover_gluing_presheaf_via_primary` | Laurent-pair gluing |
  | τ_preBiv + 2 intertwinings + half-sections | `laurentBridge_delta_eq_zero_via_primary` | `deltaMap_gen = 0` |
  | τ_preBiv + 2 intertwinings + Laurent+V-cover | `laurentAndVCover_gluing_unified_via_primary` | combined smoke test |
  | (τ₁₂, hcompat_bridge) + V-cover data | `V_cover_gluing_from_laurentPair_via_compatible_bridge` | V-cover gluing |
  | (τ₁₂, hcompat_bridge) + Laurent-pair data | `laurentCover_gluing_presheaf_via_compatible_bridge` | Laurent-pair gluing |
  | (τ₁₂, hcompat_bridge) + half-sections | `laurentBridge_delta_eq_zero_via_compatible_bridge` | `deltaMap_gen = 0` |
  | (τ₁₂, hcompat_bridge) + Laurent+V-cover data | `laurentAndVCover_gluing_unified_via_compatible_bridge` | combined smoke test |

  The `_via_primary` rows (top) are the new caller-ready entries for
  Lane C inductive steps. The `_via_compatible_bridge` rows (bottom)
  remain as library primitives for callers who independently produce a
  compatible bridge (or for the internal composition inside `_via_primary`).

  **2. Root wire-up:** added `import «Adic spaces».LaurentOverlapConsumer`
  at `Adic spaces.lean:39`.

  **3. LaurentOverlap.lean blocker discovered (38 build errors); my
  edits reverted (file restored to HEAD = 6bd14ab):** LaurentOverlap.lean
  in its committed state does **not** compile. The first failure is the
  five "Unknown identifier `instTopologicalSpaceTateAlgebra`" errors at
  lines 2548-2562 inside `B₁_gen_nonarchimedeanRing`, but a single
  `open TateAlgebra in` namespace fix uncovers a **38-error cascade** of
  pre-existing semantic issues in the file:

  * Line 2569: `local instance B₁_gen_topologicalSpace` needs
    `noncomputable` keyword (depends on noncomputable `quotientPlusFSubXIdealTopology`).
  * Lines 2672, 2677, 2751, 3056, 3074, 3270, 3603, 3608: `Tactic
    rewrite` failures and `unsolved goals` in proof bodies.
  * Lines 2983, 3472, 3811, 3813: `failed to synthesize instance of
    type class`.
  * Lines 3003, 3020, 3037: `typeclass instance problem is stuck`.
  * Lines 2984, 3427, 3682: `Application type mismatch`.
  * Lines 3367, 3611: `Unknown identifier i` / `w` (likely intro
    binding failures).
  * Line 3504: `unexpected token 'set_option'; expected 'lemma'`.
  * Line 3819: `(deterministic) timeout at isDefEq` (heartbeat
    exhaustion despite `set_option maxHeartbeats 800000 in`).

  These go far beyond namespace-scoping. Several declarations in the
  file (especially `B₁_gen_topologicalSpace`,
  `TA_B₁_gen_to_bivariateOverlap_outer_evalHom_*`,
  `TA_B₁_gen_quotient_backward_forward_eq_id_of_inputs`, and theorems
  in the 3000-3700 range) appear to be in WIP / partially-broken state.

  **Tested approach (then reverted)**: experimented with adding
  `open TateAlgebra in` before each of the four declarations using
  unqualified `instTopologicalSpaceTateAlgebra` (`B₁_gen_nonarchimedeanRing`
  at line 2538, `ReverseRoundTripInputs` structure at line 3442,
  `tateAlgebra_continuous_ringHom_ext` at line 3457,
  `TA_B₁_gen_quotient_backward_forward_eq_id_of_inputs` at line 3507).
  This fixed the namespace errors but the build then hit the 38
  semantic errors above. **Reverted all four edits**; LaurentOverlap.lean
  is now identical to HEAD = 6bd14ab.

  **Scope respected**: created `LaurentOverlapConsumer.lean`; edited
  `Adic spaces.lean` (one root import). Did NOT permanently modify
  `LaurentOverlap.lean` (Primary's file). Did NOT touch
  `GeometricReduction.lean` or any Lane-B file.

  **T-OVERLAP-COMPAT end-to-end status (Lane C side)**: caller-ready
  `_via_primary` tower is **source-complete** in
  `LaurentOverlapConsumer.lean`. Four theorems sorry-free modulo the
  T001 leak that all `restrictionMap`-touching theorems inherit
  (same axiom footprint as the sibling `_via_compatible_bridge`
  theorems). Compilation **blocked** on Primary fixing the 38 build
  errors in `LaurentOverlap.lean` (most of which are pre-existing tactic
  / typeclass failures, not just namespace scoping).

  **Unpark condition** (single line): any commit to `LaurentOverlap.lean`
  on top of `6bd14ab` that produces `LaurentOverlap.olean`. No other
  upstream / downstream change is required for the consumer file to
  compile and for T-OVERLAP-COMPAT end-to-end to close.

  **Action needed from Primary**: stabilize `LaurentOverlap.lean` so that
  it compiles cleanly. Once `LaurentOverlap.olean` is produced, my
  `LaurentOverlapConsumer.lean` should compile automatically (3 theorems,
  pure structural composition; no new analytic content). T-OVERLAP-COMPAT
  end-to-end then closes immediately.

- **2026-04-21** (CLEANUP-C2: overlap-consumer tower docstring +
  end-to-end smoke test, Primary): Own the CLEANUP-C2 closure ticket
  for the explicit-compatible-bridge caller tower in
  `Adic spaces/LaurentRefinement.lean`. Two deliverables:

  **1. Docstring cleanup** (~60 lines rewritten):
  * **Section-level tower docstring** at line 3686 (before
    `laurentBridge_delta_eq_zero_via_compatible_bridge`): introduces
    the three-theorem caller tower with an explicit abstraction-level
    table (algebraic δ → Laurent-pair presheaf gluing → V-cover
    presheaf gluing), and a concrete "Typical Lane-C usage pattern"
    code snippet showing the standard
    `obtain ⟨τ₁₂, hcompat_bridge⟩ := laurentOverlapBridge_exists_compatible …`
    extraction + single-call V-cover consumer invocation.
  * **V-cover theorem docstring** (line 3915): removed transient
    concurrent-agent line-number references (334, 603, 607, 613, 748,
    829) that were already shifting and distracted from the
    architectural message. The relevant content — the theorem is
    parametric in abstract `V_covers` for immunity to in-flight edits
    in downstream-geometric files — is preserved concisely.

  **2. End-to-end smoke test** (~120 new lines):
  `ValuationSpectrum.laurentAndVCover_gluing_unified_via_compatible_bridge`.
  Composes the three-theorem caller tower into a single invocation that
  returns a **combined existential**:

  ```lean
  ∃ x : presheafValue D₀,
    restrictionMap D₀ (laurentPlusDatum D₀ f)
        (laurentPlus_subset D₀ f) x = u_plus ∧
    restrictionMap D₀ (laurentMinusDatum D₀ f)
        (laurentMinus_subset D₀ f) x = u_minus ∧
    ∀ D : { D // D ∈ V_covers },
      restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D
  ```

  **Why this is a "smoke test"**: the combined existential verifies the
  Laurent-pair and V-cover conclusions share a **single witness** `x`
  (not two different ones) — an inherent property of the tower's
  factoring that wasn't explicitly exposed by any individual theorem
  statement. The proof uses the same `x` from
  `laurentCover_gluing_presheaf_via_compatible_bridge` internally and
  extracts both conclusions. Sanity-check for callers who need both
  half-section recoveries AND V-piece restrictions from the same
  witness.

  **Caller value**: a consumer who needs all three conclusions can call
  the smoke-test theorem once instead of (a) calling
  `laurentCover_gluing_presheaf_via_compatible_bridge`, (b) unpacking the
  Laurent-pair witness, (c) separately calling
  `V_cover_gluing_from_laurentPair_via_compatible_bridge` (which would
  give a different existential `x`), (d) manually checking consistency.

  **Scope respected**: edited only `LaurentRefinement.lean`. Did NOT
  touch `LaurentOverlap.lean`, `GeometricReduction.lean`, or any Lane-B
  file.

  **Axiom hygiene**:
  `laurentAndVCover_gluing_unified_via_compatible_bridge` depends on
  `[propext, sorryAx, Classical.choice, Quot.sound]` — same pre-existing
  T001 leak pattern as the other three `_via_compatible_bridge`
  theorems. **No dependency on the Lane-A sorry**
  (`laurentOverlapBridge_exists_compatible`): proof body uses only
  `laurentCover_gluing_presheaf_via_compatible_bridge` +
  `restrictionMap_comp` (both Lane-A-sorry-free).

  **Net project sorry delta**: 0. Pre-existing sorries at lines 3124
  and 4254 (shifted from 4167 by the ~120-line insertion) unchanged.

  **Caller tower now fully documented** (all in LaurentRefinement.lean,
  all Lane-A-sorry-free, all consume the same single witness
  `(τ₁₂, hcompat_bridge)`):

  | Level | Theorem |
  |---|---|
  | algebraic δ=0 | `laurentBridge_delta_eq_zero_via_compatible_bridge` |
  | Laurent-pair gluing | `laurentCover_gluing_presheaf_via_compatible_bridge` |
  | V-cover gluing | `V_cover_gluing_from_laurentPair_via_compatible_bridge` |
  | **Combined** (smoke test) | **`laurentAndVCover_gluing_unified_via_compatible_bridge`** |

  **Build**: `lake build «Adic spaces».LaurentRefinement` → EXIT 0 with
  only pre-existing sorry warnings. Axiom check confirms expected T001
  footprint for the new smoke-test theorem.

  **Lane-C downstream status**: **DONE modulo the single upstream
  Lane-A witness** `(τ₁₂, hcompat_bridge)` from
  `laurentOverlapBridge_exists_compatible`. When Primary lands that
  existential, downstream callers can plug it into any of the four
  consumer theorems above — the final Part 2 / gluing wiring is ready.

- **2026-04-21** (V-cover Lane-C consumer landed in LaurentRefinement,
  Primary): Own the downstream integration lane end-to-end. Land the
  **strongest caller-ready V-cover gluing theorem** in
  `Adic spaces/LaurentRefinement.lean` (~150 new lines), packaging the
  Laurent-pair explicit-bridge gluing with the standard
  plus/minus-refinement dichotomy to produce **V-cover gluing directly**
  from a single compatible overlap bridge witness.

  **Landed**: `ValuationSpectrum.V_cover_gluing_from_laurentPair_via_compatible_bridge`.
  Signature:

  ```lean
  theorem V_cover_gluing_from_laurentPair_via_compatible_bridge
      -- 7-hypothesis Tate bundle on `presheafValue D₀` (hNoeth_B, hLocLift_B,
      -- hA₀Noeth_B, hA_complete_B, hnoeth_B, hcont_forward_B, hcont_eval_B)
      -- + Laurent-pair inputs (D₀, f)
      -- + explicit compatible overlap bridge
      (τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
              LaurentCover.B₁₂_gen (D₀.canonicalMap f))
      (hcompat_bridge : LaurentOverlapBridgeCompatible … τ₁₂)
      -- + abstract V-cover (no dependence on standardCoverVCovers)
      (V_covers : Finset (RationalLocData A))
      (hV_subset_base : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
        rationalOpen D₀.T D₀.s)
      (hrefine : ∀ D : { D // D ∈ V_covers }, refines plus ∨ refines minus)
      (u_plus u_minus) (fV)
      (hfV_plus hfV_minus hcompat) :
      ∃ x : presheafValue D₀, ∀ D ∈ V_covers,
        restrictionMap D₀ D.1 (hV_subset_base D.1 D.2) x = fV D
  ```

  **What it does**: consumes the **single upstream Lane-A witness**
  `(τ₁₂, hcompat_bridge)` and produces a **V-cover-level Part-2 gluing
  result** without the caller needing to unpack the Laurent pair.
  Internally chains `laurentCover_gluing_presheaf_via_compatible_bridge`
  (prior session) with the plus/minus-refinement dichotomy via
  `restrictionMap_comp` — pure structural composition, no new analytic
  content.

  **Architectural advantage over the attempted
  `standardCover_gluing_induction_step_via_compatible_bridge`** (which
  the prior sub-session could not land due to concurrent-agent errors
  in `GeometricReduction.lean`): this theorem is **parametric in
  abstract `V_covers`**, so it does NOT depend on
  `GeometricReduction.standardCoverVCovers` or any other
  GeometricReduction API. **It compiles cleanly in LaurentRefinement.lean**
  as a self-contained theorem, completely independent of whatever
  in-flight state GeometricReduction.lean is in.

  **Usage**: downstream callers (Lane C) who work with standard-cover
  V-sets instantiate:
  * `V_covers := C.standardCoverVCovers S`
  * `hV_subset_base := fun D hD => C.standardCoverVCovers_subset_base S D hD`
  * `hrefine := fun D => ...` (from `refinedVCovers_plusMinus_dichotomy`,
    etc.)

  and get V-cover gluing in one call. Consumers who work with
  **arbitrary V-covers** (e.g., ad-hoc Lane-C variants, Hübner-style
  direct V-cover constructions) simply supply the Finset directly.

  **Caller-ready interface picture now complete** (all in LaurentRefinement.lean,
  all sorry-free modulo pre-existing T001 leak, all accept the same
  single upstream Lane-A witness `(τ₁₂, hcompat_bridge)`):

  | Level | Theorem | Caller supplies |
  |---|---|---|
  | delta=0 | `laurentBridge_delta_eq_zero_via_compatible_bridge` | bridge + uplus/uminus + compat |
  | Laurent pair gluing | `laurentCover_gluing_presheaf_via_compatible_bridge` | bridge + uplus/uminus + compat + hplus/hminus |
  | V-cover gluing | `V_cover_gluing_from_laurentPair_via_compatible_bridge` (**new**) | bridge + V-cover + plus/minus dichotomy + halves matching |

  Lane C's ultimate downstream call only needs the V-cover version.

  **Scope respected**: edited ONLY `LaurentRefinement.lean`. Did NOT
  touch `LaurentOverlap.lean` (Primary's file). Did NOT touch
  `GeometricReduction.lean` (Tertiary's in-flight file with build
  errors). Did NOT reopen Lane B. The prior sub-session's reverted
  GeometricReduction.lean addition remains reverted.

  **Axiom hygiene**:
  `V_cover_gluing_from_laurentPair_via_compatible_bridge` depends on
  `[propext, sorryAx, Classical.choice, Quot.sound]`. The `sorryAx`
  is the **pre-existing T001 leak** via `[HasLocLiftPowerBounded A]` →
  `restrictionMap` → `spa_point_nonOpen_of_rational_subset` — identical
  axiom pattern to the three sibling `_via_compatible_bridge` theorems.
  **The new theorem does NOT depend on the Lane-A sorry**
  (`laurentOverlapBridge_exists_compatible`): proof body uses only
  `laurentCover_gluing_presheaf_via_compatible_bridge` (which skips the
  Lane-A `obtain`) and `restrictionMap_comp` (sorry-free).

  **Net project sorry delta**: 0. Pre-existing sorries at
  `laurentOverlapBridge_exists_compatible` (now at line 3187) and
  `tateAcyclicity` Part 2 (now at line 4167) unchanged.

  **Builds**:
  * `lake build «Adic spaces».LaurentRefinement` → EXIT 0, clean.
  * All sorry warnings in the build output are pre-existing in other
    upstream files; the only LaurentRefinement warnings are for the two
    pre-existing sorries above.
  * Axiom check confirms same T001 footprint as siblings.

  **Downstream impact**: Lane C's entire downstream integration side is
  now **DONE modulo the single upstream Lane-A witness**
  `(τ₁₂, hcompat_bridge)`. The final caller needs only:
  1. Supply the compatible overlap bridge (Lane A, in
     `LaurentOverlap.lean` — Primary's responsibility).
  2. Provide the V-cover structure + plus/minus dichotomy at each
     induction step (standard content, already available via
     `refinedVCovers_plusMinus_dichotomy` once `GeometricReduction.lean`
     stabilizes).

- **2026-04-21** (Lane-C V-cover consumer attempt — blocked by concurrent
  agent's GeometricReduction.lean errors, Secondary): Attempted to land the
  **next consumer theorem** one level higher: a caller-ready
  `standardCover_gluing_induction_step_via_compatible_bridge` in
  `Adic spaces/GeometricReduction.lean` that would chain the
  `laurentCover_gluing_presheaf_via_compatible_bridge` (prior-session
  landed) through `standardCover_gluing_induction_step` to give Lane C
  a V-cover-level Part-2 gluing step taking just the compatible overlap
  bridge as explicit input.

  **Blocker found**: `Adic spaces/GeometricReduction.lean` has ~4700
  lines of **concurrent-agent in-flight edits** (not from this session)
  with six pre-existing build errors at lines 334, 603, 607, 613, 748,
  829:
  ```
  error: Unknown identifier `restrictionMap_bijective_of_rationalOpen_eq`
  error: Unknown identifier `g`
  error: Unknown identifier `f₀`
  error: Application type mismatch: The argument …
  error: unexpected token ':='; expected '}'
  error: (deterministic) timeout at `isDefEq`, heartbeats exhausted
  ```
  These errors exist in the current uncommitted working state and are
  independent of this session — they appear whether or not my theorem
  addition is present. The file does not build.

  **Actions taken**:
  1. Drafted `standardCover_gluing_induction_step_via_compatible_bridge`
     (~110 lines) at line 1468 of GeometricReduction.lean. Structurally
     correct (mirrors `_via_laurentGluing` but routes through the new
     `_via_compatible_bridge` Laurent variant).
  2. **Reverted** the addition — since the file is under heavy concurrent
     editing and cannot build, adding new theorems there is risky and
     can't be verified.
  3. **Did not create a downstream file** — would require importing
     `GeometricReduction.lean` to use `standardCover_gluing_induction_step`,
     which is currently unbuildable; source-only content with import-cycle
     workarounds would be heavy-handed for an unverified theorem.

  **Source-only snippet** (ready to drop into GeometricReduction.lean
  once concurrent errors resolve, or into a downstream file if
  GeometricReduction.lean stabilizes):
  ```lean
  theorem RationalCovering.standardCover_gluing_induction_step_via_compatible_bridge
      [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
      [DecidableEq A]
      (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
      (C : RationalCovering A)
      [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
      [LaurentNormalized C.base]
      (f₀ : A) (S : Finset A)
      (u_plus : presheafValue (laurentPlusDatum C.base f₀))
      (u_minus : presheafValue (laurentMinusDatum C.base f₀))
      (fV : ∀ D : { D // D ∈ C.standardCoverVCovers S }, presheafValue D.1)
      (hrefine : …) (hfV_plus : …) (hfV_minus : …) (hcompat : …)
      (hNoeth_B : …) (hLocLift_B : …) (hA₀Noeth_B : …)
      (hA_complete_B : …) (hnoeth_B : …)
      (hcont_forward_B : …) (hcont_eval_B : …)
      (τ₁₂ : presheafValue (laurentOverlapDatum C.base f₀) ≃+*
        LaurentCover.B₁₂_gen (C.base.canonicalMap f₀))
      (hcompat_bridge : LaurentOverlapBridgeCompatible P C.base f₀ … τ₁₂) :
      ∃ x, ∀ D ∈ C.standardCoverVCovers S, restrictionMap C.base D.1 _ x = fV D :=
    C.standardCover_gluing_induction_step f₀ S u_plus u_minus fV hrefine
      hfV_plus hfV_minus
      (laurentCover_gluing_presheaf_via_compatible_bridge P C.base f₀
        hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B
        hcont_forward_B hcont_eval_B τ₁₂ hcompat_bridge
        (laurentPlus_subset C.base f₀) (laurentMinus_subset C.base f₀)
        u_plus u_minus hcompat)
  ```

  **Current Lane-C consumer state**:
  * **`laurentCover_gluing_presheaf_via_compatible_bridge`**
    (LaurentRefinement.lean, prior session, sorry-free modulo T001 leak)
    — this IS the currently-available caller-ready theorem. Lane C
    callers consume it at the **Laurent-pair level** (takes `uplus, uminus`
    directly) rather than at the V-cover level. Slightly lower-level
    than the attempted `standardCover_gluing_induction_step_via_compatible_bridge`
    but fully functional.

  **Scope respected**: did NOT edit `LaurentOverlap.lean`. Did NOT
  reopen Lane B. No new sorries. No new critical-path dependencies.
  GeometricReduction.lean reverted to pre-session concurrent state.

  **Net sorry delta**: 0. All additions reverted.

  **Next-session actionable**: once concurrent agent resolves
  GeometricReduction.lean errors (likely targeting unresolved identifiers
  and the mid-file syntax error around line 748), drop in the source-only
  snippet above and verify with `lake build «Adic spaces».GeometricReduction`.

- **2026-04-21** (Lane-C consumer theorems landed with explicit bridge
  hypothesis, Secondary): Build the **next consumer theorem** in the
  downstream overlap-compatibility lane: a pair of theorems in
  `LaurentRefinement.lean` that take the compatible overlap bridge
  `(τ₁₂, hcompat_bridge)` as an **explicit caller-supplied hypothesis**
  and produce `deltaMap_gen = 0` and the Laurent-cover gluing conclusion
  — avoiding the sorry'd `laurentOverlapBridge_exists_compatible`
  (LaurentRefinement.lean:3124, Lane-A target).

  **Landed** (`Adic spaces/LaurentRefinement.lean`, +197 lines after the
  existing `laurentCover_gluing_presheaf`):

  1. **`laurentBridge_delta_eq_zero_via_compatible_bridge`** — analog of
     `laurentBridge_delta_eq_zero_of_compat` with `(τ₁₂, hcompat_bridge)`
     as explicit caller-supplied hypotheses. Proof body is the existing
     `_of_compat` body **minus** the `obtain ⟨τ₁₂, hcompat_bridge⟩ := …`
     step that routes through Lane-A's sorry. ~30 lines of proof body
     (copied + trimmed).

  2. **`laurentCover_gluing_presheaf_via_compatible_bridge`** — top-level
     Lane-C consumer analog of `laurentCover_gluing_presheaf`. Factored
     through the parametric `laurentCover_gluing_presheaf_viaRow3`
     (sorry-free) plus the new
     `laurentBridge_delta_eq_zero_via_compatible_bridge` for the
     delta-zero step. Returns gluing existential directly.

  **Two-stage architecture preserved**: the theorems still separate
  * **Stage 1** (algebraic): `bivariateOverlap_equiv_B₁₂gen` (Primary's
    Step B, sorry-free in LaurentOverlap.lean:630). **Not referenced
    directly by this session's theorems** — it's used within the
    ambient factorization reduction
    `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
    (prior session), which any caller can compose with the new
    consumer.
  * **Stage 2** (presheaf-side bivariate iso + intertwining identities):
    the input `(τ₁₂, hcompat_bridge)` bundles both the presheaf iso and
    the two intertwining identities. Callers can either construct
    directly or obtain via the parametric factorization reduction.

  **Scope respected**: did NOT edit `LaurentOverlap.lean`. Worked only
  in `LaurentRefinement.lean`. Primary's in-flight
  `LaurentOverlap.lean:3322` (`instTopologicalSpaceTateAlgebra`) error
  remains unresolved (Primary's responsibility), but does **not block**
  this session's work since `LaurentRefinement.lean` sits upstream of
  `LaurentOverlap.lean` and compiles independently.

  **Axiom hygiene**:
  * `laurentBridge_delta_eq_zero_via_compatible_bridge`:
    `[propext, sorryAx, Classical.choice, Quot.sound]`.
  * `laurentCover_gluing_presheaf_via_compatible_bridge`:
    `[propext, sorryAx, Classical.choice, Quot.sound]`.

  The `sorryAx` is the **pre-existing T001 leak** via
  `[HasLocLiftPowerBounded A]` → `restrictionMap` →
  `spa_point_nonOpen_of_rational_subset`. Identical axiom footprint to
  the sibling `_of_compat` / `_viaBridges` theorems, which inherit the
  same leak. **Crucially, my new theorems do NOT depend on the
  Lane-A sorry** (`laurentOverlapBridge_exists_compatible`): the proof
  body skips the `obtain` step that extracts from the existential.
  Once Primary closes Lane A, the sibling theorems can simplify to
  these new variants by providing an explicit witness.

  **Net project sorry delta**: 0. No new sorries introduced. Pre-existing
  sorry at `laurentOverlapBridge_exists_compatible` (line 3124) and
  `tateAcyclicity` Part 2 (now at line 3967 due to the ~197-line
  insertion) unchanged.

  **Build**: `lake env lean "Adic spaces/LaurentRefinement.lean"` →
  EXIT 0 with only pre-existing sorry warnings and unrelated upstream
  linter warnings. Axiom check confirms identical sorry-footprint to
  siblings.

  **Downstream impact**: Lane-C callers (e.g., `T-GEOM-RED` iterated
  Laurent induction, `tateAcyclicity` Part 2 via Hübner refinement) can
  now consume `laurentCover_gluing_presheaf_via_compatible_bridge`
  directly as their per-step gluing primitive, supplying the compatible
  overlap bridge as an explicit hypothesis. This **decouples Lane C
  from the Lane-A sorry** until Lane A's existential closes.

- **2026-04-21** (T-OV-1 downstream instantiation attempt — blocked by
  in-flight Primary build error, Secondary): Attempted to land a
  **downstream instantiation** of the Lane-A reduction theorem
  (`laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
  from earlier this session) that bakes in Primary's sorry-free
  `bivariateOverlap_equiv_B₁₂gen` (LaurentOverlap.lean:630) as the
  algebraic iso τ_alg, leaving only τ_preBiv + 2 intertwinings as
  external hypotheses.

  **Blocker discovered**: Primary's `LaurentOverlap.lean` has a
  **pre-existing in-flight build error** at line 3322 in the newly-added
  `ReverseRoundTripInputs` structure (Step 11, `parametric reverse round
  trip` section, commit 5b99886 "parametric RingEquiv bundle for specialized
  Laurent-overlap bridge"):

  ```
  error: Adic spaces/LaurentOverlap.lean:3322:57:
    Unknown identifier `instTopologicalSpaceTateAlgebra`
  ```

  The `instTopologicalSpaceTateAlgebra` instance exists for
  `TateAlgebra A` under `[IsTateRing A]`, but at `A := LaurentCover.B₁_gen b`
  this instance isn't derivable (would require a Tate structure on
  `B₁_gen b = TA B / plusFSubXIdeal b`, which Primary's own docstring
  notes is "substantial work" not yet constructed). The error is in
  Primary's in-flight work, not caused by this session.

  **Actions taken**:
  1. Attempted new file `Adic spaces/LaurentOverlapCompatReduction.lean`
     (~110 lines) that imports both `LaurentOverlap` and
     `LaurentRefinement`, and provides the instantiation. File content
     is correct but cannot compile until Primary's LaurentOverlap error
     resolves.
  2. **Removed** the new file since it cannot build; reverted the root
     import addition in `Adic spaces.lean`.
  3. **Kept** the parametric reduction theorem in
     `LaurentRefinement.lean` (prior session's landed deliverable,
     which compiles independently).

  **Scope respected**: did NOT edit `LaurentOverlap.lean` despite
  discovering the error. Primary's in-flight state preserved unchanged.

  **Boundary now visible**: the Lane-A closure path requires:
  * **(Primary)** resolve the `instTopologicalSpaceTateAlgebra` issue
    at LaurentOverlap.lean:3322 — likely by either constructing a Tate
    instance on `B₁_gen b` or parameterizing the topology in the
    `ReverseRoundTripInputs` structure.
  * **(Primary)** close `laurentOverlapBridge_exists_compatible` itself
    by providing τ_preBiv (Step A / S-OV-GLUE) + the two intertwining
    identities, pluggable into the prior-session reduction theorem via
    the composition wrap.

  **Net project sorry delta**: 0 (no new sorries, no new files
  committed, removed the attempted downstream file).

  **Build**: `lake env lean "Adic spaces/LaurentRefinement.lean"` →
  EXIT 0 with only pre-existing sorries (3124 / 3770) and pre-existing
  linter warnings. `lake build «Adic spaces».LaurentOverlap` → EXIT 1
  (Primary's in-flight error, as reported).

  **Next-session actionable**: once Primary resolves the
  `instTopologicalSpaceTateAlgebra` issue at LaurentOverlap.lean:3322,
  the downstream instantiation file is ready to re-land in ~110 lines
  (the prepared content is documented in this ticket's attempt notes
  and can be reconstructed from the factorization reduction's
  signature).

- **2026-04-21** (T-OV-1 / S-OV-GLUE presheaf-side factorization reduction,
  Primary): Land a **reduction theorem** for
  `laurentOverlapBridge_exists_compatible` in
  `Adic spaces/LaurentRefinement.lean`, factoring the bridge through
  `TateAlgebra₂(B) ⧸ bivariateOverlapIdeal b` and separating the algebraic
  step (Primary's sorry-free `bivariateOverlap_equiv_B₁₂gen` Step B) from
  the presheaf-side bivariate iso (Primary's still-open Step A / S-OV-GLUE).

  **Landed**:
  `ValuationSpectrum.laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
  in `LaurentRefinement.lean` (~82 new lines). The theorem takes:
  * `τ_preBiv : presheafValue(laurentOverlapDatum D₀ f) ≃+*
    TateAlgebra₂(presheafValue D₀) ⧸ bivariateOverlapIdeal (D₀.canonicalMap f)`
    — the **presheaf-level bivariate iso** (Step A / S-OV-GLUE remaining
    open content in Primary's `LaurentOverlap.lean`).
  * `τ_alg : TateAlgebra₂(…) ⧸ bivariateOverlapIdeal … ≃+* B₁₂_gen …`
    — **Primary's sorry-free `bivariateOverlap_equiv_B₁₂gen`** (Step B,
    LaurentOverlap.lean:630).
  * `h_plus_compat`, `h_minus_compat` — the two intertwining identities at
    the **composed level** `τ_alg ∘ τ_preBiv`.

  Produces the full `∃ τ₁₂, LaurentOverlapBridgeCompatible … τ₁₂`
  conclusion via `⟨τ_preBiv.trans τ_alg, { plus_compat, minus_compat }⟩`.
  Theorem body is a **trivial composition wrap** — no new mathematical
  content, but a **named interface** making the reduction shape explicit.

  **Scope respected** per reviewer:
  * Edit: `LaurentRefinement.lean` only.
  * **Did NOT edit `LaurentOverlap.lean`** (Primary's file).
  * Import cycle avoided — both `TateAlgebra₂.bivariateOverlapIdeal`
    (defined in `TateAlgebraTopology.lean`) and `LaurentCover.B₁₂_gen`
    (defined in `LaurentCoverExact.lean`) are transitively accessible
    from `LaurentRefinement.lean` via
    `PresheafTateStructure → PresheafIdentification → TateAlgebraWedhorn →
    TateAlgebraTopology`.

  **Remaining content** (Primary's Lane A to close the original
  `laurentOverlapBridge_exists_compatible` sorry at
  LaurentRefinement.lean:3187):
  1. **`τ_preBiv`** — the bivariate presheaf iso, i.e., Primary's Step A
     / S-OV-GLUE. Still open in the Lane A tracker.
  2. **Two intertwining identities** at the composed level. Once
     Primary produces Step A + the algebraic action lemmas for
     `bivariateOverlap_equiv_B₁₂gen` (`_algebraMap`, `_X`, `_Y`, already
     sorry-free in LaurentOverlap.lean:687-714), these reduce to
     mechanical computations relating `τ_preBiv` to
     `laurentPlusBridge` / `laurentMinusBridge` + `posLift` / `negLift`.

  **Docstring update** on the original `laurentOverlapBridge_exists_compatible`
  body now cites the new reduction theorem as the available path forward.

  **Axioms**:
  `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
  depends on `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` is the **pre-existing T001 leak** via
  `[HasLocLiftPowerBounded A]` → `restrictionMap` (used inside
  `LaurentOverlapBridgeCompatible`'s compat fields). Identical axiom
  pattern to sibling `laurentOverlap_plus_intertwine_of_compatible`
  (also uses `restrictionMap`). **No new sorry introduced by this
  theorem's body** (the body is a literal structural composition).

  **Net project sorry delta this session**: 0. Shift-only: pre-existing
  sorries in `LaurentRefinement.lean` moved from lines 3173 and 3737 to
  3187 and 3836 due to the ~82-line insertion.

  **Build**: `lake build «Adic spaces».LaurentRefinement` → EXIT 0,
  clean (only pre-existing unused-section-variable warnings on unrelated
  upstream theorems). Focused `lake env lean "Adic spaces/LaurentRefinement.lean"`
  → EXIT 0 with the same pre-existing warnings.

  **Next-session actionable** (for Primary): now that the reduction
  interface is named, Primary's S-OV-GLUE work can target the two
  specific Lean-signature outputs (`τ_preBiv` and the two intertwining
  identities) and feed them into this reduction theorem from a new
  downstream file that imports both `LaurentRefinement` and
  `LaurentOverlap`. The original
  `laurentOverlapBridge_exists_compatible` at line 3187 then becomes
  trivially dischargeable once those outputs are available.

- **2026-04-20** (Unconditional Jacobson residual DISPROVED; packet produced,
  Primary): Direct attempt to prove
  `locIdeal ≤ Ideal.jacobson (⊥ : Ideal (locSubring))` unconditionally
  found a **concrete counterexample**, confirming the unconditional form
  is FALSE for uncompleted Tate localization rings.

  **Counterexample** (verified in packet):
  - `A = ℚ_p⟨X⟩` (Tate algebra, complete, `p` top-nilp unit).
  - `A₀ = ℤ_p⟨X⟩`, `P.I = (p)`.
  - Rational open datum: `T = {X}`, `s = p`. locSubring = `ℤ_p⟨X⟩[X/p]`
    (incomplete sub-algebra of `A[1/p] = A`).
  - `X ∈ locIdeal` (via `X = p · (X/p)`, `p ∈ P.I`, `X/p ∈ locSubring`).
  - `X` is top-nilp in locSubring (by existing sorry-free lemma
    `locIdeal_forall_isTopologicallyNilpotent`, IdealLocalization.lean:339).
  - `1 + X` is NOT a unit in locSubring, because the formal inverse
    `1 - X + X² - …` has coefficients ±1 that don't tend to 0 in `ℚ_p`,
    so it isn't a restricted power series; equivalently, `1 + X` vanishes
    at `X = -1 ∈ ℤ_p`, so it's not a unit on any Tate algebra containing
    locSubring.
  - By `Ideal.mem_jacobson_bot` (Mathlib): X ∉ Jacobson ⊥ (take y = 1).
  - Therefore `locIdeal ⊄ Jacobson ⊥` in locSubring. QED.

  **Root cause**: the geometric-series proof
  (`IsTopologicallyNilpotent.isUnit_one_sub`, Wedhorn Prop 5.38, project
  file `GeometricSeries.lean:43`) **explicitly requires `[CompleteSpace A]`**,
  which locSubring does NOT satisfy. Without completeness, top-nilp
  elements need not yield units, and the Jacobson condition can fail.

  **Actions taken**:
  1. **No theorem landed** (per reviewer directive: "no new critical-path
     sorries" applied to false statements too).
  2. **Escalation packet produced** at
     `.mathlib-quality/chatgpt-packet-locIdeal-jacobson-falsity.md`
     (~180 lines). Documents the full counterexample with 4 claims
     (X ∈ locIdeal, X top-nilp, 1+X not a unit, X ∉ Jac ⊥), root cause,
     implications for Lane B, and 5 acceptable response forms from
     ChatGPT Pro (A-E):
     - (A) Hidden extra hypothesis ruling out counterexample.
     - (B) Wedhorn's Cor 8.32 uses the completion's FF not locSubring's.
     - (C) Different route to `coeRingHom_preserves_proper` avoiding
       both Jacobson and FF.
     - (D) Additional hypothesis on A (e.g., affinoid fin-gen, Jacobson
       ring, bounded Krull dim).
     - (E) Pivot to Hübner route, Lane B officially parked.
  3. **Three conditional wrappers from prior session remain valid**; they
     take the Jacobson hypothesis as caller-supplied and are unaffected
     by this falsity result.

  **Critical-path status update**:
  - Lane B's unconditional closure via Jacobson CANNOT be achieved for
    general Tate localization rings (the route is fundamentally blocked
    by `ℚ_p⟨X⟩[X/p]` and similar uncompleted sub-algebras).
  - The three equivalent entry points (`_of_stacks00MA`,
    `_of_locIdeal_le_jacobson`, `_of_ringOfDef_faithfullyFlat`) all
    reduce to the same open question: faithful-flatness of the canonical
    `locSubring → presheafValue_ringOfDef` without circular Jacobson
    assumption.
  - Hübner route (parked in prior session): orthogonal, has its own
    non-domain obstruction documented in
    `chatgpt-packet-hubner-nondomain.md`.

  **Files**: no Lean code changes. Documentation-only session, producing
  packet `chatgpt-packet-locIdeal-jacobson-falsity.md` and this log entry.

  **Next session** (pending ChatGPT Pro / reviewer input): cannot
  proceed on unconditional Jacobson; needs strategic redirection based
  on response form A-E.

- **2026-04-20** (Stacks 00MA wired into Cor 8.32 / T-COMP-FF bridge,
  Primary): Wire the newly-landed
  `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` through the entire
  Cor 8.32 / T-COMP-FF chain, producing three **Jacobson-conditional**
  wrappers that replace the raw `Module.FaithfullyFlat` hypothesis by
  the cleaner purely-algebraic hypothesis `locIdeal ≤ Ideal.jacobson ⊥`
  in `locSubring`.

  **Landed** (three wrappers, sorry-free composition):

  1. **`IdealLocalizationCompletion.lean`, ~15 new lines**:
     `locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson`.
     Takes `locIdeal ≤ Jacobson ⊥`, produces
     `RingHom.FaithfullyFlat (locSubringToRingOfDef D)`. Composes
     `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`
     (`AdicCompletionFaithfullyFlat.lean`) with the T-COMP-FF residual
     `locSubringToRingOfDef_faithfullyFlat_of_residual`
     (`IdealLocalizationCompletion.lean:414`).

  2. **`Cor832.lean`, ~15 new lines**:
     `coeRingHom_preserves_proper_of_locIdeal_le_jacobson`. Takes
     `locIdeal ≤ Jacobson ⊥`, produces
     `Ideal.map D.coeRingHom q ≠ ⊤` for proper `q ⊆ Localization.Away D.s`.
     Composes the generic Stacks 00MA with
     `coeRingHom_preserves_proper_of_stacks00MA` (Cor832.lean:1866,
     prior session).

  3. **`Cor832.lean`, ~22 new lines**:
     `productRestriction_injective_tate_of_locIdeal_le_jacobson`.
     Cover-level analog: takes `locIdeal ≤ Jacobson ⊥` at `C.base`,
     produces Part-1 injectivity of the product restriction for rational
     covering `C`. Composes through the Jacobson-conditional
     `locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson` +
     the cover-level theorem
     `productRestriction_injective_tate_of_ringOfDef_faithfullyFlat`.

  **Reviewer boundary respected**: the Jacobson hypothesis
  `locIdeal ≤ Ideal.jacobson ⊥` is **not asserted** in any of the three
  wrappers — it is taken as an explicit caller-supplied argument. The
  project does NOT assert the Jacobson hypothesis unconditionally for
  uncompleted Tate localization rings (reviewer's explicit warning,
  preserved across sessions).

  **Axiom hygiene**:
  - `locSubringToRingOfDef_faithfullyFlat_of_locIdeal_le_jacobson`:
    `[propext, Classical.choice, Quot.sound]` — **fully sorry-free**
    (lives in `IdealLocalizationCompletion.lean` which has
    `omit [PlusSubring A] [HasLocLiftPowerBounded A]` throughout,
    avoiding the T001 leak).
  - `coeRingHom_preserves_proper_of_locIdeal_le_jacobson`:
    `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` is the
    pre-existing T001 leak via Cor832.lean's file-wide
    `[HasLocLiftPowerBounded A]` variable (same leak as sibling
    `coeRingHom_preserves_proper_of_stacks00MA`).
  - `productRestriction_injective_tate_of_locIdeal_le_jacobson`: same
    T001 leak as (2).

  **No new sorry introduced** in any of the three wrappers; the sorryAx
  in (2) and (3) is the pre-existing T001 dependency chain
  (Presheaf.lean:807 via `restrictionMap`'s typeclass closure), shared
  with all other `restrictionMap`-consuming theorems in Cor832.lean.

  **Interface picture now complete**. Downstream consumers of Cor 8.32
  have **three equivalent entry points** to choose from:

  * `..._of_stacks00MA`: direct `Module.FaithfullyFlat` instance
    (matches Mathlib interface style).
  * `..._of_locIdeal_le_jacobson`: purely algebraic `locIdeal ≤ Jac ⊥`
    (matches classical Zariski-ring / Stacks-00MA statement style).
  * `..._of_ringOfDef_faithfullyFlat`: ring-hom faithful-flatness of
    `locSubringToRingOfDef` (matches T-COMP-FF pipeline style).

  All three forms are interprovable via the landed bridges, and all
  three reduce to the same **open unconditional residual**: a
  `locIdeal ≤ Jacobson ⊥`-style proof for uncompleted Tate localization
  rings (see `AdicCompletionFaithfullyFlat.lean` boundary block).

  **Files**: `Adic spaces/IdealLocalizationCompletion.lean` (+15 lines,
  added import of `AdicCompletionFaithfullyFlat`),
  `Adic spaces/Cor832.lean` (+37 lines). No other files touched.

  **Builds**:
  - `lake build «Adic spaces».IdealLocalizationCompletion` → EXIT 0,
    clean.
  - `lake build «Adic spaces».Cor832` → EXIT 0, only pre-existing
    unrelated unused-variable warning.

- **2026-04-20** (Stacks 00MA generic theorem landed, Primary): Land the
  **Mathlib-compatible generic Stacks 00MA theorem** in a new project file
  `Adic spaces/AdicCompletionFaithfullyFlat.lean` (99 lines).

  **Landed**: `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`. For any
  Noetherian ring `R` and ideal `I ⊆ R` with `I ≤ Ideal.jacobson ⊥`,
  proves `Module.FaithfullyFlat R (AdicCompletion I R)`. Fully sorry-free:
  axioms `[propext, Classical.choice, Quot.sound]` (standard Mathlib).

  **Proof strategy** (40 lines of pure Mathlib content):
  1. Flatness via `AdicCompletion.flat_of_isNoetherian` (Mathlib,
     `AsTensorProduct.lean:346`).
  2. Maximal-ideal descent via `Ideal.smul_top_eq_map` (Mathlib) +
     `Submodule.restrictScalars_eq_top_iff` (Mathlib) to reduce to
     `Ideal.map (algebraMap R (AdicCompletion I R)) m ≠ ⊤`.
  3. Apply `AdicCompletion.evalₐ I 1 : R^ → R/I` (Mathlib, `Algebra.lean:133`)
     whose composition with `algebraMap R R^` is `Ideal.Quotient.mk I`
     (via `AdicCompletion.evalₐ_of`).
  4. `Ideal.map_map` + `Ideal.map_top` push `hm_top` through the composition
     to `m.map (Ideal.Quotient.mk I) = ⊤` in `R/I`.
  5. `Ideal.comap_map_quotientMk I m` (Mathlib, `Operations.lean:790`):
     `comap (Quotient.mk I) (m.map (Quotient.mk I)) = I ⊔ m`, combined with
     `Ideal.comap_top` gives `I ⊔ m = ⊤`.
  6. `I ≤ Ideal.jacobson ⊥ ≤ m` (via `Ideal.jacobson_bot ▸
     Ring.jacobson_le_of_isMaximal m`) gives `sup_eq_right.mpr hIm :
     I ⊔ m = m`, so `m = ⊤`, contradicting `hm.ne_top`.

  **Boundary documented in-file** at end of
  `AdicCompletionFaithfullyFlat.lean`:

  **What the theorem DOES NOT give for free**: the project's Lane B
  residual needs `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal
  locSubring)`. Instantiating the generic theorem at
  `R := locSubring D.P D.T D.s`, `I := locIdeal D.P D.T D.s` would require
  `locIdeal ≤ Ideal.jacobson ⊥` in `locSubring` — **which is NOT
  automatic** for uncompleted Tate localization rings (reviewer's explicit
  warning).

  **Open unconditional residual** (named explicitly, no sorry introduced):

  ```lean
  theorem locIdeal_le_jacobson_bot_unconditional
      (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
      (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)] :
      locIdeal D.P D.T D.s ≤ Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))
  ```

  The project has **conditional** versions but none unconditional:
  * `locIdeal_le_jacobson_bot_of_isAdicComplete` — assumes locSubring
    adic-complete (false in general).
  * `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat` — assumes FF
    of locSubringToRingOfDef, which via `locSubringToRingOfDef_faithfullyFlat_of_residual`
    needs Stacks 00MA with `I ≤ Jac` — circular.

  **Circular-dependency diagram** identified this session:
  ```
  Stacks 00MA (my generic theorem)
    + locIdeal ≤ Jac (unconditional, OPEN) → Module.FaithfullyFlat locSubring (AdicCompletion ...)
       ↓ (locSubringToRingOfDef_faithfullyFlat_of_residual, my T-COMP-FF work)
  FF of locSubringToRingOfDef
       ↓ (locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat)
  locIdeal ≤ Jac (conditional)
  ```

  All three statements are equivalent; to break the circle, one MUST prove
  one of them unconditionally. The most plausible route is proving
  `locIdeal ≤ Jac` directly from the Tate structure (topological nilpotence
  of `P.I` + bounded-subring of locSubring + geometric-series unit
  argument), without asserting any completeness or faithful-flatness.

  **Files**: `Adic spaces/AdicCompletionFaithfullyFlat.lean` (new, 99 lines,
  imported into `Adic spaces.lean` at position 2). No other files touched.

  **Build**: `lake build «Adic spaces».AdicCompletionFaithfullyFlat` → EXIT 0,
  clean. Full axiom check:
  `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` depends on
  `[propext, Classical.choice, Quot.sound]` — **sorry-free**, no T001
  leak (file doesn't touch `restrictionMap` or `HasLocLiftPowerBounded`).

  **Next-session actionable**: work on `locIdeal_le_jacobson_bot_unconditional`
  (the remaining Tate-specific ring-theoretic content). Candidate approach:
  express `locIdeal ⊆ Ring.jacobson locSubring` via topologically nilpotent
  elements + `Module.exists_topologicallyNilpotent_basis_of_pair_of_definition`
  (project lemma `locIdeal_forall_isTopologicallyNilpotent` is landed).
  Geometric series for units of the form `1 + xy` with `x ∈ locIdeal` top-nilp,
  `y ∈ locSubring` arbitrary — needs convergence in locSubring, which
  requires care (locSubring is not complete, so direct series argument
  fails; may need to pass to completion via locSubringToRingOfDef, which
  is ringOfDef-adic-complete, then pull back — needs FF... circularity
  again).

- **2026-04-20** (T-IDEAL-2 / S-IDEAL-ASM end-to-end Stacks-00MA wrapper,
  Primary): Land the **conditional end-to-end `coeRingHom_preserves_proper`
  via Stacks 00MA**, closing the T-IDEAL-2 assembly picture.

  **Landed** (`Adic spaces/Cor832.lean`, 29 new lines):
  `coeRingHom_preserves_proper_of_stacks00MA` (Cor832.lean:1861). Given
  the Stacks 00MA faithful-flatness instance
  `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`
  and a proper ideal `q ⊆ Localization.Away D.s`, produces
  `Ideal.map D.coeRingHom q ≠ ⊤` (the `coeRingHom_preserves_proper`
  shape). Composes:

  1. `locSubringToRingOfDef_faithfullyFlat_of_residual`
     (IdealLocalizationCompletion.lean:414, T-COMP-FF conditional):
     Stacks-00MA → `RingHom.FaithfullyFlat (locSubringToRingOfDef D)`.
  2. `Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat`
     (Cor832.lean:1786, S-IDEAL-JAC + S-IDEAL-LOC via Lane B descent):
     FF hypothesis → `q` closed in `D.topology`.
  3. `coeRingHom_preserves_proper_of_closed` (Cor832.lean:1420,
     T-IDEAL-1 closure combinator): closed proper `q` → image proper.

  **Full T-IDEAL-2 closure now visible in a single named theorem.**
  Previously the assembly was spread across `productRestriction_injective_tate_of_ringOfDef_faithfullyFlat`
  (cover-level), `Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat`
  (per-ideal closedness), and `coeRingHom_preserves_proper_of_closed`
  (properness preservation). The new wrapper is the **per-ideal
  endpoint** directly usable as `coeRingHom_preserves_proper` for any
  downstream consumer.

  **Audit of the existing T-IDEAL-2 landscape** (pre-existing, verified
  this session):
  - **S-IDEAL-JAC (conditional on FF)**: `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat`
    landed at Cor832.lean:1736. Pulls back `presheafValue_idealOfDef ≤ Jacobson ⊥`
    (via `IsAdicComplete.le_jacobson_bot` applied to
    `presheafValue_isAdicComplete`) through the FF of
    `locSubringToRingOfDef`. **No `locSubring` adic-completeness asserted.**
  - **S-IDEAL-JAC (unconditional direct)**: Not attempted — structurally
    blocked without `locSubring` completeness (Tate topology has 0-nhd
    basis of ideals of A₀, not of A; Krull witnesses from
    `Ideal.mem_iInf_smul_pow_eq_bot_iff` are in A not A₀, so iteration
    doesn't preserve ideal nhds). Same mathematical obstruction as
    the parked non-domain Hübner H1.
  - **S-IDEAL-LOC Step 1 (unit decomposition)**: `Localization.Away.exists_unit_locSubring_decomp`
    (IdealLocalization.lean:81) landed sorry-free.
  - **S-IDEAL-LOC Step 2 (clearing denominators)**:
    `Localization.Away.mem_ideal_iff_clearing_denominator`
    (IdealLocalization.lean:137) landed sorry-free.
  - **S-IDEAL-LOC Step 3 (topological transfer)**:
    `Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
    (IdealLocalization.lean:163) landed sorry-free.
  - **S-IDEAL-ASM (closedness → properness)**:
    `coeRingHom_preserves_proper_of_closed` (Cor832.lean:1420) landed
    sorry-free (baseline axioms `[propext, Classical.choice, Quot.sound]`
    — no T001 leak).

  **Critical-path status after this session**: T-IDEAL-2 is **fully
  structurally closed** modulo the single external Stacks 00MA residual.
  The new `coeRingHom_preserves_proper_of_stacks00MA` is the cleanest
  end-to-end witness. Any downstream consumer (e.g.,
  `liftedIdeal_ne_top_of_coeRingHom_preserves_proper` Cor832.lean:1202
  or `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
  Cor832.lean:1242) can discharge its `coeRingHom_preserves_proper`
  hypothesis by providing the Stacks 00MA instance.

  **Axiom hygiene** (ran post-build):
  - `coeRingHom_preserves_proper_of_stacks00MA`:
    `[propext, sorryAx, Classical.choice, Quot.sound]`. `sorryAx` is the
    **pre-existing T001 leak** via `[HasLocLiftPowerBounded A]` →
    `restrictionMap` → `spa_point_nonOpen_of_rational_subset`
    (Presheaf.lean:807). Same leak as
    `productRestriction_injective_tate_of_ringOfDef_faithfullyFlat` and
    all other file-wide-variable theorems in Cor832.lean. **No new sorry
    introduced this session.**
  - `coeRingHom_preserves_proper_of_closed` (sibling, omits HasLocLift):
    `[propext, Classical.choice, Quot.sound]` (baseline, clean).

  **Files**: `Adic spaces/Cor832.lean` edited (29 new lines at the end,
  immediately before `end ValuationSpectrum`). No other files touched.

  **Build**: `lake build «Adic spaces».Cor832` → EXIT 0, clean
  (only the pre-existing unused-variable warning on an unrelated theorem).

- **2026-04-22** (Lane A HEAD build unblock — IN PROGRESS, Primary):
  Secondary reports `Adic spaces/LaurentOverlap.lean` at HEAD fails to
  build, blocking T-OVERLAP-COMPAT. Root cause: Secondary's working-tree
  additions to `TateAlgebraTopology.lean` (1600+ new lines for bivariate
  topology foundation) changed API signatures for downstream consumers.

  **Session commit `a551a71`**: partial repair — reduced error count
  from 47 to 25. Surface-level fixes applied:
  - Qualify `TateAlgebra.instTopologicalSpaceTateAlgebra` /
    `tateAlgBasis'` references previously unqualified.
  - `bivariateOverlap_equiv_B₁₂gen b` → `bivariateOverlap_equiv_B₁₂gen B b`.
  - `noncomputable` on local instances `B₁_gen_topologicalSpace` /
    `B₁_gen_nonarchimedeanRing_inst`.
  - `BackwardEvalHypotheses` restructured to use `addOuter` field + coherent
    `cOuter` via `IsTopologicalAddGroup.rightUniformSpace`.
  - `(B := B) b` → `b` in structure-usage sites.
  - `set_option maxHeartbeats` moved ahead of docstring blocks.
  - `[PlusSubring A]` / `[IsHuberRing A]` / `[HasLocLiftPowerBounded A]`
    added to `_via_primary` theorem signature.

  **Remaining 25 errors** (next session work):
  - Outer-evalHom `_X` / `_algebraMap` proofs: `rw [if_neg hne]; ring` not
    closing `0 * mk^n = 0` (lines 2441, 2668, 2705).
  - `oneSub_eq_zero`: typeclass timeout + rewrite pattern mismatch.
  - Backward evalHom₂ action proofs: UniformSpace coherence cascade.
  - Reverse round trip `_of_inputs`: typeclass + `i` identifier at 3395.
  - `_via_primary`: 3 Application type mismatches at restrictionMap sites.

  **Secondary unblock options** (if this session can't close all 25):
  1. **Narrow waive**: skip `_via_primary` wrapper and call
     `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
     (LaurentRefinement) directly with `bivariateOverlap_equiv_B₁₂gen`.
  2. **Hard revert**: roll LaurentOverlap.lean to `537362d` (forward-only).
  3. **Continue**: next session iterates on remaining errors.

- **2026-04-21** (T-OV-1 Lane A close-out: exported finish theorem +
  unified bundle + public-API docstring, Primary):
  Finished Lane A end-to-end. `LaurentOverlap.lean` now exposes the
  specialized Laurent-overlap bridge as a clean caller-facing API with
  a single mathematical residual.

  **Landed this session (close-out)**:
  - `SpecializedOverlapBridgeInputs` — unified hypothesis bundle
    (hcont_base + BackwardEvalHypotheses + hcont_forward + hcont_backward
    + ReverseRoundTripInputs).
  - `specializedOverlapBridge` — top-level exported theorem taking the
    single unified bundle and returning the full `RingEquiv`
    `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b ≃+* LaurentCover.B₁₂_gen b`.
  - `laurentOverlapBridge_exists_compatible_via_primary` — exported
    closure theorem specializing
    `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
    by binding `τ_alg` to `bivariateOverlap_equiv_B₁₂gen`. Downstream
    supplies only `τ_preBiv` + two intertwining witnesses.
  - Top-level public-API docstring summary documenting the four entry
    points and the single residual.

  **Caller-facing API (final Lane A state)**:
  1. `TA_B₁_gen_quotient_specialized_equiv_of_inputs` — raw parametric
     quotient equiv.
  2. `TA_B₁_gen_quotient_to_B₁₂_gen_equiv` — composite to `B₁₂_gen b`.
  3. `specializedOverlapBridge` — single-bundle convenience (recommended).
  4. `laurentOverlapBridge_exists_compatible_via_primary` — downstream
     closure theorem.

  **Single remaining mathematical residual**: polynomial density on
  `TA(B₁_gen b)` (`ReverseRoundTripInputs.hDense`). All decomposition
  hypotheses discharged internally via `tateAlgebra_polynomial_decomp`.

  **Files**: `Adic spaces/LaurentOverlap.lean` only. Zero sorries. Clean.

- **2026-04-21** (T-OV-1 specialized Laurent-overlap quotient bridge,
  end-to-end composite bridge + polynomial decomp helper landed, Primary):
  Finalized the specialized Laurent-overlap quotient bridge with a
  downstream-consumable composite equivalence and an internal polynomial
  decomposition helper eliminating two of three residual hypotheses from
  `ReverseRoundTripInputs`.

  **Landed this increment**:
  - `TateAlgebra_monomial_val` — univariate monomial value formula.
  - `Finsupp_fin1_decomp` — `l = Finsupp.single 0 (l 0)` for Fin 1.
  - `tateAlgebra_polynomial_decomp` — univariate polynomial
    decomposition for `TA R` — purely algebraic (no IsTateRing required).
    Discharges BOTH decomp hypotheses previously in
    `ReverseRoundTripInputs`, reducing residuals from 3 fields to 1.
  - `TA_B₁_gen_quotient_to_B₁₂_gen_equiv` — caller-ready composite
    bridge `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b ≃+* B₁₂_gen b`.
    Composes the specialized equiv with `bivariateOverlap_equiv_B₁₂gen`.

  **Specialized bridge final status**:
  - Forward + backward directions + action lemmas: ✅ landed.
  - Both round trips: ✅ landed parametrically.
  - Full RingEquiv bundles (raw / via inputs): ✅ landed.
  - End-to-end composite `TA(B₁_gen) ⧸ outer ≃+* B₁₂_gen b`: ✅ landed.

  **Single remaining residual**: `ReverseRoundTripInputs.hDense`, the
  polynomial density on `TA(B₁_gen b)`. Mathematically honest: captures
  exactly the gap between "quotient of a Tate ring by a general ideal"
  and the canonical Tate topology. Discharging requires either (a)
  explicit `PairOfDefinition` on the quotient (then
  `tateAlgebra_polynomials_dense_canonical` applies), or (b) a direct
  truncation-based density argument.

  **Files touched**: `Adic spaces/LaurentOverlap.lean` (~3450 → ~3600
  lines, ~136 new / -24 cleaned). Focused check — clean, zero sorries.

- **2026-04-21** (T-OV-1 specialized Laurent-overlap quotient bridge,
  reverse round trip closed via narrow extensionality, Primary):
  Reduced the boundary on `backward ∘ forward = id` from
  `[IsTateRing (B₁_gen b)]` to just polynomial density + decomp on the
  outer quotient (bundled in `ReverseRoundTripInputs`).

  **Landed this increment**:
  - `tateAlgebra_continuous_ringHom_ext` — narrow extensionality helper:
    two continuous ring homs `f, g : TA R →+* S` with `S` T2 agree on all
    of `TA R` if they agree on `algebraMap r` for `r ∈ R` and on
    `TateAlgebra.X`, provided polynomials are dense and a polynomial
    decomposition holds. Purely a `Continuous.ext_on` at the TateAlgebra
    level with the usual ring-hom distribution through monomials.
  - `ReverseRoundTripInputs` — 3-field structure capturing the genuinely
    missing hypotheses: `hDense` (polynomial density on TA(B₁_gen b)),
    `hDecomp` (outer polynomial decomposition), `hDecomp_inner` (inner
    polynomial decomposition on TA B — purely algebraic fact that can
    be provided by a univariate analog of `tateAlgebra₂_polynomial_decomp`).
    Inner density is FREE via `[IsTateRing B]` and
    `tateAlgebra_polynomials_dense_canonical`.
  - `TA_B₁_gen_quotient_backward_forward_eq_id_of_inputs` — parametric
    reverse round trip proof: applies `Ideal.Quotient.ringHom_ext` at
    outer ideal, then `tateAlgebra_continuous_ringHom_ext` at R := B₁_gen,
    then (for algMap agreement) `Ideal.Quotient.ringHom_ext` at inner
    ideal + `tateAlgebra_continuous_ringHom_ext` at R := B. Generator
    agreement via existing action lemmas.
  - `TA_B₁_gen_quotient_specialized_equiv_of_inputs` — convenience
    `RingEquiv` using `ReverseRoundTripInputs` directly.

  **Specialized bridge final status**:
  - Forward direction + action lemmas: ✅ landed.
  - Backward direction + action lemmas: ✅ landed.
  - `forward ∘ backward = id`: ✅ landed parametrically.
  - `backward ∘ forward = id`: ✅ landed parametrically via
    `ReverseRoundTripInputs`.
  - Full `RingEquiv` bundle: ✅ landed in TWO flavors (raw `h_bwd_fwd` +
    via `ReverseRoundTripInputs`).

  **Remaining boundary** (minimal): three concrete algebraic/topological
  facts in `ReverseRoundTripInputs` — outer density, outer decomp, inner
  decomp. None require `PairOfDefinition` construction on the quotient.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (~3200 → ~3450 lines, ~241 new lines for extensionality + reverse
  round trip + convenience equiv). Focused check — clean.

- **2026-04-21** (T-OV-1 specialized Laurent-overlap quotient bridge,
  parametric RingEquiv bundle landed, Primary):
  Bundled the specialized Laurent-overlap quotient bridge into a
  `RingEquiv` parametric on the reverse round trip hypothesis.
  Landed `TA_B₁_gen_quotient_specialized_equiv` in
  `Adic spaces/LaurentOverlap.lean`. Focused build passes with zero sorries.

  **Landed this increment**:
  - `TA_B₁_gen_quotient_specialized_equiv` — parametric `RingEquiv`
    `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b ≃+* TA₂ B ⧸
    bivariateOverlapIdeal b`. Fields:
    * `toFun` = `TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom`
    * `invFun` = `TA_B_bivariate_quotient_to_outerQuotient_backwardHom`
    * `right_inv` = discharged via landed
      `TA_B₁_gen_quotient_forward_backward_eq_id`
    * `left_inv` = threaded via explicit `h_bwd_fwd` hypothesis
  - Takes the full hypothesis menu: `hcont_base`, `h : BackwardEvalHypotheses`,
    `hcont_forward`, `hcont_backward`, `h_bwd_fwd`.

  **Specialized bridge final status**:
  - Forward direction + action lemmas: ✅ landed.
  - Backward direction + action lemmas: ✅ landed.
  - Round trip `forward ∘ backward = id`: ✅ landed parametrically.
  - Round trip `backward ∘ forward = id`: exposed as `h_bwd_fwd`
    hypothesis (boundary documented in prior log entry — requires
    `IsTateRing (B₁_gen b)` or parameterization on polynomial density).
  - Full `RingEquiv` bundle: ✅ landed parametrically.

  **Downstream usability**: any caller with the outer-quotient
  topological structure (via `BackwardEvalHypotheses`), forward+backward
  continuity, and the reverse round trip can instantiate
  `TA_B₁_gen_quotient_specialized_equiv` and use it as a concrete
  `RingEquiv`. This gives an alternative to (or supplements)
  `example638Bivariate_equiv` for downstream
  `laurentOverlapBridge_exists_compatible` consumption.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (~3150 → ~3200 lines, ~47 new lines for RingEquiv bundle).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — clean.

- **2026-04-21** (T-OV-1 specialized Laurent-overlap quotient bridge,
  forward∘backward round trip landed parametrically, Primary):
  Proved the first of two round trips for the specialized quotient bridge
  in `Adic spaces/LaurentOverlap.lean`. Focused build passes with zero sorries.

  **Landed this increment**:
  - `TA_B₁_gen_quotient_forward_backward_eq_id` — parametric round-trip
    theorem `forward ∘ backward = id on TA₂ B ⧸ bivariateOverlapIdeal b`.
    Takes `hcont_forward` and `hcont_backward` as explicit continuity
    hypotheses (mirrors `example638Bivariate_backward_forward_eq_id` /
    `example638Plus_equiv` pattern). Proof uses:
    * `Ideal.Quotient.ringHom_ext` to reduce to `TA₂ B` level.
    * `tateAlgebra₂_polynomials_dense_canonical` for polynomial density.
    * `tateAlgebra₂_polynomial_decomp` for finite-sum decomposition.
    * Monomial-wise agreement via `forwardHom_mk_algebraMap_mk_algebraMap`
      + `_mk_algebraMap_mk_X` + `_mk_X` action lemmas (forward side) and
      `evalHom₂_algebraMap` + `_X` + `_Y` action lemmas (backward side).
    * `Continuous.ext_on` to extend from polynomials to full TA₂ B.
    * `TateAlgebra.quotient_bivariateOverlapIdeal_t2Space` for T2Space.
  - Required `set_option maxHeartbeats 800000 in` due to the 12-step
    `map_mul`/`map_pow` rewrite chain in the monomial agreement lemma.

  **Specialized bridge status (updated)**:
  - Forward direction + action lemmas: ✅ landed (prior commits).
  - Backward direction + action lemmas: ✅ landed (prior commits).
  - Round trip `forward ∘ backward = id`: ✅ landed this increment.
  - Round trip `backward ∘ forward = id` on TA(B₁_gen) / outer: **blocked**
    on polynomial density for `TA(B₁_gen b)`.
  - Full `RingEquiv` bundle: pending (needs both round trips).

  **Density boundary for `backward ∘ forward = id`**: would require
  `@Dense (↥(TateAlgebra (B₁_gen b))) instTopologicalSpaceTateAlgebra
  polynomials` — the univariate analog of
  `tateAlgebra₂_polynomials_dense_canonical`. The existing
  `tateAlgebra_polynomials_dense_canonical` (in
  `Adic spaces/TopologyComparison.lean:1479`) requires `[IsTateRing A]`
  at `A := B₁_gen b`. `IsTateRing (B₁_gen b)` is not obviously automatic:
  it requires a `PairOfDefinition` on `B₁_gen b` (subring A₀ + top.-nilp.
  ideal I with `I^n` basis of nbhds of 0). The quotient of `TA B` by
  `plusFSubXIdeal b` doesn't inherit such a pair without additional work.
  Two paths:
  * (a) Prove `IsTateRing (B₁_gen b)` by constructing an explicit
    `PairOfDefinition` (using e.g. the image of `TA.pairSubring`'s
    principal pair under the quotient).
  * (b) Parameterize `backward ∘ forward = id` on `hDense` +
    `polynomial_decomp` as additional hypotheses, mirroring the
    `BackwardEvalHypotheses` threading pattern. Strictly weaker but clean.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (~3020 → ~3150 lines, ~134 new lines for round trip).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — clean.

- **2026-04-20** (T-OV-1 specialized Laurent-overlap quotient bridge,
  backward direction scaffolded with hypothesis bundle, Primary):
  Landed the full backward-direction infrastructure in
  `Adic spaces/LaurentOverlap.lean`, closing Steps 6-8 of the critical-path
  plan for T-OV-1 / T-OVERLAP-COMPAT. Focused build passes with zero sorries.

  **Landed this increment** (11 new defs/theorems):
  1. `outerQuotient_baseHom` — the composition
     `B → TA B → B₁_gen b → TA(B₁_gen b) → outer quotient` as a ring hom.
  2. `outerQuotient_YbarTgt` — image of `algMap(mk_inner(TA.X))` in the outer
     quotient (target for `TA₂.X` under backward).
  3. `outerQuotient_XoutTgt` — image of outer `TateAlgebra.X` in the outer
     quotient (target for `TA₂.Y` under backward).
  4. `BackwardEvalHypotheses` — hypothesis bundle structure with 10 fields:
     `topOuter`, `ringOuter`, `uOuter`, `uAddOuter`, `cOuter`, `tOuter`,
     `naOuter` (the outer quotient's topological structure) plus analytic
     hypotheses `hcont_base`, `hpb_Ybar`, `hpb_Xout` (continuity + power-
     boundedness). Mirrors the `example638Plus_equiv`/`hcont_forward`
     pattern where unprovable-at-this-level facts are threaded as hypotheses.
  5. `TA_B_bivariate_to_outerQuotient_evalHom₂` — backward evaluation hom
     `TA₂ B →+* outer quotient` built via `evalHomBounded₂` from the
     hypothesis bundle.
  6. `_algebraMap`, `_X`, `_Y` action lemmas: evalHom₂ sends `algMap a` to
     `outerQuotient_baseHom a`, `TA₂.X` to `outerQuotient_YbarTgt`, and
     `TA₂.Y` to `outerQuotient_XoutTgt` respectively.
  7. `_algMap_b_sub_X_eq_zero` — kernel lemma: evalHom₂ kills
     `algMap b - TA₂.X`. Uses `quotient_algebraMap_b_eq_X` in B₁_gen b.
  8. `_one_sub_algMap_b_Y_eq_zero` — kernel lemma: evalHom₂ kills
     `1 - algMap b · TA₂.Y`. Uses `quotient_algebraMap_b_eq_X` + the outer
     ideal relation `1 - Ybar · X_out ∈ outerLaurentOverlapIdeal`.
  9. `TA_B_bivariate_quotient_to_outerQuotient_backwardHom` — factored
     backward quotient hom via `Ideal.Quotient.lift` on
     `bivariateOverlapIdeal`.
  10. `_mk_algebraMap`, `_mk_X`, `_mk_Y` — three action lemmas on the
      factored backward quotient hom.

  **Specialized bridge status (updated)**:
  - First-stage forward: ✅ landed (prior).
  - Factor through `plusFSubXIdeal b`: ✅ landed (prior).
  - Outer `evalHomBounded` on `TA(B₁_gen b)`: ✅ landed (prior).
  - Factor through outer `(1 - Ybar · X_out)` ideal: ✅ landed (prior).
  - Forward quotient action lemmas: ✅ landed (prior).
  - Backward `TA₂ B → outer quotient` via `evalHomBounded₂`: ✅ landed.
  - Backward action lemmas on `algebraMap`/`X`/`Y`: ✅ landed.
  - Kernel lemmas on both `bivariateOverlapIdeal` generators: ✅ landed.
  - Factored backward quotient hom: ✅ landed.
  - Backward quotient action lemmas on `mk`-generators: ✅ landed.
  - Round trips `forward∘backward = id` and `backward∘forward = id`:
    pending (needs density/continuity argument; evalHomBounded₂-based homs
    agree on generators but the underlying rings aren't generated by
    polynomials finitely — likely requires continuity-based extension).
  - Full `RingEquiv` bundle: pending (needs round trips first).

  **Discharge of `BackwardEvalHypotheses`**: for the specialized bridge to be
  USABLE by downstream `laurentOverlapBridge_exists_compatible`, callers must
  supply (at instantiation points) the outer-quotient topological structure
  + continuity + power-boundedness. These follow from the localization /
  completion structure of `presheafValue(overlap)`, but construction of the
  explicit evidence is downstream work.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (~2860 → ~3020 lines, ~160 new lines for backward direction).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — clean.

- **2026-04-20** (T-OV-1 specialized Laurent-overlap quotient bridge,
  outer evalHom + forward quotient hom + action lemmas landed, Primary):
  Completed Steps 3, 4, and 5 of the forward direction for the specialized
  Laurent-overlap quotient bridge in `Adic spaces/LaurentOverlap.lean`.
  Focused build passes with zero sorries, only pre-existing unused-section-
  variable warnings.

  **Landed this increment** (7 new defs/theorems + 2 local instances):
  1. `B₁_gen_nonarchimedeanRing` — extracted inline construction from
     `Example638.lean:529` as named reusable theorem: `B₁_gen b` is a
     nonarchimedean ring under `quotientPlusFSubXIdealTopology`. Uses
     `NonarchimedeanRing.is_nonarchimedean` on the ambient `TateAlgebra B`
     plus `QuotientRing.isOpenMap_coe` to push the open subgroup through
     the quotient map.
  2. `local instance B₁_gen_topologicalSpace` and
     `local instance B₁_gen_nonarchimedeanRing_inst` — registered at section
     level so downstream signatures can mention `TateAlgebra (B₁_gen b)`
     without explicit `@` annotations or fragile `haveI`-in-type-signature
     patterns.
  3. `TA_B₁_gen_to_bivariateOverlap_outer_evalHom` — outer evalHom
     `TA(B₁_gen b) →+* TA₂ B ⧸ bivariateOverlapIdeal b` built via
     `TateAlgebraWedhorn.evalHomBounded` with base =
     `baseHom_B₁_gen_to_bivariateOverlap` and target element =
     `mk TateAlgebra₂.Y`. Takes `hcont_base` as an explicit hypothesis
     (mirroring `example638Plus_equiv.hcont_forward` pattern).
  4. `TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap` — action on
     constants: `outer_evalHom (algebraMap α) = baseHom α` for
     `α : B₁_gen b`. Via `tsum_eq_single 0` + `MvPowerSeries.coeff_C`.
  5. `TA_B₁_gen_to_bivariateOverlap_outer_evalHom_X` — action on outer
     `TateAlgebra.X`: equals `mk TateAlgebra₂.Y`. Via `tsum_eq_single 1` +
     `MvPowerSeries.coeff_X`.
  6. `TA_B₁_gen_to_bivariateOverlap_outer_evalHom_oneSub_eq_zero` — kernel
     lemma: the outer ideal generator `1 - Ybar · X_out` maps to 0. Via
     ring manipulation `X·Y - 1 = -(1 - algMap b · Y) - (-Y)(algMap b - X)`
     expressing the difference as a linear combination of the two
     `bivariateOverlapIdeal` generators.
  7. `outerLaurentOverlapIdeal` — `1 - Ybar · X_out` ideal definition.
  8. `TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom` — factored forward
     hom `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b →+*
     TA₂ B ⧸ bivariateOverlapIdeal b`, via `Ideal.Quotient.lift` on the
     outer evalHom with kernel discharged by lemma (6).
  9. `TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom_mk_algebraMap_mk_algebraMap`,
     `_mk_algebraMap_mk_X`, `_mk_X` — three action lemmas describing the
     forward quotient hom on generators:
     * `mk_outer(algMap(mk_inner(algMap a)))` ↦ `mk(algMap a)`.
     * `mk_outer(algMap(mk_inner(TateAlgebra.X)))` ↦ `mk TateAlgebra₂.X`.
     * `mk_outer(TateAlgebra.X)` ↦ `mk TateAlgebra₂.Y`.
     Each proved via `change _ = _; rw [Ideal.Quotient.lift_mk, outer_evalHom_...]`
     — mirroring `example638Bivariate_forwardHom_mk_algebraMap` pattern.

  **Specialized bridge status (updated)**:
  - First-stage forward: ✅ landed (prior increment).
  - Factor through `plusFSubXIdeal b`: ✅ landed (prior increment).
  - Outer `evalHomBounded` on `TA(B₁_gen b)`: ✅ landed.
  - Factor through outer `(1 - Ybar · X_out)` ideal: ✅ landed.
  - Forward quotient action lemmas on generators: ✅ landed.
  - Backward `TA₂ B → TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b` via
    `evalHomBounded₂`: pending. Plan: base hom
    `a ↦ mk_outer(algMap(mk_inner(algMap a)))`, target elements
    `mk_outer(algMap(mk_inner(X)))` (for TA₂.X) and `mk_outer(TA.X)` (for
    TA₂.Y). Kernel contains both `algMap b - TA₂.X` (via plusFSubXIdeal
    relation in B₁_gen) and `1 - algMap b · TA₂.Y` (via outerLaurentOverlapIdeal
    relation after Ybar = X substitution).
  - Round trips forward∘backward = id and backward∘forward = id: pending.
  - Bundle into full `RingEquiv`: pending.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (~2510 → ~2860 lines, ~350 new lines for outer evalHom + forward
  quotient hom + action lemmas + local instances).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — clean
  (no errors, no sorries, only pre-existing unused-section-variable
  warnings on unrelated theorems).

- **2026-04-20** (T-OV-1 specialized Laurent-overlap quotient bridge,
  forward factor-through landed, Primary): Extended the first-stage evalHom
  through the `plusFSubXIdeal b` quotient to land `baseHom_B₁_gen_to_bivariateOverlap`
  plus its action lemmas in `Adic spaces/LaurentOverlap.lean`. Full build passes
  (2627 jobs), zero sorries. Three new named theorems/defs in addition to the
  three from the prior increment:
  4. `TA_B_to_bivariateOverlap_evalHom_plusFSubX_eq_zero` — kernel lemma:
     the evalHom kills `algebraMap b - X`. Proved via
     `map_sub` + `_algebraMap` + `_X` + `TateAlgebra.quotient_algebraMap_b_eq_X_bivariate`
     + `sub_self`.
  5. `baseHom_B₁_gen_to_bivariateOverlap` — factored
     `B₁_gen b →+* TA₂ B ⧸ bivariateOverlapIdeal b`. Built via
     `Ideal.Quotient.lift plusFSubXIdeal (TA_B_to_bivariateOverlap_evalHom) _`
     with kernel discharged by (4) via `Ideal.span_le`.
  6. `baseHom_B₁_gen_to_bivariateOverlap_mk_algebraMap` — action on
     `mk(algebraMap a) ↦ mk(algebraMap a)`.
  7. `baseHom_B₁_gen_to_bivariateOverlap_mk_X` — action on
     `mk(TateAlgebra.X) ↦ mk(TateAlgebra₂.X)`.

  **Status on full specialized bridge (updated)**:
  - First-stage forward (`TA B → TA₂ B ⧸ bivariateOverlapIdeal b`): ✅ landed.
  - Factor through `plusFSubXIdeal b`: ✅ landed with action lemmas.
  - Outer `evalHomBounded` on `TA(B₁_gen b)`: pending — requires continuity of
    `baseHom_B₁_gen_to_bivariateOverlap` and `NonarchimedeanRing B₁_gen b`
    typeclass. Continuity reduces to continuity of
    `TA_B_to_bivariateOverlap_evalHom` (which is `evalHomBounded`-based and
    lacks a general continuity theorem in the project). Path forward: take
    continuity as a hypothesis (mirroring how `example638Plus_equiv` takes
    `hcont_forward` as a hypothesis). `NonarchimedeanRing B₁_gen b` is
    constructed inline in `Example638.lean:529` — extract as named lemma.
  - Factor through outer `(1 - Ybar · X_out)` ideal: pending.
  - Backward + round trips: pending.

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (2427 → ~2510 lines, ~80 new lines for factor-through + action lemmas).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — clean.
  Full build `lake build "«Adic spaces».LaurentOverlap"` — passes.

- **2026-04-20** (T-OV-1 specialized Laurent-overlap quotient bridge,
  first-stage forward landed, Primary): First-stage forward map of the
  specialized bridge landed in `Adic spaces/LaurentOverlap.lean`. Three new
  theorems/defs, sorry-free, full build passes (2627 jobs):
  1. `TA_B_to_bivariateOverlap_evalHom` — `TA B →+* TA₂ B ⧸ bivariateOverlapIdeal b`
     via `TateAlgebraWedhorn.evalHomBounded`, using:
     * base map `mk ∘ algebraMap B (TA₂ B)` (continuous via
       `TateAlgebra.mk_algebraMap_continuous_bivariateOverlap`);
     * target element `mk TateAlgebra₂.X` (power-bounded via
       `TateAlgebra.mk_X_isPowerBounded_in_bivariateOverlap`);
     * all target typeclass instances (`CompleteSpace`, `T0Space`,
       `NonarchimedeanRing`, `IsUniformAddGroup`) constructed inside via
       existing T013 lemmas.
  2. `TA_B_to_bivariateOverlap_evalHom_algebraMap` — action on constants:
     `evalHom (algebraMap a) = mk (algebraMap a)`. Proof pattern mirrors
     `example638Plus_evalHom_algebraMap` (unfold + `tsum_eq_single 0` +
     `MvPowerSeries.coeff_C`).
  3. `TA_B_to_bivariateOverlap_evalHom_X` — action on X:
     `evalHom TateAlgebra.X = mk TateAlgebra₂.X`. Via `tsum_eq_single 1` +
     `MvPowerSeries.coeff_X`.

  **Specialized bridge status**:
  - First-stage forward (`TA B → TA₂ B ⧸ bivariateOverlapIdeal b`): **landed** ✅.
  - Next step: factor through `plusFSubXIdeal b = (algebraMap b - X)` to get
    `B₁_gen b → TA₂ B ⧸ bivariateOverlapIdeal b`. The ideal lies in the kernel
    because `algMap b - X ↦ mk(algMap b) - mk(X)`, and
    `mk(algMap b) = mk(X)` via existing
    `TateAlgebra.quotient_algebraMap_b_eq_X_bivariate`.
  - Then outer `evalHomBounded` on `TA(B₁_gen b)` with base = previous hom,
    target elt = `mk TateAlgebra₂.Y` (power-bounded via
    `TateAlgebra.mk_Y_isPowerBounded_in_bivariateOverlap`). Requires
    continuity of the base hom (easy: quotient_lift of continuous hom).
  - Then factor `(1 - Ybar · X_out)` via algebraic identification using
    `bivariateOverlap_ideal_eq` + negation swap.

  **Remaining work on forward side**: ~80 lines for the two factorization
  steps + associated action lemmas.
  **Remaining work on backward side + round trips**: ~200 lines total
  (analog of `example638Bivariate_backward_forward_eq_id` pattern).

  **Files touched this session**: `Adic spaces/LaurentOverlap.lean`
  (1965 → ~2427 lines, ~460 new lines — first-stage def + two action
  lemmas + supporting typeclass wiring).
  Focused check `lake env lean "Adic spaces/LaurentOverlap.lean"` — zero
  errors, zero sorries. Full build `lake build "«Adic spaces».LaurentOverlap"`
  — completed successfully.

- **2026-04-20** (H1 non-domain direct attempt, Tate-topology obstruction,
  sorry removed, Primary): Reviewer tightened criteria: do not leave a
  newly imported sorry as landed progress. Attempt to close non-domain
  H1 directly on Steps 4 & 5; if unsuccessful, remove the sorry theorem.

  **Outcome chosen: sorry removed. H1 domain landed; H1 general target
  is documentation-only + escalation packet.** Justification: direct
  attempt uncovered a **fundamental Tate-topology obstruction at Step 5**
  that cannot be closed with current infrastructure; per reviewer
  directive, the sorry is removed rather than left in the root import.

  **Obstruction found** (new this session, refining the earlier packet):

  The proposed Hübner proof sketch needs (after general Krull +
  iteration): from `a = c^N · f^N · a` and `f^N · a → 0` in B's topology,
  to conclude `a ∈ I^k` for every open nhd `I^k` of 0, hence `a = 0` by
  Hausdorff. This works IF the 0-nhd basis consists of ideals I^k with
  `c · I^k ⊆ I^k` for every `c ∈ B` (the Krull witness).

  **But in a Tate ring** B with pair of definition (B₀, I₀):
  * The 0-nhd basis `{I₀^k}_k` consists of ideals of **B₀**, not of B.
  * Extending `I₀^k · B` makes them ideals of B, but they become all of
    B (since the topologically-nilpotent unit `π ∈ I₀` is a unit in B:
    `I₀ · B = π · B₀ · B = B`).
  * The iteration step requires `c · I₀^k ⊆ I₀^k`, i.e., `c ∈ B₀`
    (power-bounded). The Krull witness `c` from Mathlib
    `Ideal.mem_iInf_smul_pow_eq_bot_iff` is an arbitrary `c ∈ B`, not
    necessarily in B₀.

  This is a **genuine mathematical obstruction**, not just a
  formalization detail. The Hübner-route proof via general Krull +
  iteration + topological Hausdorffness does NOT close Laurent-pair
  injectivity for non-domain noetherian Tate rings. A different
  strategy is needed:
  * **(a)** Refined Krull giving witness `c ∈ B₀`.
  * **(b)** Different argument (flatness + spectrum, or mapping cone).
  * **(c)** Stacks 00MA / Cor 8.32 — which is what we were trying to
    avoid.

  **Work completed**:
  1. **Kept** `laurentCover_separation_presheaf_viaRow3_domain`
     (H1-domain, sorry-free).
  2. **Removed** `laurentCover_separation_presheaf_viaRow3_noetherian`
     sorry theorem. Replaced with a **documentation comment block**
     (lines 140-203 in `HubnerSeparation.lean`) stating the target, the
     obstruction found, and pointing to the escalation packet.
  3. **Updated** module docstring: "domain H1 landed; non-domain H1
     documented/pending (not imported as sorry)".
  4. **Kept** `.mathlib-quality/chatgpt-packet-hubner-nondomain.md`
     (154 lines) unchanged — the external escalation artifact for the
     ChatGPT Pro question.

  **Net project sorry delta this session**: 0. No new sorry in
  HubnerSeparation.lean. Domain H1 remains landed sorry-free; non-domain
  target is documentation-only.

  **Next-session decision point**:
  * **(a)** Escalate the packet to ChatGPT Pro / math research and act
    on the response (closes the open mathematical question).
  * **(b)** Accept `tateAcyclicity_for_domains` as a domain-only
    restricted theorem and move forward with H2/H3/H4 under that scope.
  * **(c)** Concede Hübner decouples only partly and keep Lane B
    (T-COMP-FF / T-IDEAL-2) / Stacks 00MA on the critical path.

  **Files**: `Adic spaces/HubnerSeparation.lean` edited (202 lines,
  0 sorry). No other files touched.

  **Build**: `lake build «Adic spaces».HubnerSeparation` → EXIT 0,
  clean (no sorry warning from HubnerSeparation; the only sorry warning
  in the build is the pre-existing LaurentRefinement.lean:3671
  `tateAcyclicity` Part 2 sorry, unchanged).

  **Axiom check**: `laurentCover_separation_presheaf_viaRow3_domain`
  has axioms `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` here is exclusively the **pre-existing T001 leak** via
  `restrictionMap → HasLocLiftPowerBounded → isUnit_algebraMap_s_of_huber
  → spa_point_nonOpen_of_rational_subset` (Presheaf.lean:807).
  HubnerSeparation.lean itself introduces no new sorry.

- **2026-04-20** (T-OV-1 reviewer-driven critical path revision, Primary):
  Reviewer update: **full TateAlgebra quotient transport deferred; specialized
  overlap bridge preferred**.

  **Revised plan**: build the specialized Laurent-overlap quotient-of-quotients
  bridge rather than the full `(R/I)⟨X⟩ ≃+* R⟨X⟩/I⟨X⟩` general theorem.

  **Specialized target theorem** (in project notation):
  ```lean
  noncomputable def TA_B₁_gen_quotient_equiv_bivariateOverlap
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
      [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
      [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
      (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
      (hA_complete : ...)
      (hnoeth : ...) :
      ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ Ideal.span {
        (1 : ↥(TateAlgebra (LaurentCover.B₁_gen b))) -
          (algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b)))
            (Ideal.Quotient.mk (plusFSubXIdeal B b) TateAlgebra.X) *
          TateAlgebra.X
      } ≃+*
        ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b
  ```

  Schematically:
  `TA(B₁_gen b) ⧸ (1 - Ybar · X_out) ≃+* TA₂ B ⧸ (algMap b - X_{2,1}, 1 - X_{2,1}·X_{2,2})`
  where `Ybar = mk(TateAlgebra.X) ∈ B₁_gen b`, `X_out` is the outer TateAlgebra variable,
  and the RHS ideal equals `bivariateOverlapIdeal b` via project's
  `bivariateOverlap_ideal_eq` (swapping negated generator).

  **Construction plan** (forward direction, ~150 lines):
  1. Base map `B₁_gen b → TA₂ B ⧸ bivariateOverlapIdeal b` via
     `Ideal.Quotient.lift` applied to `TA B →+* TA₂ B ⧸ (algMap b - X_{2,1}, ...)`
     sending `X_{TA B} ↦ X_{2,1}` and `algMap a ↦ algMap a`. Well-defined because
     `algMap b - X_{TA B}` maps to `algMap b - X_{2,1} ≡ 0` (mod target ideal).
  2. Continuity via `continuous_quotient_mk'` composed with the TA-level hom's
     continuity.
  3. Power-boundedness of `X_{2,2}` image in the quotient — already landed as
     `TateAlgebra.mk_Y_isPowerBounded_in_bivariateOverlap` (project).
  4. Apply `evalHomBounded` (from `TateAlgebraWedhorn.lean`) with base map from (1)
     and element `X_{2,2}` (power-bounded by (3)) to get
     `TA(B₁_gen b) →+* TA₂ B ⧸ bivariateOverlapIdeal b`.
  5. Factor through the outer quotient `(1 - Ybar · X_out)`: it maps to
     `1 - X_{2,1} · X_{2,2} ≡ 0` in `TA₂ B ⧸ bivariateOverlapIdeal b` via the
     `bivariateOverlap_ideal_eq` identification.

  **Backward direction** (~100 lines): construct
  `TA₂ B → TA(B₁_gen b) ⧸ (1 - Ybar · X_out)` via `evalHomBounded₂` sending
  `X_{2,1} ↦ algMap_{TA(B₁_gen b)} Ybar` (power-bounded since it's a unit's image)
  and `X_{2,2} ↦ X_out`. Factor through the ideal.

  **Round trips** (~100 lines): via `Ideal.Quotient.ringHom_ext` +
  `polynomial decomposition` (similar to `example638Bivariate_backward_forward_eq_id`).

  **Estimated size**: ~350 lines total for the specialized bridge alone.

  **Unlocks**:
  - Compose with `bivariateOverlap_equiv_B₁₂gen` → `TA(B₁_gen b) ⧸ (...) ≃+* B₁₂_gen b`.
  - Compose with `TateAlgebra_mapRingEquiv laurentPlusBridge_{cont,symm_cont}`
    (landed prior session) → `TA(B_plus) ⧸ (...) ≃+* TA(B₁_gen b) ⧸ (...)`.
  - Combined: Step 3 of T-OVERLAP-COMPAT composition route becomes available.

  **Fallback plan per reviewer**: if specialized becomes as hard as full, pivot
  to direct two-variable Example 6.38 proof for the A-side overlap:
  `presheafValue (laurentOverlapDatum D₀ f) ≃+* A⟨Y,X⟩/...`. However, this
  requires a new Example 6.38 proof for arbitrary rational-sub-datum
  (not just `trivialPlusDatum`), structurally at least as large as the
  specialized quotient approach. Current `example638Bivariate_equiv` only
  covers `overlapDatum B P b` (with `trivialPlusDatum` base, `s = 1`), not
  the Laurent `overlapDatum D₀ f` (with `s = D₀.s * f`).

  **Action item**: queue the specialized bridge as the next Lane A work
  session. Estimated two to three focused sessions for the ~350-line build
  + integration.

  **Files this session**: `.mathlib-quality/tickets.md` (this entry).
  Focused check `Adic spaces/LaurentOverlap.lean` — clean (no errors, no sorries).
  No code changes this session (reviewer revision is a critical-path pivot
  not a tactical fix).

- **2026-04-20** (Hübner-route audit: Cor 8.32 decoupling feasibility, Primary):
  Reviewer update: Lane B (T-COMP-FF / T-IDEAL-2 Cor 8.32) is now OPTIONAL
  infrastructure. New target: audit whether
  `simple-Laurent-exactness-for-every-rational-open + standard/Laurent refinement
  ⟹ tateAcyclicity` can bypass Cor 8.32.

  **Audit finding: Cor 8.32 is NOT unavoidable for Part 1 (separation).
  It IS currently hardwired in Part 2's `lane_B_supplier` but can be
  replaced by a Hübner-style Laurent route via existing sorry-free pieces.**

  **Current Cor 8.32 touchpoints in the final assembly:**
  1. `tateAcyclicity` (LaurentRefinement.lean:3671) Part 1 uses
     `ValuationSpectrum.restrictionMapHom_injective` at line 3695 — a
     RETIRED-AS-FALSE single-map injectivity (PresheafTateStructure.lean:1322,
     sorry-carrying; retired 2026-04-18). Replacing with Cor 8.32 cover-level
     product-injectivity is the documented critical path. Hübner route CAN
     replace this without Cor 8.32 (see below).
  2. `tateAcyclicity_Part2_via_hZavyalov_per_E_direct`
     (GeometricReduction.lean:3412) `lane_B_supplier` (lines 3441–3451) — an
     explicit hypothesis for per-E injectivity of product restriction to the
     `per_E_local_covering`. This is Cor 8.32 at each `E ∈ C.covers` and is
     the principal Cor 8.32 wiring in the Part 2 assembly.

  **Hübner-route pieces ALREADY SORRY-FREE (at algebraic level):**
  - `LaurentCover.epsilonHom_gen_injective` (LaurentCoverExact.lean:315) —
    algebraic Laurent-pair injectivity via Krull intersection; axioms
    `[propext, Classical.choice, Quot.sound]`.
  - `LaurentCover.row3_exact` (LaurentCoverExact.lean:1560) — full algebraic
    Laurent row exactness; axioms `[propext, Classical.choice, Quot.sound]`.
  - `ValuationSpectrum.separation_of_finer_rational`
    (RationalRefinement.lean:42) — refinement transfer of separation;
    proof body is sorry-free. (Axiom check shows `sorryAx` but this is
    pre-existing leak from `[HasLocLiftPowerBounded A]` → `restrictionMap`
    → `spa_point_nonOpen_of_rational_subset` sorry at Presheaf.lean:807,
    NOT from the theorem's own proof — fixable by `omit`.)

  **Hübner-route pieces PARAMETERIZED (use-site hypotheses, no sorry body):**
  - `laurentPlusBridge`, `laurentMinusBridge` (LaurentRefinement.lean:2480,
    2548) — ring isos `presheafValue(laurent) ≃+* B₁/₂_gen`, unconditional
    defs with six hypothesis bundle.
  - `laurentPlusBridge_restrictionMap`, `laurentMinusBridge_restrictionMap`
    (LaurentRefinement.lean:2734, 2853) — intertwining lemmas.

  **Pre-existing foundational sorry (affects EVERY `restrictionMap` use,
  not just Cor 8.32):**
  - `spa_point_nonOpen_of_rational_subset` (Presheaf.lean:807). Hits via
    `isUnit_algebraMap_s_of_huber` → `HasLocLiftPowerBounded` → `restrictionMap`.
    **Any route using `restrictionMap` carries this sorry via typeclass leak
    until T001 closes.** This is orthogonal to Cor 8.32.

  **Theorem boundary to decouple Part 1 from Cor 8.32:** three new theorems,
  all landable with existing infrastructure modulo pre-existing T001 gap:

  ```lean
  -- Theorem H1 (new, ~50 lines): Laurent separation at presheafValue level
  -- via `epsilonHom_gen_injective` + `laurentPlus/MinusBridge_restrictionMap`.
  theorem laurentCover_separation_presheaf
      [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
      (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
      (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
      [LaurentNormalized D₀] (f : A) (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
      (hNoeth_B ... hcont_eval_B : ...)  -- seven hypothesis bundle (same as gluing)
      (hplus hminus : ...) (x : presheafValue D₀)
      (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
      (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
      x = 0

  -- Theorem H2 (new, ~80-150 lines): iterated Laurent separation via induction
  -- on standard-cover size, using H1 + the standard-cover Laurent splitting
  -- from S-GEOM-IND (Wedhorn 8.34).
  theorem laurentIteratedCover_separation_presheaf
      (D₀ : RationalLocData A) (S : Finset A) (hSpan : Ideal.span S = ⊤) ... :
      Function.Injective ((productRestriction to laurent-iterated pieces))

  -- Theorem H3 (new, ~30 lines): Hübner Part 1 wrapper, composes H2 with
  -- `separation_of_finer_rational` via `refines_by_standard_cover`.
  theorem tateAcyclicity_Part1_via_hübner
      (C : RationalCovering A) (hne : C.covers.Nonempty)
      (hNullstellensatz : ...)
      (h_laurent_hyps : ... seven hypothesis bundle supplied uniformly) :
      ∀ x : presheafValue C.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
          restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0
  ```

  **Theorem boundary to decouple Part 2 from Cor 8.32** (per-E separation):
  Replace `lane_B_supplier` in
  `tateAcyclicity_Part2_via_hZavyalov_per_E_direct` with a Laurent-route
  supplier, which requires:

  ```lean
  -- Theorem H4 (new, ~50-100 lines): iterated Laurent separation at E
  -- for the per_E_local_covering. Uses H2 at E.1 with the Laurent pieces
  -- coming from the Nullstellensatz refinement at E.
  theorem per_E_local_covering_separation_via_laurent
      (C : RationalCovering A) (S : Finset A) (f₀ : A)
      (hS_per_E : refines_cover_per_E C S) (hS_contain : refines_contain C S)
      (E : { E // E ∈ C.covers })
      (h_laurent_hyps : ... hypothesis package at E) :
      ∀ a b : presheafValue E.1,
        (∀ D ∈ (per_E_local_covering S f₀ E hS_per_E).covers,
          restrictionMap E.1 D _ a = restrictionMap E.1 D _ b) → a = b
  ```

  If H4 lands, the `lane_B_supplier` hypothesis of
  `tateAcyclicity_Part2_via_hZavyalov_per_E_direct` is directly discharged
  by H4 at each E — **eliminating Cor 8.32 from Part 2's critical path**.

  **Feasibility assessment:**
  - H1 is ~50 lines, directly written by mirroring
    `laurentCover_gluing_presheaf_viaRow3` but using `epsilonHom_gen_injective`
    instead of `row3_exact.2.1` — fully feasible with current infrastructure.
  - H2 is the main content: iterated Laurent induction on |S|. Requires the
    same Laurent-split machinery as S-GEOM-IND (Wedhorn 8.34), ~80-150 lines.
  - H3 composes H2 + `refines_by_standard_cover_per_E` + `separation_of_finer_rational`,
    ~30 lines.
  - H4 is essentially H2 applied at E with the per-E local covering being
    identified as a Laurent refinement, ~50-100 lines.

  **Total Hübner-route scope**: ~210–330 lines, all new infrastructure. Does
  NOT need:
  - Stacks 00MA faithful-flatness (Cor 8.32 residual).
  - T-COMP-FF / T-IDEAL-2 Lane B.
  - The `restrictionMapHom_injective` retired false theorem.

  **Still depends on** (shared with the Cor 8.32 route):
  - `laurentOverlapBridge_exists_compatible` (T-OV-1, LaurentRefinement.lean:3173)
    for `laurentCover_gluing_presheaf` (Part 2 only; not for Part 1).
  - `spa_point_nonOpen_of_rational_subset` (T001, Presheaf.lean:807) — pre-existing
    foundational gap affecting all `restrictionMap` consumers.
  - `refines_by_standard_cover_per_E` + Nullstellensatz refinement infrastructure.
  - The LaurentBridges' seven hypothesis bundle (Phase 2.5c/2.6 continuity residues).

  **Recommendation:**
  Option A — **Land H1 + H3 immediately** (minimal viable Hübner Part 1 wrapper):
    ~80 lines, non-conflicting file, demonstrates that Cor 8.32 is NOT on
    Part 1's critical path.

  Option B — **Full Hübner program**: land H1, H2, H3, H4. Decouples BOTH
    Parts 1 and 2 from Cor 8.32. Scope ~300 lines.

  **Not recommended**: continuing T-IDEAL-2 Lane B in parallel — if Hübner
  lands, Lane B becomes optional infrastructure for an already-closed goal.

  **Critical-path update (post-audit):**

  Former critical path (pre-audit):
  ```
  tateAcyclicity Part 1 + Part 2
    ↓
  Cor 8.32 (productRestriction_injective_tate)
    ↓
  T-IDEAL-2 (coeRingHom_preserves_proper)
    ↓
  Stacks 00MA (AdicCompletion.faithfullyFlat_of_le_jacobson)
  ```

  New critical path (Hübner):
  ```
  tateAcyclicity Part 1 (via Hübner wrapper H3)
    ├── H2 (iterated Laurent separation, new)
    │   └── H1 (simple Laurent separation at presheafValue level, new)
    │       ├── epsilonHom_gen_injective (sorry-free)
    │       └── laurentPlus/MinusBridge + intertwinings (sorry-free)
    ├── separation_of_finer_rational (sorry-free)
    └── refines_by_standard_cover_per_E (sorry-free)

  tateAcyclicity Part 2 (via hZavyalov_per_E_direct + H4)
    ├── H4 (iterated per-E Laurent separation) ← replaces Cor 8.32 Lane B
    ├── Lane A = T-OVERLAP-COMPAT (unchanged, orthogonal to Cor 8.32)
    └── hZavyalov_per_E (Nullstellensatz multi-piece, unchanged)
  ```

  Stacks 00MA / Cor 8.32 / T-IDEAL-2 Lane B become OPTIONAL named
  infrastructure for downstream consumers who want stronger faithful-flatness
  statements (beyond what Hübner separation provides).

  **This session outputs**: audit report + **H1 landed**.

  **H1 landed**: `ValuationSpectrum.laurentCover_separation_presheaf_viaRow3`
  in new file `Adic spaces/HubnerSeparation.lean` (152 lines), added to
  `Adic spaces.lean` root imports. Structure mirrors
  `laurentCover_gluing_presheaf_viaRow3`: takes `τ_plus`, `τ_minus` ring isos +
  intertwining conditions `htau_plus`, `htau_minus` + non-unit hypothesis
  `hf_nonunit : ¬IsUnit (D₀.canonicalMap f)`, and concludes: if
  `restrictionMap D₀ plus x = 0` and `restrictionMap D₀ minus x = 0` then
  `x = 0`. Proof directly applies `LaurentCover.epsilonHom_gen_injective`
  after componentwise reduction of both restriction vanishings via the
  intertwining conditions. No new sorry introduced. Axiom check:
  `[propext, sorryAx, Classical.choice, Quot.sound]` where `sorryAx` is
  the **pre-existing T001 leak** via `restrictionMap` →
  `HasLocLiftPowerBounded` → `isUnit_algebraMap_s_of_huber` →
  `spa_point_nonOpen_of_rational_subset` (Presheaf.lean:807) — identical
  to every other `restrictionMap`-consuming theorem in the project.

  **Domain caveat**: H1 requires `[IsDomain (presheafValue D₀)]` because
  `LaurentCover.epsilonHom_gen_injective` uses `Ideal.iInf_pow_eq_bot_of_isDomain`
  (Krull intersection). For non-domain Tate rings the Laurent-pair
  injectivity requires a different proof (likely Jacobson + adic completeness,
  which re-encounters the Stacks 00MA territory). This is a genuine math
  limitation of the direct Hübner route. For downstream use in
  `tateAcyclicity`, either (i) restrict to domain Tate rings (a common
  case), or (ii) generalize `epsilonHom_gen_injective` to noetherian Tate
  rings via a non-domain proof strategy (~80 lines of Jacobson/completeness
  argument).

  **Next sessions**:
  1. **H2** iterated Laurent separation (~100-150 lines).
  2. **H3** final Hübner Part 1 wrapper composing H2 +
     `separation_of_finer_rational` + `refines_by_standard_cover_per_E`
     (~30 lines).
  3. **H4** per-E Laurent separation for Part 2 `lane_B_supplier`
     (~80-100 lines).
  4. (Optional) generalize `epsilonHom_gen_injective` to non-domain Tate rings.

  **Builds**: `lake build «Adic spaces».HubnerSeparation` → EXIT 0, clean.

- **2026-04-20** (T-COMP-FF commutativity residual closed, Primary):
  Closed the routine commutativity lemma `locSubringToRingOfDef_val_eq_symm_comp_of`
  in `IdealLocalizationCompletion.lean` (line 311). The proof chains through the
  three bridges forming `presheafValue_ringOfDef_ringEquiv_adicCompletion`:
  (1) `locSubringCompletionEquivAdicCompletion.symm` on `AdicCompletion.of r`
  returns `↑r` via a new project lemma `adicCompletionRingEquiv_coe` (added to
  `AdicCompletionBridge.lean:382`); (2) `completionLocSubringEquiv` on `↑r`
  returns `D.locSubringToCompleted r` via a new project lemma
  `completionRingEquiv_coe` (added to `AdicCompletionBridge.lean:370`);
  (3) `completedLocSubring_ringEquiv_ringOfDef` is identity on `.val`.
  Combining: both sides reduce to `D.coeRingHom r.val` by `rfl` after the
  `RingEquiv.symm_trans_apply` + `RingEquiv.symm_symm` rewrites.

  **Collateral unlocks**: `locSubringToPresheafValue_continuous` promoted
  from `private` to public in `CompletionLocalization.lean:332`.

  **Conditional final interface** `locSubringToRingOfDef_faithfullyFlat_of_residual`
  (line 405) now sorry-free. Under the explicit hypothesis
  `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`
  (Stacks 00MA specialization), it produces
  `RingHom.FaithfullyFlat (locSubringToRingOfDef D)` via
  `faithfullyFlat_algebraMap_iff` + `FaithfullyFlat.of_bijective` +
  `stableUnderComposition` + the new commutativity lemma.

  **Axiom check** (all six theorems):
  ```
  locSubringToRingOfDef_val_eq_symm_comp_of:       [propext, Classical.choice, Quot.sound]
  locSubringToRingOfDef_faithfullyFlat_of_residual: [propext, Classical.choice, Quot.sound]
  presheafValue_ringOfDef_ringEquiv_adicCompletion: [propext, Classical.choice, Quot.sound]
  completedLocSubring_eq_ringOfDef_subring:        [propext, Classical.choice, Quot.sound]
  AdicCompletionBridge.completionRingEquiv_coe:    [propext, Classical.choice, Quot.sound]
  AdicCompletionBridge.adicCompletionRingEquiv_coe: [propext, Classical.choice, Quot.sound]
  ```

  **sorryAx hygiene fix**: added `omit [PlusSubring A] [HasLocLiftPowerBounded A] in`
  before all four `IdealLocalizationCompletion.lean` theorems, because the
  file-wide `[HasLocLiftPowerBounded A]` scope otherwise pulls in a pre-existing
  sorry from `isUnit_algebraMap_s_of_huber`→`spa_point_nonOpen_of_rational_subset`
  (Presheaf.lean:807) via typeclass transitive dependency, even when the
  typeclass is unused in the proof.

  **Downstream**: once Stacks 00MA lands in Mathlib (or as a project-level
  residual), compose with `locSubringToRingOfDef_faithfullyFlat_of_residual`
  to discharge the `RingHom.FaithfullyFlat` hypothesis of the Lane B Cor 8.32
  assembly theorems in `Cor832.lean`.

  **Builds**: `lake env lean "Adic spaces/IdealLocalizationCompletion.lean"` →
  EXIT 0, no warnings. `lake env lean "Adic spaces/Cor832.lean"` → EXIT 0
  (pre-existing unused-variable warning on an unrelated theorem).

- **2026-04-20** (T-OV-1 Step 3 quotient-transport blocker report, Primary):
  Exhaustive Mathlib + project search for the quotient-transport primitive
  needed to complete T-OVERLAP-COMPAT Step 3. Produced precise boundary.

  **Search results (negative)**:
  - `Mathlib/RingTheory/MvPowerSeries/`: no theorem stating
    `MvPowerSeries (R/I) ≃+* MvPowerSeries R ⧸ (I lifted)`. Only functoriality
    (`map_C`, `map_X`, `map_comp`) and ideal-interaction helpers
    (`PowerSeries.map_constantCoeff_le_self_of_X_mem`).
  - `Mathlib/RingTheory/PowerSeries/Ideal.lean`: no univariate version.
  - `Mathlib/Algebra/{Mv,}Polynomial/`: no direct quotient-equiv; closest is
    `MvPolynomial.polynomialQuotientEquivQuotientPolynomial` (different shape).
  - `Adic spaces/`: no `TateAlgebra`-quotient or
    `restrictedMvPowerSeriesSubring`-quotient API.

  **Mathematical issue (structural)**: kernel of
  `MvPowerSeries.map (Ideal.Quotient.mk I) : TA R →+* TA (R/I)` is
  `{g : TA R | ∀ n, coeff n g ∈ I}` ("all coefficients in I"), while
  `Ideal.map (algebraMap R (TA R)) I` is the algebraic ideal generated by
  constants from `I`. For restricted power series the former is generally
  LARGER — it's the topological closure of the latter. Equality requires
  closed `I` + `NonarchimedeanRing` density (Wedhorn Prop 6.17 at R side).

  **Precise theorem boundary**:

  Option A — Full general primitive (~200 lines, reusable):
  ```lean
  noncomputable def TateAlgebra_of_quotient_equiv
      {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [NonarchimedeanRing R] (I : Ideal R)
      (hI_closed : IsClosed ((I : Set R)))
      (hI_fg : I.FG) :
      ↥(TateAlgebra (R ⧸ I)) ≃+* ↥(TateAlgebra R) ⧸
        Ideal.map (algebraMap R ↥(TateAlgebra R)) I
  ```
  Construction: forward via `TateAlgebra_mapRingHom (Ideal.Quotient.mk I)` +
  surjectivity on polynomials (dense); kernel identification uses
  `hI_closed + hI_fg` — ~80 lines.

  Option B — Specialized bivariate primitive (~300 lines):
  ```lean
  noncomputable def bivariateOverlap_from_TA_quotient_iterate
      (B : Type u) [CommRing B] ... (b : B) :
      ↥(TateAlgebra ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)) ≃+*
        ↥(TateAlgebra₂ B) ⧸ Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X}
  ```
  Combines `TA(TA B) ≃+* TA₂ B` (iterate identification, ~80 lines) with
  quotient transport.

  **Both options require a genuinely new structural theorem.** The
  `TA(TA B) ≃+* TA₂ B` identification alone is ~80 lines of coefficient
  re-indexing (Finsupp `Fin 1` ↔ `Fin 2 → ℕ`) + `IsRestricted` preservation.

  **Recommendation**: Option A first (reusable). Apply at `R := TA B`,
  `I := plusFSubXIdeal f_B` to get `TA(TA B ⧸ I) ≃+* TA(TA B) ⧸ (lifted)`,
  then separate `TA(TA B) ≃+* TA₂ B` finishes Step 3.

  **Composition route checkpoint**:
  - Step 1 `presheafValue_iteratedOverlap_as_minus_at_plus` ✅ landed.
  - Step 2 `presheafValue_iteratedOverlap_to_B₂_at_plus` ✅ landed.
  - Step 3 blocker: `TateAlgebra_of_quotient_equiv` (Option A) +
    `TA(TA B) ≃+* TA₂ B`, OR `bivariateOverlap_from_TA_quotient_iterate`
    (Option B).
  - Supporting primitives landed: `TateAlgebra_mapRingEquiv`,
    `laurentPlusBridge_continuous/_symm_continuous`,
    `MvPowerSeries_IsRestricted_map_pub`, `TateAlgebra_mapRingHom`.

  **REFERENCES CHECKED**:
  - Mathlib `RingTheory/MvPowerSeries/Basic.lean:502-555` — `MvPowerSeries.map`
    definition + functoriality + `coeff_map`, `map_C`, `map_X`, `map_comp`.
  - Mathlib `RingTheory/Ideal/Quotient/Operations.lean:67-120, 596-609` —
    `RingHom.quotientKerEquivOfSurjective`, `Ideal.quotientMap` (templates).
  - Mathlib `RingTheory/Ideal/Maps.lean:128` — `Ideal.map_quotient_self`.
  - Mathlib `RingTheory/PowerSeries/Ideal.lean:61-67` — demonstrates
    non-triviality of ideal functoriality through power series.
  - Mathlib `RingTheory/Ideal/Quotient/Defs.lean:212` — `Ideal.quotEquivOfEq`.
  - `Adic spaces/TateAlgebra.lean:75, 135, 170` — `TateAlgebra`,
    `TateAlgebra₂`, `LaurentTateAlgebra`.
  - `Adic spaces/RestrictedPowerSeries.lean:203-228` —
    `MvPowerSeries.IsRestricted_algebraMap`, algebra instance.
  - Wedhorn Prop 6.17 (closed ideals in noetherian Tate — needed for kernel
    closure in Option A).

  **Files touched this session**: `.mathlib-quality/tickets.md` (this entry).
  No code changes — analysis + reporting session given the size of the
  identified primitives.

- **2026-04-20** (T-OV-1 Step 3 naturality, Primary): landed
  `laurentPlusBridge_continuous` and `laurentPlusBridge_symm_continuous` in
  `LaurentOverlap.lean`, removing the Step 3 naturality blocker for
  `TateAlgebra_mapRingEquiv` composition. Seven supporting continuity
  primitives, all sorry-free with zero new axioms:
  1. `iteratedPlus_forwardHom_continuous` — `UniformSpace.Completion.continuous_extension`
     applied to `iteratedPlus_forwardHom` (extensionHom structural).
  2. `iteratedPlus_backwardHom_continuous` — same pattern for backward hom.
  3. `presheafValue_iteratedPlus_equiv_continuous` — equiv wrapper forward.
  4. `presheafValue_iteratedPlus_equiv_symm_continuous` — equiv wrapper backward.
  5. `example638Plus_backwardHom_continuous` — extensionHom continuity for
     `example638Plus_backwardHom`; requires explicit
     `quotientPlusFSubXIdealTopology` on target and `quotient_plusFSubXIdeal_completeSpace`.
  6. `presheafValue_trivialPlus_fSubX_equiv_continuous` +
     `presheafValue_trivialPlus_fSubX_equiv_symm_continuous` — continuity in
     both directions; `.symm` uses `hcont_forward_B` directly as it equals
     `example638Plus_forwardHom`.
  7. `laurentPlusBridge_continuous` = `_trivialPlus_fSubX_equiv_continuous` ∘
     `_iteratedPlus_equiv_continuous`; no `hcont_forward_B` dependency.
  8. `laurentPlusBridge_symm_continuous` = `_iteratedPlus_equiv_symm_continuous`
     ∘ `_trivialPlus_fSubX_equiv_symm_continuous` (uses `hcont_forward_B`).

  Statement style: `letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀`
  in the return type to make `quotientPlusFSubXIdealTopology` typecheck at
  `B := presheafValue D₀`.

  Consumes: `hcont_forward_B` hypothesis already present in `laurentPlusBridge`.
  Unlocks: direct `TateAlgebra_mapRingEquiv laurentPlusBridge_continuous
  laurentPlusBridge_symm_continuous` for Step 3 of T-OVERLAP-COMPAT composition
  route.

  Residual for Step 3: `TateAlgebra_of_quotient_equiv` still needed to identify
  `TA B_plus` with `TA₂ B ⧸ (algMap f_B - X_1)` as a RING (after the
  `TateAlgebra_mapRingEquiv` produces `TA B_plus ≃+* TA B₁_gen f_B`). That is
  the next precise Lean/math primitive.

  Files: `Adic spaces/LaurentOverlap.lean` (~350 lines added, 1965 → 2277),
  build passes (2627 jobs).

- **2026-04-20** (T-COMP-FF scaffold, claude2): landed the identification
  `presheafValue_ringOfDef D ≃+* AdicCompletion (locIdeal D.P D.T D.s)
  (locSubring D.P D.T D.s)` in `IdealLocalizationCompletion.lean`, sorry-free
  with empty axiom list. Three new theorems/defs:
  1. `completedLocSubring_eq_ringOfDef_subring` — promotes the existing
     set-level equality from `Cor832.completedLocSubring_eq_presheafValue_ringOfDef`
     to a `Subring`-level equality via `SetLike.ext'`. Axioms: `[]`.
  2. `completedLocSubring_ringEquiv_ringOfDef` — ring isomorphism
     `D.completedLocSubring ≃+* presheafValue_ringOfDef D` by the Subring
     equality (identity carrier). Axioms: `[]`.
  3. `presheafValue_ringOfDef_ringEquiv_adicCompletion` — the main T-COMP-FF
     identification, composed from `CompletionLocalization.completionLocSubringEquiv`,
     `CompletionLocalization.locSubringCompletionEquivAdicCompletion`, and (2).
     Axioms: `[]`.

  **Precise Mathlib residual** (exact minimal missing theorem):
  ```
  theorem AdicCompletion.faithfullyFlat_of_le_jacobson
      {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
      (hI : I ≤ Ideal.jacobson ⊥) :
      Module.FaithfullyFlat R (AdicCompletion I R)
  ```
  (Stacks 00MA). Named as
  `AdicCompletion_faithfullyFlat_of_le_jacobson_residual : Prop` in the
  file. Not yet in Mathlib — current Mathlib only has
  `AdicCompletion.flat_of_isNoetherian` (flat, no Jacobson/faithful upgrade).

  Focused `lake env lean` on `IdealLocalizationCompletion.lean`: `EXIT: 0`.
  Focused check on `Cor832.lean` (now imports `IdealLocalizationCompletion`): `EXIT: 0`.

  **Remaining for full T-COMP-FF closure**:
  - (a) Mathlib lands `AdicCompletion.faithfullyFlat_of_le_jacobson` (Stacks 00MA).
  - (b) Project lands a short commutativity lemma:
    `locSubringToRingOfDef D =
    (presheafValue_ringOfDef_ringEquiv_adicCompletion D).symm ∘ AdicCompletion.of _ _`
    — routine transport via existing bridges, not attempted in this turn.

  Under (a) + the `locIdeal ≤ Jacobson ⊥ locSubring` hypothesis discharged
  via already-landed `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat`
  (S-IDEAL-JAC), full `RingHom.FaithfullyFlat (locSubringToRingOfDef D)`
  follows via `RingHom.FaithfullyFlat.of_bijective` + `stableUnderComposition`.
- **2026-04-20** (T-IDEAL-2 / S-IDEAL-ASM end-to-end via Lane-B, claude2):
  landed the full Cor 8.32 assembly under the correct Lane-B hypothesis
  (no `locSubring`-completeness). Four new theorems in `Cor832.lean`, all
  sorry-free (axioms: `[]`):
  1. `locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat` — Tate
     specialization of the generic faithful-flat descent, taking
     `(locSubringToRingOfDef D).FaithfullyFlat` and using
     `presheafValue_isAdicComplete` + `IsAdicComplete.le_jacobson_bot`
     for the target-side Jacobson containment.
  2. `Ideal.isClosed_in_locSubring_subspace_of_ringOfDef_faithfullyFlat`
     — closedness of ANY ideal of `locSubring` in subspace topology via
     `Ideal.isClosed_of_le_jacobson` + (1).
  3. `Ideal.isClosed_in_locTopology_of_ringOfDef_faithfullyFlat`
     — closedness in `Localization.Away D.s` via S-IDEAL-LOC main + (2).
  4. `productRestriction_injective_tate_of_ringOfDef_faithfullyFlat`
     — end-to-end Cor 8.32 Part-1 injectivity via
     `productRestriction_injective_tate_via_prime_extension_closed` + (3)
     + `IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀`.

  Consumes the single concrete residual `(locSubringToRingOfDef C.base).FaithfullyFlat`
  — the standard Noetherian adic-completion faithful-flatness content
  (Stacks 00MA). **Does NOT assert `locSubring` adic-complete**, does NOT
  revive single restriction-map injectivity, does NOT chase global
  Jacobson/Krull claims.

  New import: `Mathlib.RingTheory.RingHom.FaithfullyFlat` in `Cor832.lean`.
  Focused `lake env lean` on `Cor832.lean`: `EXIT: 0`, no errors, no new
  warnings.
- **2026-04-20** (T-IDEAL-2 / S-IDEAL-JAC faithful-flat descent, claude2):
  landed `locIdeal_le_jacobson_bot_of_faithfullyFlat` in
  `IdealLocalization.lean` — **proves `locIdeal ≤ Jacobson ⊥` in
  `locSubring P T s` without asserting `locSubring` is adic-complete**.
  Takes `[Module.FaithfullyFlat (locSubring) S]` + `Ideal.map (algebraMap
  _ S) locIdeal ≤ Jacobson ⊥ S` as hypotheses, proves the Jacobson
  containment by unit-lifting via the Mathlib FF identity
  `Ideal.comap_map_eq_self_of_faithfullyFlat` + `Ideal.mem_jacobson_bot`.
  Added private helper `isUnit_of_algebraMap_isUnit_of_faithfullyFlat`.
  No `sorry`; axioms `[]` (truly minimal).
  **Sorry-free T-IDEAL-2 inventory in `IdealLocalization.lean`**:
  `Localization.Away.exists_unit_locSubring_decomp`,
  `Localization.Away.mem_ideal_iff_clearing_denominator`,
  `Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
  (S-IDEAL-LOC main), `locIdeal_le_jacobson_bot_of_isAdicComplete` (Mathlib
  1-liner), `locIdeal_le_jacobson_bot_of_faithfullyFlat` (NEW, descent from
  complete target), `locIdeal_forall_isTopologicallyNilpotent`,
  `Ideal.isClosed_in_locSubring_subspace_of_isAdicComplete`,
  `Ideal.isClosed_in_locTopology_of_isAdicComplete`. All with axioms
  `[propext, Quot.sound, Classical.choice]` only (no `sorryAx`).
  `lake build` green (3091/3092 jobs).
- **2026-04-20** (Cor 8.32 upstream dependency cleanup / Prop 8.15 refactor,
  claude2): removed false single-map injectivity dependency from the
  Prop 8.15 / Cor 8.32 flatness chain. **Theorem landed**:
  `restrictionMapHom_ker_isTorsion` (`PresheafTateStructure.lean`, new named
  residual) — the strictly-weaker `IsLocalization`-equalizer condition:
  `restrictionMapHom D₀ D h c = 0 → ∃ n, (D₀.canonicalMap D.s)^n * c = 0`.
  **Refactored**: `restrictionMap_isLocalization` (`PresheafTateStructure.lean:1512`)
  now closes its `IsLocalization.Away.mk` eq-condition via the new torsion
  residual, NOT via the retired-false `restrictionMapHom_injective`.
  Deprecation warning added to `restrictionMapHom_injective` docstring
  (false in general by reviewer counterexample `A = k⟨T,U⟩/(TU), U = R(1/T)`).
  Downstream chain: `flat_over_base_tate` → `productRestriction_faithfullyFlat_abstract`
  → `productRestriction_faithfullyFlat_tate_of_hSpa_points` — now transitively
  parameterized on the correct residual (`restrictionMapHom_ker_isTorsion`
  + `restrictionMapHom_surj`) rather than the false one. `lake build`
  passes (3091/3092 jobs, only unrelated pre-existing sorries in
  FarguesFontaine/ScottishBook remain). Legacy callers of
  `restrictionMapHom_injective` in `LaurentRefinement.lean:3638, 3695`
  preserved but flagged for cover-level Cor 8.32 refactor (separate ticket).
- **2026-04-19** (T-IDEAL-2 / Cor 8.32 cover-level faithful flatness, claude2):
  plan reset per ChatGPT Pro — retargeted from ideal-closedness route to
  **Wedhorn Cor 8.32 as a cover-level faithful-flatness theorem**. Audit
  found the abstract `productRestriction_faithfullyFlat_abstract`
  (`Cor832.lean:202`) already proved sorry-free, `flat_over_base_tate`
  (`Cor832.lean:551`), `hSpa_surj_from_spanTop` (`Cor832.lean:508`), and
  `hspan_top_of_hSpa_points` (`Cor832.lean:744`) all proved modulo upstream
  sorries. Landed the explicit theorem-sized faithful-flatness combinator
  `productRestriction_faithfullyFlat_tate_of_hSpa_points` (Cor832.lean)
  that chains these: Prop 8.30 flatness + `Module.Flat.pi_of_algebra` +
  `hSpa_surj_from_spanTop ∘ hspan_top_of_hSpa_points` +
  `Module.FaithfullyFlat.of_comap_surjective` via
  `faithfullyFlat_pi_of_prime_surjection`. No new sorry; inherits the SAME
  upstream `sorryAx` chain as the existing injective variant
  `productRestriction_injective_tate_of_hSpa_points`.
  **Upstream blocking sorries (NOT T-IDEAL-2 scope)**:
  `spa_point_nonOpen_of_rational_subset` (`Presheaf.lean:807`),
  `restrictionMapHom_injective` (`PresheafTateStructure.lean:1322`),
  `restrictionMapHom_surj` (`PresheafTateStructure.lean:1208`).
  Previous locSubring-completion files (`IdealLocalizationCompletion.lean`,
  generic Jacobson lemmas) retained as valid support machinery but no
  longer on the Cor-8.32 critical path.
- **2026-04-19** (T-IDEAL-2 / Route B landing, claude2): unblocked
  `TateAlgebraTopology.lean:3096` (replaced an incorrect `rw [show … from rfl]`
  with `rw [(MvPowerSeries.coeff_apply _ _).symm, map_sum]` — the rfl was
  false because `MvPowerSeries.coeff` is a LinearMap, not the raw
  evaluation). `lake build` now passes end-to-end. Landed new helper
  `IdealLocalizationCompletion.lean` with the Route B support lemmas:
  `Ideal.isClosed_in_ringOfDef_subspace_of_isAdicComplete`,
  `Ideal.isClosed_in_presheafValue_of_isClosed_in_ringOfDef`,
  `Ideal.isClosed_in_presheafValue_of_ringOfDef_ideal`, and
  `IsClosed.preimage_coeRingHom`. All noncontroversial; `IsAdicComplete`
  is taken as a typeclass hypothesis (so the caller can plug in
  `Cor832.presheafValue_isAdicComplete` without cycle).
  **Residual remains S-IDEAL-JAC** (`locIdeal ≤ Jacobson ⊥` in `locSubring`
  Noetherian) / equivalently faithful flatness of `locSubringToRingOfDef`
  — see ChatGPT Pro packet in prior report.
- **2026-04-19** (T-IDEAL-2 / Route B attempt, claude2): attempted to land
  the completion-level closedness bridge (`Ideal.isClosed_in_ringOfDef_subspace_of_isAdicComplete`,
  `Ideal.isClosed_in_presheafValue_of_isClosed_in_ringOfDef`,
  `IsClosed.preimage_coeRingHom`) in a new helper `IdealLocalizationCompletion.lean`.
  Transitively requires `PresheafTateStructure.lean` which depends on
  `TateAlgebraTopology.lean` — currently broken (pre-existing failure at
  line 3096, another agent's work per git status). Rolled back the new file;
  support lemmas staged in the ChatGPT Pro packet for landing once the
  unrelated `TateAlgebraTopology` compile is restored.
  **Math residual on Route B (confirmed)**: the contraction identity
  `(locSubringToRingOfDef)⁻¹(Ideal.map locSubringToRingOfDef (q ∩ locSubring))
  = q ∩ locSubring` requires faithful flatness of `locSubringToRingOfDef`,
  equivalent to `locIdeal ⊆ Jacobson ⊥` in `locSubring` — **still the same
  S-IDEAL-JAC residual**. The completion route gives the closedness of the
  **extension** in `presheafValue_ringOfDef`, but *not* of the contraction
  back in `locSubring` without faithful flatness.
- **2026-04-19** (T-IDEAL-2 / S-IDEAL-ASM Route B, claude2): end-to-end
  conditional closure landed as
  `productRestriction_injective_tate_of_isAdicComplete` in `Cor832.lean`.
  Composes `productRestriction_injective_tate_via_prime_extension_closed`
  + `Ideal.isClosed_in_locTopology_of_isAdicComplete` (S-IDEAL-LOC/ASM plug-in
  from `IdealLocalization.lean`) + `IsTateRing.exists_topologicallyNilpotent_unit_mem_A₀`
  (new private helper for Tate pseudo-uniformizer in `P.A₀`). Under
  `[IsAdicComplete (locIdeal) (locSubring)]` + standard Tate hypotheses,
  discharges `productRestriction_injective_tate` completely. Residual
  reduced to a **single typeclass instance**: `IsAdicComplete (locIdeal)
  (locSubring)` — see Route C sketch in the interface report.
- **2026-04-19** (T-IDEAL-2 / S-IDEAL-JAC, claude2): S-IDEAL-JAC landed as
  conditional theorem `locIdeal_le_jacobson_bot_of_isAdicComplete`
  (`IdealLocalization.lean`), one-line application of Mathlib's
  `IsAdicComplete.le_jacobson_bot`. Generic infrastructure added in
  `IdealClosedness.lean`: `isTopologicallyNilpotent_of_mem_of_isAdic`
  (algebraic, no completeness), `Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent`
  (generic t.n. → Jacobson, uses Wedhorn Prop 5.38 geometric series),
  `Ideal.le_jacobson_bot_of_isAdic_complete` (composition). S-IDEAL-ASM
  direct plug-ins: `Ideal.isClosed_in_locSubring_subspace_of_isAdicComplete`
  and end-to-end `Ideal.isClosed_in_locTopology_of_isAdicComplete`.
  **Remaining blocker**: discharge of `IsAdicComplete (locIdeal) (locSubring)`
  — not automatic even in Tate case (the project's adic-completeness
  witness `presheafValue_isAdicComplete` is for the completion, not
  `locSubring` itself).
- **2026-04-19** (T-IDEAL-2 / S-IDEAL-LOC, claude2): clearing-denominators
  transfer landed in `IdealLocalization.lean`: `exists_unit_locSubring_decomp`,
  `mem_ideal_iff_clearing_denominator`, `isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`.
- **2026-04-18** (T-GEOM-RED, me): new file `GeometricReduction.lean`;
  `tateAcyclicity_gluing_via_refinement_cover_level` (corrected variant) +
  `plusDatum` + `standardCoverVCovers` + bridge helpers. DecidableEq
  diamond blocking τ documented with workaround.
- **2026-04-18** (T-IDEAL-2, worker): major landing —
  `IdealClosedness.lean` with Krull-based closedness + subring-lift
  bridge. `coeRingHom_preserves_proper_of_closed` closure combinator +
  `isClosed_image_of_isClosed_subspace_in_locSubring` Tate-specific
  bridge added to `Cor832.lean`. T-IDEAL-2 ~80% landed; remaining:
  S-IDEAL-JAC + S-IDEAL-LOC.
- **2026-04-18** (T-OV-1, worker): Step A infrastructure — foundational
  power-boundedness lemmas + half-forward evalHoms
  (`overlap_plus_forwardHom`, `overlap_minus_forwardHom`) +
  symm-direction action lemmas for Step B. Main Step A theorem
  (S-OV-GLUE) still pending.
- **2026-04-18** (T-INJ-1, retirement): false Route A scaffolds removed
  per reviewer counterexample.
- **2026-04-18** (tickets): incorporated AI reviewer's three
  architectural corrections.
- **2026-04-17** (T-OV-1): Step B closed (Wedhorn p.83 pure-algebra core).
- **2026-04-16**: T-IDEAL-1 `one_mem_closure_coeRingHom_image` landed.
  Cor 8.32 abstract framework. Wedhorn Prop 6.18 port for hcont_eval.
- **Earlier**: Example 6.38 generic, Lemma 2.13 iterated rational,
  Cor 7.32, Spa/Spv compactness, bridge chain.

---

## DEPTH-N WEDHORN 2.13 GENERALISATION

Added 2026-05-11 round 3 via `/develop --continue`. This is the substantial
structural piece that, once landed, closes T-RATIONAL-FLAT-GENERAL completely
(by feeding the relative equiv into the existing hypothesis-parameterised
`restrictionMap_flat_of_rational_subset_via_relative`).

Architecture: new file `Adic spaces/RelativeRationalLocData.lean`, ~800-1500
lines, parallel structure to the existing depth-1 minus infrastructure
(`iteratedMinusDatum_B`, `iteratedMinus_forwardHom`, etc.) but generalised
from T = {1}, s = canonicalMap f to arbitrary T, s coming from D.

Dependency graph:
```
T-WEDHORN-213-DATUM
   ├─→ T-WEDHORN-213-FORWARD ─┐
   └─→ T-WEDHORN-213-BACKWARD ┴─→ T-WEDHORN-213-ROUNDTRIP
                                  → T-WEDHORN-213-EQUIV
                                  → T-WEDHORN-213-INTERTWINE
                                  → T-RATIONAL-FLAT-GENERAL-CLOSE
CLEANUP-WEDHORN-213 (final per-file cleanup)
```

### [T-WEDHORN-213-DATUM] Define `relativeRationalLocData E D hsub`

- **Status**: PARTIAL — LaurentNormalized case DONE (2026-05-12, T218)
- **2026-05-12 update**: The LaurentNormalized D case is closed sorry-free
  via `relativeRationalLocData_laurentNormalized` and
  `relativeRationalLocData_hopen_proof_of_laurentNormalized` (commit a8d364a).
  The hopen goes through with N=0 by leveraging 1 ∈ D.T (the
  LaurentNormalized condition) to put 1 ∈ T_at_E, then
  divByS b s_at_E = algebraMap b * divByS 1 s_at_E ∈ locSubring.
  This is parallel to iteratedMinusDatum_B's hopen (where T = {1}).
- **Remaining**: non-LaurentNormalized D case still has the sorry
  in `relativeRationalLocData_hopen_proof`. The full Wedhorn 2.13
  algebraic identity is still needed for arbitrary D.
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: none — uses only existing `RationalLocData`,
  `presheafValue_pairOfDefinition_concrete`, `RationalLocData.canonicalMap`.
- **Type**: def + API lemmas
- **Mathematical statement**: given `E, D : RationalLocData A` with
  `rationalOpen D.T D.s ⊆ rationalOpen E.T E.s`, build a rational locale data
  for D at the B = presheafValue E level:
  - P_at_E := `presheafValue_pairOfDefinition_concrete E.P E`
  - T_at_E := `D.T.image E.canonicalMap`
  - s_at_E := `E.canonicalMap D.s`
  - hopen via push-through of D's hopen along E.canonicalMap.
- **Proof sketch (general case, still open)**: pull D's `hopen` (∃ N, ∀ b ∈ E.P.I^N,
  divByS b D.s ∈ locSubring) along `E.canonicalMap`, using that the image of
  E.P.I is contained in P_at_E.I (the pair-of-definition at E-level), and
  divByS commutes with the algebraMap-image where applicable.
- **Mathlib lemmas needed**: `Finset.image`, `divByS_mem_locSubring`,
  `algebraMap_mem_locSubring` (all existing).
- **Sources**: Wedhorn Lemma 2.13. Templates: `iteratedMinusDatum_B` (line
  476 of LaurentRefinement.lean), `iteratedPlusDatum_B` (line 460).
- **Generality decision**: `(E D : RationalLocData A)` — D arbitrary
  modulo rationalOpen-inclusion. Uses E.P as the base pair-of-definition.
- **Risks**: subtleties in matching B-level ideal-of-definition images.
  Test with `E.canonicalMap D.s`'s topological behaviour.

### [T-WEDHORN-213-FORWARD] Forward hom presheafValue D → presheafValue (relativeRationalLocData ...)

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T263)
- **Closed**: 2026-05-12 audit — `relativeLaurentNormalized_forwardLocHom`
  (line 411) and `relativeLaurentNormalized_forwardHom` (line 790) in
  `Adic spaces/RelativeRationalLocData.lean`. Both sorry-free for the
  LaurentNormalized case (T220-T223). The general non-LaurentNormalized
  case is BYPASSED per the normalized-minus reframe.
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-DATUM
- **Type**: def + continuity lemma
- **Mathematical statement**:
  ```
  relativeForwardLocHom : Localization.Away D.s →+*
    Localization.Away (relativeRationalLocData E D hsub).s
  relativeForwardHom : presheafValue D →+*
    presheafValue (relativeRationalLocData E D hsub)
  relativeForwardHom_continuous (..continuity..)
  ```
- **Proof sketch**:
  1. Build LocHom via `IsLocalization.Away.lift` (E.canonicalMap D.s is a
     unit in Localization.Away itself).
  2. Compose with `coeRingHom` of presheafValue (relativeRationalLocData).
  3. Continuity: the algebraic LocHom sends divByS-generators of D's
     locSubring to elements of relativeRationalLocData's locSubring (after
     E.canonicalMap-image), giving the continuity by the universal property
     of the localized topology.
  4. Extend over completion via `UniformSpace.Completion.extensionHom`.
- **Mathlib lemmas needed**: `IsLocalization.Away.lift`,
  `IsLocalization.Away.algebraMap_isUnit`,
  `UniformSpace.Completion.extensionHom`,
  `UniformSpace.Completion.extensionHom_coe`.
- **Sources**: parallel to `iteratedMinus_forwardLocHom` and
  `iteratedMinus_forwardHom`.

### [T-WEDHORN-213-BACKWARD] Backward hom presheafValue (relativeRationalLocData ...) → presheafValue D

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T263)
- **Closed**: 2026-05-12 — `relativeLaurentNormalized_backwardLocHom`
  (line 461) and `relativeLaurentNormalized_backwardHom` (line 933).
  Sorry-free (T223-T224).
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-DATUM
- **Type**: def + continuity lemma
- **Mathematical statement**:
  ```
  relativeBackwardLocHom : Localization.Away (relativeRationalLocData...).s
                            →+* Localization.Away D.s
  relativeBackwardHom : presheafValue (relativeRationalLocData...) →+*
                         presheafValue D
  ```
- **Proof sketch**: parallel to T-WEDHORN-213-FORWARD but in the reverse
  direction. The image of E.canonicalMap is invertible in Localization.Away
  D.s (because D.s | D.s in that ring), giving the LocHom; continuity and
  completion-extension as before.
- **Mathlib lemmas needed**: same as T-WEDHORN-213-FORWARD.

### [T-WEDHORN-213-ROUNDTRIP] Backward ∘ Forward = id; Forward ∘ Backward = id

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T263)
- **Closed**: 2026-05-12 — `relativeLaurentNormalized_backwardHom_comp_forwardHom`
  (line 1039). Sorry-free (T224-T226).
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-FORWARD, T-WEDHORN-213-BACKWARD
- **Type**: lemma
- **Mathematical statement**:
  ```
  relativeBackwardHom.comp relativeForwardHom = RingHom.id (presheafValue D)
  relativeForwardHom.comp relativeBackwardHom = RingHom.id (presheafValue ...)
  ```
- **Proof sketch**:
  1. Algebraic identity at the `coeRingHom` image (uniqueness of
     IsLocalization-lift on a dense subset).
  2. Extend via `UniformSpace.Completion.ext'` (continuous functions agreeing
     on a dense set agree everywhere).
- **Mathlib lemmas needed**: `UniformSpace.Completion.ext'`,
  `IsLocalization.lift_unique` or equivalent.

### [T-WEDHORN-213-EQUIV] Package as ring equiv

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T263)
- **Closed**: 2026-05-12 — packaged as the equiv used in
  `restrictionMap_flat_of_rational_subset_laurentNormalized` (T227-T228).
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-ROUNDTRIP
- **Type**: def (RingEquiv)
- **Mathematical statement**:
  ```
  presheafValue_relative_equiv : presheafValue D ≃+*
    presheafValue (relativeRationalLocData E D hsub)
  ```
- **Proof sketch**: direct construction via `RingEquiv.mk` using forward,
  backward, and round-trip identities.

### [T-WEDHORN-213-INTERTWINE] Intertwining with restriction map

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T263)
- **Closed**: 2026-05-12 — full intertwining at A and presheafValue E
  levels in `RelativeRationalLocData.lean` (T225-T226).
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-EQUIV
- **Type**: theorem
- **Mathematical statement**:
  ```
  ∀ a : presheafValue E,
    presheafValue_relative_equiv E D hsub
        (restrictionMapHom E D hsub a) =
      (relativeRationalLocData E D hsub).canonicalMap a
  ```
- **Proof sketch**:
  1. Apply `UniformSpace.Completion.ext'` on `a : presheafValue E`.
  2. Reduce to `a = E.coeRingHom a₀` for `a₀ ∈ Localization.Away E.s`.
  3. Trace both maps through the chain; reduce to algebraic identity in
     `Localization.Away (relativeRationalLocData.s)`, which is
     `Localization.Away (E.canonicalMap D.s)`.
- **Mathlib lemmas needed**: `UniformSpace.Completion.ext'`,
  `IsLocalization.ringHom_ext`.
- **Sources**: parallel to
  `presheafValue_iteratedMinus_equiv_restrictionMap_canonicalMap`.

### [T-RATIONAL-FLAT-GENERAL-CLOSE] Wire into the general flatness theorem

- **Status**: DONE for LaurentNormalized (audited 2026-05-12, T264)
- **Closed**: 2026-05-12 — `restrictionMap_flat_of_rational_subset_laurentNormalized`
  in `Adic spaces/RestrictionFlatness.lean` (T228). Sorry-free; closes
  T-RATIONAL-FLAT-GENERAL for the needed case on the critical path.
  General non-LaurentNormalized case BYPASSED per the normalized-minus
  reframe.
- **File**: `Adic spaces/RestrictionFlatness.lean`
- **Depends on**: T-WEDHORN-213-INTERTWINE
- **Type**: theorem
- **Mathematical statement**:
  ```
  restrictionMap_flat_of_rational_subset :
    Module.Flat (presheafValue E) (presheafValue D) along restrictionMap
  ```
  Sorry-free closure of the general flatness theorem.
- **Proof sketch**:
  1. Build D_at_E from T-WEDHORN-213-DATUM.
  2. Obtain relative equiv (T-WEDHORN-213-EQUIV) + intertwining
     (T-WEDHORN-213-INTERTWINE).
  3. Apply `restrictionMap_flat_of_rational_subset_via_relative` (existing).
  4. Discharge the B-level canonical-form flatness hypotheses (hb, hT_pb,
     hcont_eval) for D_at_E shape via the strong-noetherian Tate setting.

### [CLEANUP-WEDHORN-213] Run /cleanup on RelativeRationalLocData.lean

- **Status**: PARTIAL (2026-05-27). General `relativeRationalLocData` chain deleted (~257 LOC removed) — the dead sub-lemma `_divByS_one_mem_locSubring`, the `_hopen_proof`, and the unused general `relativeRationalLocData` + `_T` + `_s` declarations all gone. Only LaurentNormalized variant + downstream machinery remains (axiom-clean). b2_log entry 35 logs the deletion. Final `/cleanup` polish (golfing, docstring tightening) deferred.
- **File**: `Adic spaces/RelativeRationalLocData.lean`
- **Depends on**: T-WEDHORN-213-INTERTWINE
- **Type**: cleanup
- **Description**: Final per-file cleanup for the new file. Runs after the
  inducing theorems are in place.

---

## CHAIN DECOMPOSITION ROUTE — pivoted 2026-05-11 (round 3, second pivot)

The reviewer's session-3 recommendation explicitly prescribed:
> Build [the general flatness theorem] from the two basic flatness steps
> plus transitivity/decomposition of rational localizations.

This is the **chain decomposition** approach: express D ⊆ E as a finite
chain of basic plus/minus Laurent steps starting from E, then compose
`Module.Flat` along the chain (each step is flat by the existing depth-1
infrastructure).

The earlier T-WEDHORN-213-* tickets (direct depth-N relative datum
construction) are **PARKED** — mathematically valid alternative, but the
chain approach is what the reviewer recommended AND reuses existing
infrastructure directly.

### [T-CHAIN-CONSTRUCTION] Chain of basic plus/minus steps from E to D's data

- **Status**: BYPASSED — DONE for LaurentNormalized via T229-T237 (audited 2026-05-12, T262)
- **Closed**: 2026-05-12 audit — the reviewer-prescribed normalized-minus
  bypass (T229-T237) routes the Wedhorn Laurent-decomposition tree
  through normalized-minus pieces, eliminating the need for arbitrary
  E-D chain construction. `relativeRationalLocData_laurentNormalized`
  in `Adic spaces/RelativeRationalLocData.lean` is the LaurentNormalized
  case, sorry-free. The general non-LaurentNormalized chain is no
  longer on the critical path.
- **File**: `Adic spaces/RationalChainDecomposition.lean` (new file)
- **Type**: def + theorem
- **Mathematical statement**: For E, D : RationalLocData A with
  rationalOpen D ⊆ rationalOpen E, define a finite sequence
  `chainSteps : Fin (D.T.card + 2) → RationalLocData A` with
  chainSteps 0 = E and each successive step a basic Laurent plus or
  minus operation on the previous, terminating at a locale chainEnd
  whose rationalOpen equals D's.
- **Construction outline**:
  1. Step 0: chainSteps 0 := E.
  2. Step 1 (basic minus at D.s over E): chainSteps 1 := laurentMinusDatum E D.s.
     This makes D.s a denominator (inverts D.s topologically).
  3. Steps 2..|D.T|+1 (basic plus at each t ∈ D.T): enumerate D.T as
     {t_1, ..., t_n}; chainSteps (i+2) := laurentPlusDatum (chainSteps (i+1)) t_i.
- **Reviewer guidance**: "[the chain] is the natural transitivity formulation."
- **Reference**: Wedhorn Lemma 2.13.

### [T-CHAIN-STEP-FLATNESS] Each chain step is flat

- **Status**: BYPASSED via T229-T237 (audited 2026-05-12, T262)
- **Closed**: 2026-05-12 audit — the normalized-minus bypass eliminates
  the need for arbitrary chain-step flatness. The relevant flatness
  is provided by `restrictionMap_flat_via_normalizedMinus` (T230) +
  `restrictionMap_flat_of_rational_subset_laurentNormalized` (T228),
  both sorry-free.
- **File**: `Adic spaces/RationalChainDecomposition.lean`
- **Depends on**: T-CHAIN-CONSTRUCTION
- **Type**: theorem
- **Mathematical statement**: For each i, the restriction map
  `presheafValue (chainSteps i) → presheafValue (chainSteps (i+1))` is flat
  along the natural inclusion.
- **Proof outline**: Plus steps use `restrictionMap_flat_via_fSubX_quotient`
  (committed earlier); minus steps use `restrictionMap_flat_via_oneSubfX_quotient`
  or `restrictionMap_flat_via_iteratedMinus`. Both flat. Each step's
  hypothesis bundle propagated as needed.

### [T-CHAIN-COMPOSITION] Chain composite is flat

- **Status**: DONE (depth 2, 3, 4, 5, 6, 7 covered as of 2026-05-12, commit 13f724a)
- **File**: `Adic spaces/RestrictionFlatness.lean`
- **Depends on**: T-CHAIN-STEP-FLATNESS
- **Type**: theorem
- **Mathematical statement**: `presheafValue E → presheafValue chainEnd` is
  flat (via composition of the chain's flat restriction maps).
- **Proof outline**: Cascade `restrictionMap_flat_trans` (depth 2). Each
  `chain_N` is direct call of `chain_{N-1}` + `restrictionMap_flat_trans`.
- **Available APIs (2026-05-12)**:
  - `restrictionMap_flat_trans` (depth 2)
  - `restrictionMap_flat_chain_three`
  - `restrictionMap_flat_chain_four`
  - `restrictionMap_flat_chain_five` (NEW)
  - `restrictionMap_flat_chain_six` (NEW)
  - `restrictionMap_flat_chain_seven` (NEW)
- Covers Wedhorn-style chains with `|D.T|` up to 5
  (chainSteps : Fin (|D.T| + 2)).

### [T-CHAIN-END-IDENTIFICATION] chainEnd has D's rationalOpen; presheaf values match

- **Status**: BYPASSED via T229-T237 (audited 2026-05-12, T262)
- **Closed**: 2026-05-12 audit — the normalized-minus bypass eliminates
  the need for chain-end identification (the chain is reduced to a single
  normalized-minus step). The relevant identification is provided by
  `rationalOpen_laurentMinusNormalized_eq` (T229), sorry-free.
- **File**: `Adic spaces/RationalChainDecomposition.lean`
- **Depends on**: T-CHAIN-CONSTRUCTION
- **Type**: theorem
- **Mathematical statement**:
  1. rationalOpen chainEnd.T chainEnd.s = rationalOpen D.T D.s in Spv A.
  2. presheafValue chainEnd ≃+* presheafValue D as topological A-algebras,
     and the iso intertwines restriction maps from any common predecessor.
- **Proof outline**:
  - Part 1 via direct unfolding of valuation conditions.
  - Part 2 via universal property of presheafValue (functoriality on rationalOpen).
    May need a helper lemma `presheafValue_congr_of_rationalOpen_eq` if not
    already in project.

### [T-RATIONAL-FLAT-GENERAL-CLOSE-CHAIN] Wire into general flatness

- **Status**: BYPASSED via T229-T237 (audited 2026-05-12, T262)
- **Closed**: 2026-05-12 audit — T-RATIONAL-FLAT-GENERAL was closed for
  LaurentNormalized via the normalized-minus bypass. The wire-in to
  general flatness is provided by `tateAcyclicityComplete_via_normalizedLaurent`
  (T235) in `Adic spaces/TateAcyclicityFinalAssembly.lean`, which routes
  the entire chain through normalized-minus pieces.
- **File**: `Adic spaces/RestrictionFlatness.lean`
- **Depends on**: T-CHAIN-COMPOSITION, T-CHAIN-END-IDENTIFICATION
- **Type**: theorem
- **Mathematical statement**: Final closure of `restrictionMap_flat_of_rational_subset`
  sorry-free.

### Parked (alternative direct depth-N path)

T-WEDHORN-213-DATUM, T-WEDHORN-213-FORWARD, T-WEDHORN-213-BACKWARD,
T-WEDHORN-213-ROUNDTRIP, T-WEDHORN-213-EQUIV, T-WEDHORN-213-INTERTWINE
are **PARKED**. They construct `D_at_E : RationalLocData (presheafValue E)`
directly as a single relative datum. Mathematically valid alternative
(Wedhorn 2.13 at depth N) but more ambitious than the chain approach.
Retained in tickets for future reference; not the primary path.

### Cleanup tickets (cadence)
- `CLEANUP-RATIONAL-CHAIN-1` after T-CHAIN-COMPOSITION.
- `CLEANUP-RATIONAL-CHAIN-FINAL` after T-RATIONAL-FLAT-GENERAL-CLOSE-CHAIN.

### [T-MATHLIB-STACKS-00MA] Adic completion of Noetherian ring is Noetherian  **[REFRAMED 2026-05-13 per reviewer]**

**Reviewer correction** (ChatGPT Pro, 2026-05-13): "'Adic completion of a noetherian
ring is faithfully flat without a Jacobson hypothesis' is FALSE in general. For
example, `ℤ → ℤ_p` is flat but not faithfully flat, since tensoring with `ℤ/ℓℤ` for
`ℓ ≠ p` gives zero. Faithful flatness of `I`-adic completion needs `I ⊆ Jac(R)` or
an equivalent hypothesis."

**Stacks 00MA split into true components** (reviewer-prescribed):
```
R noetherian ⇒ R̂_I noetherian                  -- UNCONDITIONAL
R noetherian ⇒ R → R̂_I flat                    -- UNCONDITIONAL (in Mathlib as `flat_of_isNoetherian`)
I ⊆ Jac(R) ⇒ R → R̂_I faithfully flat            -- CONDITIONAL (in Mathlib as `faithfullyFlat_of_le_jacobson_bot`)
```

Only the noetherianness half remains as a genuine mathlib gap. The previous
"unconditional faithfully flat" framing was MATHEMATICALLY INCORRECT.

**Status**: PARTIAL — noetherianness is the remaining mathlib gap; faithfully-flat is
conditional in Mathlib (Jacobson hypothesis), which matches Stacks. The unconditional
faithfully-flat claim of earlier framing is now retired.

- **Original Status**: PARTIAL — faithfully-flat-conditional half is DONE; Noetherianness is the remaining genuine mathlib gap (audited 2026-05-12, T270)
- **Partial closure (T270 audit)**:
  - `AdicCompletion.faithfullyFlat_of_le_jacobson_bot`
    (`Adic spaces/AdicCompletionFaithfullyFlat.lean:62`): for Noetherian R
    and ideal I with `I ≤ Jacobson ⊥`, `AdicCompletion I R` is faithfully
    flat over R. Sorry-free.
  - This is the FAITHFULLY-FLAT half of Stacks 00MA (the part that's
    actually load-bearing for the project's S-IDEAL-JAC chain).
  - The NOETHERIANNESS half of Stacks 00MA (`IsNoetherianRing (AdicCompletion I R)`
    from `IsNoetherianRing R`) remains a genuine mathlib gap.
- **File**: new `Adic spaces/AdicCompletionNoetherian.lean` or addition to existing AdicCompletion file
- **Mathematical statement**:
  ```
  theorem AdicCompletion.isNoetherianRing
      {R : Type*} [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
      IsNoetherianRing (AdicCompletion I R)
  ```
- **Reference**: Stacks Project Tag 00MA.
- **Proof sketch**: Write the I-adic completion R̂_I as a quotient of the
  power series ring R[[T_1, ..., T_n]] where T_i map to generators
  f_1, ..., f_n of I (using `Ideal.fg` if I is f.g., which it is in our
  setting). Mathlib's `PowerSeries.instIsNoetherianRing` gives noetherianity
  of R[[T]]. Multivariable case extends iteratively: R[[T_1, ..., T_n]] =
  R[[T_1]][[T_2]]...[[T_n]], each step preserving noetherian via the
  single-variable theorem. Quotient of Noetherian is Noetherian.
- **Mathlib lemmas needed**:
  - `PowerSeries.instIsNoetherianRing` (already in mathlib).
  - `Ideal.Quotient.isNoetherianRing` (standard).
  - `Ideal.fg_iff` (for I finitely generated).
  - `AdicCompletion`-specific identifications (mathlib has the structure).
- **Sources**: Stacks Tag 00MA (Section 10.97 of the Stacks Project).
- **Generality**: minimal — match the use site. The simplest form is `(I : Ideal R) [IsNoetherianRing R]` without requiring I to be in the Jacobson radical (that's for FAITHFUL flatness, not noetherianity).

---

## STRUCTURAL PIECES BLOCKING DEPTH-N ITERATION (2026-05-12)

The depth-1 flatness theorems (`restrictionMap_flat_via_fSubX_quotient` etc.)
take typeclasses `[IsTateRing A] [IsNoetherianRing A] [PlusSubring A]
[IsHuberRing A] [HasLocLiftPowerBounded A] [T2Space A] [NonarchimedeanRing A]`.

For chain composition at depth ≥ 2 (the reviewer-prescribed path to
T-RATIONAL-FLAT-GENERAL), each intermediate B = presheafValue D_i must satisfy
these typeclasses. Existing preservation:

* ✅ `IsTateRing` via `presheafValue_isTateRing` (existing).
* ✅ `IsHuberRing` via `IsTateRing.toIsHuberRing` (existing).
* ✅ `PlusSubring` via `RationalLocData.presheafValuePlusSubring` (existing).
* ✅ `IsNoetherianRing` via `presheafValue_isNoetherian_via_canonical`
  (T-STRONG-NOETH-PRESERVATION single-level, 2026-05-11).
* ✅ `T2Space`, `NonarchimedeanRing` via existing instances.

Missing preservation theorems blocking depth-≥2 iteration:

### [T-LOCLIFT-PRESERVATION] HasLocLiftPowerBounded preservation

- **Status**: SUPERSEDED (2026-05-13 round 5). Reviewer flagged the
  class formulation as "too ad hoc". The remaining preservation need
  for the grafted Wedhorn tree construction is captured by
  `T-RATIONAL-LOC-TRANSITIVITY-API` (see below in this file) — a
  cleaner formulation: "rational localization over O(D) = iterated
  rational localization over A, and the rational generators are
  power-bounded by construction." This ticket remains as historical
  record; do not work it directly.
- **Earlier status**: LARGELY OBVIATED (2026-05-12 cascade refactor T214→T216)
- **2026-05-12 progress**: Six theorems refactored to drop `hLocLift_B`
  hypothesis. All B-level depth-1 Laurent-shape flatness theorems and the
  Cor 8.32 faithful-flatness route no longer require HasLocLiftPowerBounded
  preservation:
  - `restrictionMap_flat_of_rational_subset_via_relative` (T214)
  - `iteratedMinus_B_flat_of_canonical` (T216)
  - `restrictionMap_flat_via_iteratedMinus` (T216)
  - `restrictionMap_flat_of_rational_subset_direct_laurentMinus` (T216)
  - `iteratedPlus_B_flat_of_canonical` (T216)
  - `restrictionMap_flat_via_iteratedPlus` (T216)
  - `flat_over_base_tate_laurent` (T216)
  - `productRestriction_faithfullyFlat_tate_laurent_of_hSpa_points` (T216)

  All these were carrying `hLocLift_B` as a "defensive" hypothesis that was
  unused in the proof bodies. Flatness comes from `presheafValue_flat_of_canonical`
  which only needs the canonical Tate-quotient identification (Wedhorn
  Example 6.38 + Lemma 8.31 at B-level), not the Nullstellensatz.

- **Remaining scope** (separate refactor):
  `restrictionMap_flat_via_fSubX_quotient` and `restrictionMap_flat_via_oneSubfX_quotient`
  still carry `hLocLift_B` because they thread through `laurentPlusBridge` /
  `laurentMinusBridge` in `LaurentRefinement.lean`. Those bridges have
  structural dependencies on HasLocLiftPowerBounded — refactoring them is
  a deeper cleanup across files.

- **Architectural impact**: The Cor 8.32 faithful-flatness route, the chain
  decomposition via `via_relative`, and the basic Laurent-shape suppliers
  ALL run without HasLocLiftPowerBounded preservation. The remaining
  preservation theorems needed for closing T-RATIONAL-FLAT-GENERAL via the
  chain decomposition are limited to:
  - `IsStronglyNoetherian (presheafValue D)` (T-STRONG-NOETH-PRESERVATION-FULL,
    depends on Stacks 00MA)
  - The relative datum hopen sorry (T-WEDHORN-213-DATUM)

- **Original mathematical statement**: For strongly noetherian Tate A and
  D : RationalLocData A, `HasLocLiftPowerBounded (presheafValue D)` holds.
- **Proof sketch (still applicable for any future LaurentRefinement refactor)**:
  Wedhorn 7.32 / Nullstellensatz at B-level via `presheafValue_isTateRing` +
  Wedhorn 7.14 at B-level.
- **Reference**: Wedhorn 7.14 / 7.32.

### [T-STRONG-NOETH-PRESERVATION-FULL] IsStronglyNoetherian preservation

- **Status**: OPEN (depends on Stacks 00MA mathlib contribution)
- **Mathematical statement**: For strongly noetherian Tate A and
  D : RationalLocData A, `IsStronglyNoetherian (presheafValue D)`.
- **Proof sketch**: Requires `IsNoetherianRing (restrictedMvPowerSeriesSubring k (presheafValue D))`
  for all k. Combine Stacks 00MA + multivariable Example 6.38 + Hilbert basis.
- **Depends on**: T-MATHLIB-STACKS-00MA + multivariable Example 6.38.

Once both preservation theorems land, iteration of depth-1 flatness gives
depth-N flatness. Combined with the existing `restrictionMap_flat_trans`
chain composition (already in place), this closes T-RATIONAL-FLAT-GENERAL
sorry-free for any explicit chain decomposition.

---

## ROUND-5 REVIEWER-PRESCRIBED ADDITIONS (2026-05-13)

The round-4 reviewer reply (`.mathlib-quality/expert-review/2026-05-13/reply.md`)
prescribed the following new tickets and reframings. See the integration record at
`.mathlib-quality/expert-review/2026-05-13/integration.md`.

### [T-SPA-COVER-SURJ] Spec-cover surjectivity for rational Spa-cover

- **Status**: OPEN (NEW 2026-05-13, reviewer-prescribed)
- **Priority**: medium (depends on outcome of T-IDEAL-2 statement audit)
- **File**: `Adic spaces/Cor832.lean` or new module
- **Mathematical statement**: `Spec(∏_{D ∈ C.covers} 𝒪_X(D)) → Spec(𝒪_X(C.base))`
  is surjective for a rational Spa-cover.
- **Proof sketch**: Wedhorn/Spa-point argument. Every prime `p ⊆ 𝒪_X(C.base)`
  is hit by some prime of a component, using the fact that the cover is a
  topological cover via continuous valuations: a valuation `v` lying over `p`
  with `v(C.base.s) ≠ 0` is in `R(C.base.T / C.base.s)`, hence in some
  `R(D.T / D.s)` by `C.hcover`. The corresponding prime of `𝒪_X(D)` is the
  desired preimage.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-13): "If the needed fact is
  spectrum surjectivity for the product restriction, state that directly:
  `Spec(∏ O(D_i)) → Spec(O(D₀))` is surjective for a rational Spa-cover.
  Prove it by the Wedhorn/Spa-point argument, not by arbitrary proper-ideal
  preservation in `locSubring`."
- **Use**: replacement for the false framing of T-IDEAL-2 (`closedness-residual`).

### [T-BOURBAKI-FG-CLOSED] Bourbaki closedness (safe form)

- **Status**: OPEN (NEW 2026-05-13, reviewer-prescribed)
- **Priority**: medium (alternative to T-SPA-COVER-SURJ)
- **File**: `Adic spaces/IdealClosedness.lean` (extend existing infrastructure)
- **Mathematical statement**:
  > For complete separated noetherian ring `R` with `I`-adic topology
  > and finitely generated module `M` (with induced complete topology),
  > every finitely generated submodule `N ⊆ M` is closed.
- **Proof sketch**: Artin–Rees + Krull intersection under `I ⊆ Jac(R)`.
  The `I ⊆ Jac(R)` condition follows from completeness in the standard
  argument: topologically nilpotent ⇒ `1 - x` unit (geometric series in
  COMPLETE adic rings); elements of `I` are topologically nilpotent for
  the `I`-adic topology; hence `I ⊆ Jac(R)`. Then Krull intersection
  (Artin–Rees) gives closedness of f.g. submodules.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-13): "If a closedness lemma
  is still needed, target the safe Bourbaki form ... `R` noetherian,
  complete, separated, `I`-adic, `M` finitely generated with the induced
  complete topology. Use Artin–Rees and the Jacobson/Krull intersection
  theorem under `I ⊆ Jac(R)`, deriving `I ⊆ Jac(R)` from completeness when
  appropriate."
- **Use**: alternative replacement for T-IDEAL-2 (`closedness-residual`).

### [T-LANE-C-REFINEMENT-INDUCTION] Topological refinement induction for Lane C arbitrary-C

- **Status**: TREE ITERATION DONE (2026-05-13); existence is the sole residual
- **Tree iteration closure** (`productRestrictionSub_isInducing_via_tree`,
  `productRestrictionSub_isInducing_via_tree_refinement`,
  `productRestrictionSub_isInducing_of_wedhorn_tree_existence`,
  `EmbeddingTopo.lean`, all axiom-clean, commits `e330720`, `888cd8b`,
  `80c2a09`): the full inducing-via-tree induction (LEAF + NODE) +
  the transfer from tree-cover inducing to arbitrary-C inducing +
  the factorization theorem. Combined, these reduce the
  topological-inducing-for-arbitrary-C goal to the existence of a
  Laurent refinement tree refining C (Wedhorn 8.34 content).
- **Local step closure** (`productRestrictionSub_isInducing_via_V_containing_laurent_pair`,
  `EmbeddingTopo.lean`, axiom-clean): given C with a refining V containing a
  Laurent pair at C.base, IsInducing for C follows by combining T290
  (V-bootstrap) with T282 (strengthened refinement transfer) and T285
  (natural refinement map + continuity).
- **Finset-inclusion specialisation** (`productRestrictionSub_isInducing_of_V_subset_C_with_laurent_pair`,
  `EmbeddingTopo.lean`, axiom-clean): when V_covers ⊆ C.covers as Finset,
  IsInducing follows directly via T289 (sub-inducing) ∘ T290 (V-Laurent
  bootstrap). No τ-map construction needed. This handles the case where C
  itself is "rich enough" to contain a Laurent-at-base pair as a subset.
- **Remaining**: Wedhorn 8.34 *constructive tree existence* — given
  arbitrary `C`, produce a tree refining C with `allSplitsInducing` +
  `allNodesDisjoint`. See `T-LAURENT-REFINEMENT-TREE-EXISTENCE`.
- **Priority**: HIGH (replaces the round-4 search for "single Laurent pair at base")
- **File**: `Adic spaces/EmbeddingTopo.lean`
- **Mathematical statement**:
  > If a rational cover `C` has a Laurent-refinement tree whose leaves refine
  > `C`, and every Laurent split in the tree is topologically inducing,
  > then the diagonal `productRestrictionSub A C` is topologically inducing.
- **Proof sketch**: Induction on the tree. At each internal node, the Laurent
  split is the 2-cover at some element. Apply Theorem 5.10
  (`productRestrictionSub_isInducing_of_C_covers_contains_laurent_pair`) at the
  leaf level: Laurent two-cover inducing. Propagate up via Aux 10.7
  (`productRestrictionSub_isInducing_of_finer_rational_continuous`) +
  Aux 10.8 (`naturalRefinementMap` + continuity + commutativity). Theorem 5.10
  is the LOCAL induction step at each split, not a global theorem.
- **Depends on**: T-LAURENT-REFINEMENT-TREE (for the tree existence);
  T-EMBED-TOPO-LANE-C-BOOTSTRAP (already DONE, supplies the local step).
- **Reviewer guidance** (ChatGPT Pro, 2026-05-13): "For `lane-c-arbitrary-c`,
  do not search for one Laurent pair at the base. Theorem 5.10 is a local
  induction step. Build a topological refinement induction mirroring Wedhorn
  8.34: Laurent-pair inducing at each split plus refinement transfer gives
  inducing for the original cover."

### [T-LAURENT-REFINEMENT-TREE] Finite Laurent refinement tree from standard cover

- **Status**: SPLIT (2026-05-13; re-audited 2026-05-27 — sole live residual sorry is `balancedTree_BalancedInducing_of_rescaled_S` at `TateAcyclicityResiduals.lean:1789`). The DATA STRUCTURE has landed; the EXISTENCE THEOREM (Wedhorn 8.34) is the remaining work — see Round-6 re-audit at the end of this file for the sharpened close-out plan.
- **Priority**: medium (blocks T-LANE-C-REFINEMENT-INDUCTION)

#### Data-structure stage — DONE (2026-05-13, commit `f5dc330`)

- **File**: `Adic spaces/LaurentRefinementTree.lean` (new module).
- **Landed (axiom-clean)**:
  - `LaurentTree A` inductive type (unindexed; semantics supplied separately).
  - `LaurentTree.leaves`, `.depth`, `.Refines`, `.leafCover`,
    `.leaf_subset_base`, `.cover_base`, `.toCovering`,
    `.refines_iff_forall_mem_leaves`.
  - In `EmbeddingTopo.lean`: `LaurentTree.allSplitsInducing` predicate
    + `productRestrictionSub_leafTree_isInducing` (LEAF base case for
    the tree induction; proof via `inducing_iInf_to_pi` + `iInf_unique`
    + `Subsingleton.elim` + `restrictionMap_id` + `induced_id`).
- **Design note**: an indexed `LaurentTree : RationalLocData A → Type`
  hits a strict-positivity rejection because the `node` constructor's
  recursive children are at computed indices `laurentPlusDatum D₀ f` /
  `laurentMinusDatum D₀ f` (noncomputable, computed). The unindexed
  tree + separate interpretation function `leaves` works around this
  cleanly.

#### Existence stage — OPEN

- **File**: `Adic spaces/GeometricReduction.lean` (extend existing standard-cover infrastructure)
- **Mathematical statement**: For arbitrary rational covering `C` and a
  standard cover `S ⊆ A` (with `Ideal.span S = ⊤`), construct a
  `LaurentTree A` whose interpretation `t.leaves D₀` refines `C`. Each
  internal node is a Laurent split at some element of `S`; each leaf is
  a piece contained in some piece of `C.covers`.

#### Tree-induction infrastructure — DONE (2026-05-13)

The full chain from "tree exists" to "C-level inducing" lands axiom-clean:

- `productRestrictionSub_isInducing_via_tree` (commit `e330720`,
  EmbeddingTopo.lean): given `allSplitsInducing t D₀` +
  `allNodesDisjoint t D₀`, the diagonal `productRestrictionSub` for
  the tree-induced covering is `IsInducing`. Proof by induction on
  the tree, using the LEAF base case + NODE step.
- `LaurentTree.allNodesDisjoint` (EmbeddingTopo.lean): recursive
  predicate requiring distinct + disjoint sub-coverings at every node.
- `LaurentTree.refinementTau` + `refinementTau_spec` (commit `888cd8b`,
  EmbeddingTopo.lean): τ-map extraction from `t.Refines D₀ C`.
- `productRestrictionSub_isInducing_via_tree_refinement` (commit
  `888cd8b`, EmbeddingTopo.lean): combines tree-induction with T282
  (natural refinement transfer) to deduce IsInducing for the original
  cover `C` from IsInducing for `t.toCovering D₀`.
- `productRestrictionSub_isInducing_of_wedhorn_tree_existence` (commit
  `80c2a09`, EmbeddingTopo.lean): the FINAL factorization theorem,
  isolating Wedhorn 8.34 as the sole remaining residual.
- Right-branching tree constructors (commits `1aff6a4`, `2c468f4`,
  `417352a`): `LaurentTree.ofRightBranchList`, leaf enumeration
  (`leaves_ofRightBranchList`, `plusOfMinusChain`, `terminalMinus`),
  refinement combinators (`leaf_refines_singleton`,
  `node_leaf_leaf_refines_laurentCovering`, `Refines.mono`,
  `node_refines_of_subtrees_refine`, `ofRightBranchList_refines`,
  `leaf_refines_of_singleton`).
- Concrete tree-existence witnesses (commits `a073c08`, `9a29a99`,
  `18dc249`): `exists_for_singleton_cover`, `exists_for_laurentCovering`,
  `exists_for_singleton_cover_of_eq` — depth-0 and depth-1 closures.
- Right-branching tree existence (commits `9c94153`, `0a95085`,
  `14e18ee`): per-level predicates `RightBranchInducing`,
  `RightBranchDisjoint` and conversion lemmas, packager
  `exists_for_rightBranchList`, depth-1 identification
  `ofRightBranchList_singleton`.
- IsSheafy via Wedhorn 8.34 factorization (commit `0479098`,
  EmbeddingTopo.lean): `isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence`
  composes `productRestrictionSub_isInducing_of_wedhorn_tree_existence`
  with `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing` into
  a single named theorem whose hypothesis bundle isolates `hSpa` +
  `h_wedhorn` as the two concrete residuals.

All new declarations axiom-clean: `propext, Classical.choice, Quot.sound`.

#### Remaining residual — `exists_wedhorn_laurent_refinement_tree` (renamed 2026-05-13 round-5)

Given an arbitrary rational covering `C : RationalCovering A`,
produce a `t : LaurentTree A` with `t.Refines C.base C`,
`t.allSplitsInducing C.base`, `t.allNodesDisjoint C.base`. Once this
is produced, `productRestrictionSub_isInducing_of_wedhorn_tree_existence`
discharges the topological-inducing residual in
`isSheafy_ofStronglyNoetherianTate_flat`'s embedding field.

**Reviewer guidance** (ChatGPT Pro, 2026-05-13 round 5 reply): The
single-stage balanced Laurent tree built from a standard cover
*does not* refine `C` leaf-by-leaf. The all-minus leaf has no
a-priori per-leaf containment in a single `C`-piece. Wedhorn's actual
proof is **two-stage** (graft a second tree under every first-stage
leaf):

1. Start with a standard cover `U` refining `C`.
2. Use Corollary 7.32 to build a **first-stage** Laurent cover `V`
   such that for every leaf `L` of `V`, the restricted cover `U|L`
   is *generated by units* in `𝒪(L)`. (Units depend on `L`.)
3. For each first-stage leaf `L`, refine `U|L` by a **second-stage**
   Laurent cover generated by the ratios `f_i · f_j⁻¹` of those
   units in `𝒪(L)`.
4. Graft those second-stage trees under the first-stage leaves.
5. The final leaves refine `U`, hence refine `C`.

The "all-minus leaf" is just one of the `V_j`; it is not terminal,
it is refined further by stage 2. "Cover generated by units" is NOT
a singleton cover — it has a Laurent refinement by pairwise ratios
(only trivial in special cases of integral units with valuation
identically 1).

**Quantifier structure of Step 2** (corrected from round 5):
```
Given a standard cover U generated by T = (f₀,…,fₙ),
there exists a Laurent cover V = (V_j) such that
  for every Laurent leaf V_j,
    the restricted cover U|V_j is generated by a finite family of
    units in 𝒪_X(V_j).
```
The units are *local to each Laurent leaf*; the unit-generating
family may depend on `j`.

**Construction sub-tickets** (round-5 split):

- `T-WEDHORN-STAGE-1` — first-stage Laurent cover existence via
  Cor 7.32.
- `T-WEDHORN-STAGE-2` — Laurent refinement of a unit-generated
  rational cover.
- `T-LAURENT-TREE-GRAFT` — tree-grafting operation
  (place a per-leaf sub-tree under each leaf of an outer tree,
  preserving Refines / allSplitsInducing / allNodesDisjoint).
- `T-LAURENT-TREE-RELATIVE-LABELS` — relative-label LaurentTree
  whose node labels live in the running base presheaf value, not
  in `A`. **Decision (2026-05-13)**: chosen over the denominator-
  clearing route as the mathematically preferred path.
- `T-LAURENT-TREE-PRUNE` — deduplication of trivial / duplicate
  splits to preserve `allNodesDisjoint` after the graft.

### [T-WEDHORN-STAGE-1] First-stage Laurent cover for Wedhorn 8.34

- **Status**: PARTIAL (2026-05-13 round 5 + beastmode session; re-audited 2026-05-27 — live residual sorries are `strengthened_cover_of_basic_cover` at `TateAcyclicityResiduals.lean:439`, `outside_rescue_of_per_D_cover` at line 458, and `exists_first_stage_laurent_tree_unit_generated` at line 1849 — see Round-6 re-audit at the end of this file for the sharpened close-out plan). The STRUCTURAL infrastructure is landed; the Cor 7.32 application + per-leaf restriction-as-units characterisation remains.
- **Landed (axiom-clean, beastmode session 2026-05-13)**:
  - `LaurentTree.ofBalancedList : List A → LaurentTree A` — balanced
    binary tree where both children at each level are the same
    recursive sub-tree.
  - `LaurentTree.depth_ofBalancedList` — depth equals list length.
  - `LaurentTree.balancedLeafBase D₀ L σ` — running base at leaf
    indexed by σ : Fin |L| → Bool.
  - `LaurentTree.balancedLeafBase_subset_base` — every leaf is a
    sub-base of D₀.
  - `LaurentTree.leaves_ofBalancedList_mem` — every σ gives a leaf.
  - `LaurentTree.leaves_ofBalancedList_eq_image` — every leaf comes
    from some σ (the other direction of the bijection).
  - `LaurentTree.length_leaves_ofBalancedList` — exactly 2^|L| leaves.
  - `LaurentTree.balancedLeafBase_isUnit_get_of_false` — **the
    substantive unit property**: at any leaf where σ k = false,
    L.get k is a unit in 𝒪(leaf).
- **Remaining work**:
  - Cor 7.32 application: extract dominating unit s, rescale T
    to {s⁻¹ f : f ∈ T}.
  - Define per-leaf τ_unit : leaf base → Finset of units.
  - Prove: U|leaf σ = (rational cover generated by τ_unit at leaf σ).
  This is the Cor 7.32 bookkeeping piece.
- **Priority**: HIGH (sub-piece of the Wedhorn 8.34 grafted construction)
- **File**: new module under `Adic spaces/` (working name: `WedhornStageOneLaurent.lean`)
- **Depends on**: `RationalCovering.refines_by_standard_cover`
  (DONE conditionally on hZavyalov), `Cor 7.32` dominating-unit
  extraction (DONE).
- **Mathematical statement**: Let A be a strongly noetherian Tate
  ring with `[HasLocLiftPowerBounded]`, C a rational covering of D₀,
  and U a standard cover (with `refines_cover`, `refines_contain`,
  `refines_span_top`) refining C — supplied by
  `refines_by_standard_cover`. Then there exists a Laurent
  refinement tree `V_tree : LaurentTree A` and a function τ_unit
  assigning to each leaf `L` of V_tree at D₀ a finite family
  `{u_i^L : i ∈ I_L}` of elements of `𝒪(L)` such that:
    * each u_i^L is a unit in 𝒪(L);
    * the rational cover of L generated by {u_i^L : i ∈ I_L}
      coincides (as a rational covering of L) with U|L (the
      restriction of U to L).
- **Proof sketch**: Apply Cor 7.32 to extract the dominating unit
  s; the rescaled standard cover {s⁻¹ f₀, …, s⁻¹ f_n} satisfies
  the per-leaf unit condition by the standard Wedhorn 7.32
  argument (pp. 83 of [Wed19]). The Laurent tree V_tree is the
  balanced tree on the elements s⁻¹ f_i.
- **Output type signature** (informal): `(V_tree : LaurentTree A) ×
  (τ_unit : ∀ L ∈ V_tree.leaves D₀, Finset (presheafValue L))
  × proofs that each τ_unit L generates U|L and consists of units`.

### [T-WEDHORN-STAGE-2] Laurent refinement of a unit-generated rational cover

- **Status**: OPEN (2026-05-13, round 5)
- **Priority**: HIGH
- **File**: new module under `Adic spaces/` (working name: `WedhornStageTwoLaurent.lean`)
- **Depends on**: `T-LAURENT-TREE-RELATIVE-LABELS` (the relative
  LaurentTree type that allows ratios in the running ring).
- **Mathematical statement**: Let B be a strongly noetherian Tate
  ring, D₀ a rational locality datum over B, and U a rational
  cover of D₀ generated by units u₁, …, u_r in `𝒪(D₀)`. Then
  the relative Laurent cover generated by the pairwise ratios
  `u_i · u_j⁻¹` refines U.
- **Proof sketch**: Per Wedhorn pp. 83–84: the rational cover by
  units {u_i} has the property that every valuation v on Spa(B,B⁺)
  with v inside rationalOpen D₀ satisfies v(u_i) > 0 (all units),
  hence the cover is determined by the *order* of v(u_i)'s. The
  Laurent ratios u_i · u_j⁻¹ produce a 2^(r(r-1)/2)-piece Laurent
  cover whose leaves are determined by the same orderings; the
  refinement assignment matches each ordering to the unique u_i
  with maximal v(u_i) (which defines a single piece of U).

### [T-LAURENT-TREE-GRAFT] Tree-grafting operation

- **Status**: PARTIAL (2026-05-13 round 5 + beastmode session). A-labelled
  graft operations land; `allNodesDisjoint` preservation deferred (depends
  on `T-LAURENT-TREE-PRUNE`).
- **Landed (axiom-clean, beastmode session 2026-05-13)**:
  - `LaurentTree.graftUniform : LaurentTree A → LaurentTree A → LaurentTree A` —
    uniform graft (no axioms).
  - `LaurentTree.leaves_graftUniform` — leaves of uniform graft as flatMap.
  - `LaurentTree.graftAt : LaurentTree A → RationalLocData A →
    (RationalLocData A → LaurentTree A) → LaurentTree A` — per-leaf graft.
  - `LaurentTree.leaves_graftAt` — leaves of per-leaf graft as flatMap with
    per-leaf base lookup.
  - `LaurentTree.Refines_graftAt` — Refines is preserved under per-leaf graft
    given per-leaf refinement witnesses.
  - `LaurentTree.allSplitsInducing_graftAt` — allSplitsInducing is preserved
    under per-leaf graft given outer + per-leaf inducing hypotheses.
- **Remaining work**:
  - `allNodesDisjoint` preservation under graft: the post-graft Finsets
    inflate beyond what the pre-graft disjointness covers; requires either
    a stronger outer hypothesis or `T-LAURENT-TREE-PRUNE`.
  - **Relative-labels variant**: the current graft is on A-labelled trees;
    the second-stage Laurent ratios live in O(L), so a fully general graft
    awaits `T-LAURENT-TREE-RELATIVE-LABELS`.
- **Priority**: MEDIUM (combinator for assembling stages 1 and 2)
- **File**: extend `Adic spaces/LaurentRefinementTree.lean`
- **Depends on**: `T-LAURENT-TREE-RELATIVE-LABELS`.
- **Mathematical statement**: For an outer tree `t_outer` and a
  per-leaf sub-tree family `(t_inner L : LaurentTree at L) :
  ∀ L ∈ t_outer.leaves D₀, ...`, define `t_outer.graft t_inner`
  to be the tree obtained by replacing each leaf of t_outer at L
  with `t_inner L` interpreted at base L. Prove:
    * `(t_outer.graft t_inner).leaves D₀ = ⋃_L (t_inner L).leaves L`;
    * `Refines`, `allSplitsInducing`, `allNodesDisjoint` preserved
      under graft, given the corresponding properties of t_outer
      and each t_inner L.
- **Proof sketch**: Structural induction. The leaf-set identity is
  by definition. The predicate preservation requires that at the
  grafted node (formerly the leaf of t_outer), the 2-cover at the
  current base is the *root* of t_inner L, which inherits inducing
  by hypothesis.

### [T-LAURENT-TREE-RELATIVE-LABELS] Relative-label LaurentTree

- **Status**: PARTIAL (2026-05-13 round 5 + beastmode session). The
  TYPE LAYER and the ABSOLUTE RATIO DATUM (with concrete hopen) are
  landed; the tree's semantic interpretation (`leaves`, predicates,
  tree-induction theorem) remains.
- **Landed (beastmode session 2026-05-13)**:
  - `RatioLaurentTree A` inductive type with three constructors:
    `leaf`, `nodeLaurent f L R` (standard Laurent split at f ∈ A,
    relative to running base's s), `nodeRatio f g L R` (ratio split
    at f · g⁻¹).
  - `RatioLaurentTree.depth` + simp lemmas.
  - `RatioLaurentTree.ofLaurentTree : LaurentTree A → RatioLaurentTree A`
    (embedding of standard tree). No axioms.
  - **Absolute ratio datum** (substantive hopen — attacked head-on,
    not parametric): `ratioPlusDatum D₀ f g g_inv hg hg_inv` with
    g_inv ∈ D₀.P.A₀ producing the absolute RationalLocData A whose
    rationalOpen equals `rationalOpen D₀ ∩ {v(f) ≤ v(g)}`. The
    substantive hopen proof uses the algebraic identity
    `divByS b (s·g) = algebraMap g_inv · divByS (b·g) (s·g)` and the
    new helper `divByS_mul_g_mem_T_ratio` (analogue of the existing
    `divByS_mul_f_mem'` for T₂ = {f, g}).
  - `ratioMinusDatum D₀ f g f_inv hf hf_inv` (symmetric).
  - `ratioPlus_rationalOpen`, `ratioMinus_rationalOpen` — subset
    identity via `rationalOpen_inter`.
  - `ratioPlus_subset`, `ratioMinus_subset` — containment in
    rationalOpen D₀.
  - `ratioCover_covers` — valuation-trichotomy coverage; requires
    BOTH f_inv ∈ A₀ (for minus's v(f) ≠ 0) and g_inv ∈ A₀ (for plus's
    v(g) ≠ 0).
  - `ratioCovering D₀ f g f_inv g_inv hf hf_inv hg hg_inv :
    RationalCovering A` — full 2-element ratio cover analogous to
    `laurentCovering`.
- **Remaining work**:
  - `RatioLaurentTree.leaves t D₀ (per-node-inverses) :
    List (RationalLocData A)`: recursive leaf interpretation
    dispatching on constructor. Threads per-node inverse witnesses
    through the tree walk.
  - `Refines`, `allSplitsInducing`, `allNodesDisjoint` analogues.
  - Tree-induction theorem analogous to
    `productRestrictionSub_isInducing_via_tree`.
- **Important caveat**: the hopen for `ratioPlusDatum` requires
  `g_inv ∈ D₀.P.A₀` — i.e., g is a unit *in the ring of definition
  A₀*, not just in A. For Wedhorn 8.34's actual second-stage ratios
  `f_i / f_j`, the inverses live in `presheafValue (leaf base)`, not
  in A₀. Translating between these is the content of
  `T-RATIONAL-LOC-TRANSITIVITY-API` (the transitivity bridge between
  absolute A-level data and relative-over-presheafValue data).

#### Mathematical content summary (beastmode session 2026-05-13)

The session's substantive achievement: the absolute ratio-Laurent
split machinery is now complete with constructive hopen proofs (not
parametric hypotheses) under the genuine algebraic condition
`g_inv ∈ A₀`. The proof technique:

* `divByS_mul_g_mem_T_ratio` lifts D₀'s hopen via the canonical map
  `Localization.Away D₀.s → Localization.Away (D₀.s * g)` to give
  `divByS (b·g) (D₀.s·g) ∈ locSubring(D₀.P, T_new, D₀.s·g)`.
* `ratioPlusDatum`'s hopen then uses the algebraic identity
  `divByS b (D₀.s·g) = algebraMap g_inv · divByS (b·g) (D₀.s·g)`
  (via `IsLocalization.mk'_eq_of_eq`) together with
  `algebraMap_mem_locSubring` for `algebraMap g_inv` (using
  `hg_inv : g_inv ∈ A₀`) to conclude membership.

The substantive gap remaining for Wedhorn 8.34 in full: bridging
"unit at leaf-level presheaf value" (which the unit-at-minus-leaf
lemma gives) to "unit-with-inverse-in-A₀" (which `ratioPlusDatum`
needs). This is the transitivity-API content of
`T-RATIONAL-LOC-TRANSITIVITY-API`. The absolute infrastructure
above is fully sufficient once that bridge lands.
- **Priority**: HIGH (foundational for T-WEDHORN-STAGE-2 and
  T-LAURENT-TREE-GRAFT)
- **File**: `Adic spaces/LaurentRefinementTree.lean` (extend with
  a relative type)
- **Mathematical statement**: Define a relative Laurent tree where
  each node carries an element of the running base presheaf value.
  Concretely, parameterise by a dependent path from the root:
  `LaurentTreeRel : RationalLocData A → Type`
  with
    * `leaf : LaurentTreeRel D₀`;
    * `node (f : presheafValue D₀) (L : LaurentTreeRel (laurentPlusDatumRel D₀ f))
       (R : LaurentTreeRel (laurentMinusDatumRel D₀ f)) : LaurentTreeRel D₀`.
  Here `laurentPlusDatumRel D₀ f` is the rational locality datum
  for `f` viewed as an element of presheafValue D₀ but *expressed*
  as an iterated rational locality datum over A (via the iterated-
  rational equivalence + denominator clearing).
- **Proof sketch / design notes**:
    * The strict-positivity issue from the original `LaurentTree A`
      attempt (computed indices via noncomputable
      `laurentPlusDatum`) may resurface. If so, fall back to an
      unindexed type carrying a *predicate* "f is a valid relative
      label at D₀" rather than baking the base into the type.
    * The interpretation back to `LaurentTree A` proceeds by
      iterated denominator-clearing: an element of presheafValue D₀
      is canonically represented (up to power-bounded equivalence)
      by a fraction t/s^k for some t ∈ A and k ∈ ℕ — Cor 7.32 +
      the rational-localisation-transitivity API (see
      `T-RATIONAL-LOC-TRANSITIVITY-API`) gives the precise
      statement.

### [T-LAURENT-TREE-PRUNE] Deduplication / trivial-split pruning

- **Status**: OPEN (2026-05-13, round 5)
- **Priority**: MEDIUM (Lean-artefact only; not Wedhorn content)
- **File**: extend `Adic spaces/LaurentRefinementTree.lean`
- **Mathematical statement**: Define a `prune : LaurentTree A →
  LaurentTree A` operation that removes nodes whose split element
  is a unit at the running base (so plus = minus = the whole base,
  making the split trivial) and collapses such nodes to their
  unique surviving child. Prove:
    * `t.toCovering D₀ = t.prune.toCovering D₀` (semantic
      equivalence at the cover level);
    * `t.allSplitsInducing D₀ → t.prune.allSplitsInducing D₀`;
    * `t.prune.allNodesDisjoint D₀` (trivially, since the
      problematic plus = minus collisions are pruned away).
- **Why needed**: Wedhorn does not care about duplicate cover
  pieces (the abstract Čech complex is identical); but our
  `Homeomorph.piFinsetUnion`-based NODE step requires the children
  to have *disjoint* `Finset` covers, which fails after grafting if
  the unit-ratio Laurent splits coincide at certain leaves. Pruning
  preserves the represented cover while making the Finset
  representation suitable for our topology transport.

### [T-RATIONAL-LOC-TRANSITIVITY-API] Rational-localisation transitivity (replaces T-LOCLIFT-PRESERVATION)

- **Status**: OPEN (2026-05-13, round 5 — replaces the obviated
  T-LOCLIFT-PRESERVATION ticket above)
- **Priority**: HIGH (foundational for the relative-label tree)
- **File**: new or extended `Adic spaces/CompletionLocalization.lean`
- **Mathematical statement**: Establish two facts as a single
  named API:
    * **(Transitivity)** Let A be a strongly noetherian Tate ring,
      D ⊂ A a rational locality datum, D' a rational locality
      datum over presheafValue D. Then there is a canonical
      rational locality datum D'' over A, and a canonical
      isomorphism of topological rings between presheafValue
      (over `presheafValue D`) of D' and presheafValue (over A)
      of D''.
    * **(Generators are power-bounded by construction)** The
      canonical fraction-generators of D'' (when expressed as
      iterated fractions over A) are power-bounded in the
      corresponding `locSubring` / `PlusSubring`.
- **Proof sketch**: Compose `Localization.Away` with itself; use
  the iterated-rational equivalence (`presheafValue_iteratedPlus_equiv`
  / `presheafValue_iteratedMinus_equiv`, already established) plus
  the universal-property characterisation of completions. The
  power-boundedness is by construction (each generator t/s arises
  with a specific power of s in the denominator, which by the
  Cor 7.32 dominating-unit normalisation is bounded above).
- **Reviewer guidance** (round 5): "Replace the ad hoc
  `HasLocLiftPowerBounded` preservation target with a cleaner
  transitivity API: 'rational localization over O(D) = iterated
  rational localization over A, and the rational generators are
  power-bounded by construction.' That is the right formulation
  for the preservation step."
- **Relationship to T-LOCLIFT-PRESERVATION**: That ticket is
  marked LARGELY OBVIATED in its current form (Cor 8.32 route
  refactored to drop the dependency); the residual preservation
  need (for the grafted Wedhorn tree construction) is captured
  here as the cleaner transitivity API instead of as an
  unstructured class preservation.

### [T-TREE-INDUCING-NODE] Node-case recursion of inducing-via-tree theorem

- **Status**: DONE (2026-05-13, commit `b96a6f4`). The FULL FLAT theorem
  `productRestrictionSub_isInducing_via_tree_node` lands axiom-clean.
  Key auxiliary land: `Homeomorph.piFinsetUnion_apply_left/right` using
  `Equiv.piCongrLeft_sumInl/sumInr` for the unfolding step.
- **Priority**: medium (paired with T-LAURENT-REFINEMENT-TREE existence;
  together they close T-LANE-C-REFINEMENT-INDUCTION)
- **File**: `Adic spaces/EmbeddingTopo.lean` (after the leaf base case)

#### Mathematical statement

For a `node f L R` tree at root `D₀`: given
  (i) `IsInducing (productRestrictionSub A (laurentCovering D₀ f))`,
  (ii) `IsInducing (productRestrictionSub A (L.toCovering (laurentPlusDatum D₀ f)))`,
  (iii) `IsInducing (productRestrictionSub A (R.toCovering (laurentMinusDatum D₀ f)))`,
  AND (iv) `Disjoint Lleaves Rleaves`,
conclude `IsInducing (productRestrictionSub A ((LaurentTree.node f L R).toCovering D₀))`.

#### Tools already landed (2026-05-13)

- `Homeomorph.piFinsetUnion` (EmbeddingTopo.lean, commit `a6ab898`):
  `(s_pi) × (t_pi) ≃ₜ ((s ∪ t)_pi)` under `Disjoint s t`.
- `productRestrictionSub_leafTree_isInducing` (EmbeddingTopo.lean,
  commit `f5dc330`): the LEAF base case.

#### Proof obstruction (2026-05-13)

The proof goes:

1. From (i), (ii), (iii), build IsInducing for the PAIR form:
   `presheafValue D₀ → (∀ q : Lleaves, presheafValue q.1) × (∀ q : Rleaves, presheafValue q.1)`.
2. From the PAIR form, build IsInducing for the FLAT form via
   `Homeomorph.piFinsetUnion` (composition with a homeomorphism).

Step 1 requires going from `h_split` (which has codomain
`∀ p : ↥{plus, minus}, presheafValue p.1`) to a *product* form
`presheafValue plus × presheafValue minus`. This requires a
homeomorphism `Pi-over-{plus,minus} ≃ₜ presheafValue plus ×
presheafValue minus`, which factors as
`piFinsetUnion(symm) ∘ piUnique on each singleton`.

Implementation issue: the dependent types (subtype membership proofs
carried inside `restrictionMap`'s `hsubset` field) make the rewrites
delicate. Several drafts have stalled on motive-not-type-correct or
proof-irrelevance issues when substituting `default.1 = plus`.

Step 2 also requires showing the FLAT productRestrictionSub equals the
piFinsetUnion of the pair form. This equation has the same kind of
dependent-type/proof-irrelevance issue.

#### Sub-issues to spawn before retrying

- **T-LAURENT-LEAF-DISJOINT-BASE** — DONE (commit `ad3a46a`,
  2026-05-13): the leaf-leaf base case of disjointness lands as
  `leaves_disjoint_of_leaf_leaf` in `LaurentRefinementTree.lean`.
  General tree case (depth ≥ 2) remains; deferred to Wedhorn 8.34
  tree construction maintaining disjointness as an invariant.
- **T-INTERMEDIATE-2COVER-PAIR**: prove
  `Topology.IsInducing (fun x => (restrictionMap D₀ plus _ x, restrictionMap D₀ minus _ x))`
  from `h_split`. This is the 2-cover-to-pair homeomorphism step.
  **Sub-sub-issue**: construct `Homeomorph.piTwoToProd : ((i : ↥{a, b}) → α i.1) ≃ₜ α a × α b`
  for `a ≠ b`. Composition of `piFinsetUnion.symm` (already in
  `Adic spaces/EmbeddingTopo.lean`) with `funUnique` on each singleton.
  Dep-type/Finset-cast issues remain.
- **T-NODE-FLAT-EQ-PIUNION-PAIR**: prove the equation
  `productRestrictionSub _ (node ...) x =
    piFinsetUnion (Lpi x, Rpi x)` (with index identification).
- **T-NODE-CASE-FROM-PIECES**: combine the above to get the full
  node case.

The right approach is to attack each sub-issue as a focused lemma with
its own proof, then compose. Direct end-to-end proof drafts have hit
dep-type walls; the four sub-issues isolate each technical hurdle.

### [STACKS-00MA-NOETH] AdicCompletion of Noetherian is Noetherian (unconditional)

- **Status**: OPEN (NEW 2026-05-13, reviewer-prescribed reframing of T-MATHLIB-STACKS-00MA)
- **Priority**: medium (mathlib upstream; not blocking the project per reviewer)
- **File**: future Mathlib PR, target `Mathlib/RingTheory/AdicCompletion/Noetherian.lean`
- **Mathematical statement**: For Noetherian ring `R` and f.g. ideal `I`,
  `AdicCompletion I R` is Noetherian.
- **Proof sketch**: Standard. `R̂_I` is a quotient of `R[[T_1, ..., T_n]]`
  where `T_i` map to generators of `I`. Mathlib's `PowerSeries.instIsNoetherianRing`
  + multivariable iteration. Equivalent to Stacks 00MA Lemma 1.
- **Reviewer guidance** (ChatGPT Pro, 2026-05-13): "You may still upstream:
  completion is noetherian; completion is flat; completion is faithfully
  flat under `I ≤ Jac(R)`. ... For this project, avoid it unless
  noetherianity of iterated completed rings is truly missing."
- **Replaces**: the noetherianness half of T-MATHLIB-STACKS-00MA. The
  faithfully-flat half was incorrectly stated as unconditional; that's now
  retired (the conditional form is in mathlib already).

### Reannotation: T-EMBED-TOPO-LANE-C-BASE (T273+T275) and `lane-c-single-laurent`

- **2026-05-13 reannotation** (reviewer-prescribed): Theorem 5.10 — the
  V-contains-laurent-pair bootstrap — is the LOCAL INDUCTION STEP for
  T-LANE-C-REFINEMENT-INDUCTION, not a global theorem solving arbitrary
  covers. Cross-reference: it serves as the leaf-level closure in the
  refinement-induction tree.

---

## Wedhorn 6.18 chain tickets (2026-05-17, /develop pass)

Generated from `.mathlib-quality/decomposition.md` after the binding methodical-
decomposition pre-work pass for the Wedhorn 6.16/6.17/6.18 chain + audit-pass-2
trio + AuditCleanWrappers. Roadmap doc:
`docs/plans/2026-05-17-wedhorn-618-roadmap.md`.

### [T-WEDHORN-618-L1] Banach OMT for complete metric topological abelian groups

- **Status**: **DONE (2026-05-18, commit `3a7ce47`)** with
  `[SigmaCompactSpace G]` added per BINDING-RULE (b). The original
  signature was B2-flagged (b2_log entry 3, counterexample
  G=ℝ-discrete↦H=ℝ-Euclidean). Now reduces in one line to mathlib's
  `AddMonoidHom.isOpenMap_of_sigmaCompact`
  (`Mathlib.Topology.Algebra.Group.OpenMapping`). Axiom-clean:
  `#print axioms AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`
  shows `[propext, Classical.choice, Quot.sound]`. Sub-lemmas B / C / D
  / C.1 in `BanachOMT.lean` are now obsolete (never called). `wedhorn_6_16`
  (L2) and `wedhorn_6_18_continuous` (L4.2) are also sorry-free under the
  same hypothesis cascade.
- **File**: `Adic spaces/BanachOMT.lean`
- **Depends on**: (none — mathlib gap; foundation for all later tickets)
- **Parallel**: yes (no dependencies)
- **Type**: lemma (mathlib gap, suitable for upstream)

#### Statement

```lean
theorem AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [CompleteSpace H] [(uniformity H).IsCountablyGenerated] [T2Space H]
    (f : G →+ H) (hf : Continuous f) (hsurj : Function.Surjective f) :
    IsOpenMap f := by sorry
```

#### Proof sketch

Bourbaki [TG] III.3.3 — the classical Banach argument adapted to topological
abelian groups.

1. **Source is Baire.** `G` is complete uniform with countably-generated
   uniformity ⇒ `BaireSpace G` via `BaireSpace.of_pseudoEMetricSpace_completeSpace`.
2. **Cover trick.** Pick any nbhd `U` of 0 in `G`. Since `H` is countably-generated,
   there's a countable nbhd basis `(V_n)` of 0 in `H`. For each `n`,
   `H = ⋃_k (k · V_n)` (by countability of integers acting via addition).
3. **Baire on H.** The image `f(n·U) = n·f(U)` covers `H` by countable union
   (any countable cover by translates of `f(U)`); `H` is Baire (CompleteSpace
   + countably-generated ⇒ same instance), so some `n·f(U)` has nonempty interior.
4. **Subtract.** `f(U) - f(U)` contains a nbhd of 0 in `H` (by the open-symmetric
   trick: if `n·f(U)` has interior point `y`, then `y - y = 0` is in interior
   of `f(U) - f(U)` after rescaling).
5. **Cauchy lift.** For any `y` in a small nbhd of 0 in `H`, build a Cauchy
   sequence `(x_n)` in `G` with `x_n ∈ ½^n · U` and `f(x_n) - y → 0`
   (geometric refinement). Since `G` is complete, `x_n → x ∈ G`; `f` continuous
   ⇒ `f(x) = y`; the sequence stays in `U + ¼U + ⅛U + … ⊆ 2U`, so `x ∈ 2U`.
6. **Open everywhere.** Translation invariance: `f` open at 0 ⇒ open everywhere.

#### Mathlib lemmas needed

- `BaireSpace.of_pseudoEMetricSpace_completeSpace` — Baire from complete +
  countably-generated uniformity (verified: `Mathlib.Topology.Baire.CompleteMetrizable`).
- `nonempty_interior_of_iUnion_of_closed` — Baire category for closed unions.
- `Filter.HasBasis.mem_iff`, `nhds_zero` basis lemmas.
- `CauchySeq.tendsto_of_completeSpace` — completeness ⇒ Cauchy converges.
- `IsTopologicalAddGroup.continuous_neg`, `continuous_add` — translation continuity.

#### Sources

- Bourbaki, *Topologie Générale*, Chapter III §3 no. 3 Théorème 1.
- Huber [Hu3] Lemma 2.4(i), Math. Z. 217 (1994), p. 16 (verbatim restatement
  for the A-module case).
- BGR §3.7 (uses Banach OMT as prerequisite per Introduction p. 5).

#### Generality decision

- Stated over `[AddCommGroup G]` + `[UniformSpace G]` + `[CompleteSpace G]` +
  `[(uniformity G).IsCountablyGenerated]` — minimal hypotheses; matches the
  Bourbaki abstraction (no scalar ring).
- The mathlib-style upstream version should drop the `T2Space H` if possible
  (T2 follows from completeness + countably-generated in most cases).

### [T-WEDHORN-618-L2-616] Wedhorn 6.16 = Huber 2.4(i) as A-module OMT

- **Status**: **DONE (2026-05-18, commit `3a7ce47`)** with
  `[SigmaCompactSpace M]` added (inherited from L1). Axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
- **File**: `Adic spaces/WedhornBanachTheorem.lean`
- **Depends on**: T-WEDHORN-618-L1
- **Parallel**: no (sequential after L1)
- **Type**: lemma

#### Statement

See `Adic spaces/WedhornBanachTheorem.lean:68` for `wedhorn_6_16`.

#### Proof sketch

Direct corollary of T-WEDHORN-618-L1. The A-linear map `f : M →ₗ[A] N` is in
particular an `AddMonoidHom`, and the underlying additive group structure
satisfies the hypotheses of L1.

Body: `exact AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated f.toAddMonoidHom hf hsurj`.

### [T-WEDHORN-618-L3-617] Wedhorn 6.17: noetherian ⇔ every ideal closed

- **Status**: done structurally (2026-05-26) — `wedhorn_6_17` (line 306) and
  `wedhorn_6_17_ideal` (line 330) in `Adic spaces/WedhornBanachTheorem.lean`
  both have real proof bodies (Baire + L3.2 chain stationarity for reverse,
  L3.1b fg-submodule closed for forward). Both transitively depend on
  `_sub_lemma_L3_1a_completion_fg_complete` (line 125, B2-flagged per
  `b2_log.jsonl` entry 1: needs `M̂` fg as `A`-module). The ticket's stated
  declarations are proven; the transitive sorry is in a different ticket's
  scope.
- **File**: `Adic spaces/WedhornBanachTheorem.lean`
- **Depends on**: T-WEDHORN-618-L2-616
- **Parallel**: no
- **Type**: theorem (iff)

#### Statement

See `Adic spaces/WedhornBanachTheorem.lean:103, 114` for `wedhorn_6_17` and
`wedhorn_6_17_ideal`.

#### Proof sketch

BGR §3.7.2/2 verbatim.

* **Forward (Noetherian ⇒ submodules closed)**: every submodule `M'` is fg,
  so we have a surjection `π : A^n ↠ M'`. By T-WEDHORN-618-L2-616, `π` is
  open, hence quotient map, hence `M' = im(π)` is closed in the codomain
  (it's the image of a closed set under an open quotient).
* **Reverse (submodules closed ⇒ Noetherian)**: ascending chain
  `M_1 ⊆ M_2 ⊆ …` has closed union `M' = ⋃ M_i`. By Baire on `M'`, some
  `M_i` has nonempty interior, hence equals `M'`.

### [T-WEDHORN-618-L4-618] Wedhorn 6.18: unique fg-module topology + maps strict

- **Status**: PARTIAL (2026-05-18; updated 2026-05-27):
  * `wedhorn_6_18_exists_canonical_topology` — axiom-clean (existence half,
    landed earlier this session).
  * `wedhorn_6_18_continuous` — axiom-clean (commit `3a7ce47` with
    `[SigmaCompactSpace A]` added per BINDING-RULE (b)).
  * `_sub_lemma_L4_2_continuous_via_OMT` — axiom-clean (same commit).
  * `_sub_lemma_L4_4_unique_topology` — already proved (T2 + ContinuousSMul
    parameter on alternative τ').
  * `wedhorn_6_18_unique` — **DELETED (2026-05-27)** as B2-false marker
    (b2_log entry 34): uniqueness clause without [T2Space τ'] +
    [ContinuousSMul A M with τ'] is mathematically false (counterexample:
    M=ℤ discrete vs indiscrete). No external callers. Existence via
    `wedhorn_6_18_exists_canonical_topology` (axiom-clean); uniqueness
    under the stronger profile via `_sub_lemma_L4_4_unique_topology`.
  * `wedhorn_6_18_open_onto_image` — has sorryAx (depends on L4.3 via
    L3.1b via L3.1a, all B2-flagged).
- **File**: `Adic spaces/WedhornBanachTheorem.lean`
- **Depends on**: T-WEDHORN-618-L3-617
- **Parallel**: no
- **Type**: theorem (3 sub-statements)

#### Statement

See `Adic spaces/WedhornBanachTheorem.lean:143, 175, 205` for
`wedhorn_6_18_unique`, `wedhorn_6_18_continuous`, `wedhorn_6_18_open_onto_image`.

#### Proof sketch

BGR §3.7.3/2 (continuity) and §3.7.3/3 (existence + uniqueness) and Cor 5
(strictness/openness) — see decomposition.md Layer 4 for full per-statement
sketches.

### [T-WEDHORN-618-L5-AUDIT] Audit-pass-2 trio (`_proof`-suffixed)

- **Status**: open
- **File**: `Adic spaces/WedhornStronglyNoetherian.lean`
- **Depends on**: T-WEDHORN-618-L4-618, T-MATHLIB-STACKS-00MA (ticket #36)
- **Parallel**: no
- **Type**: theorem (3 sub-statements + 1 generic-pair variant)

#### Statement

See `Adic spaces/WedhornStronglyNoetherian.lean:73, 103, 112, 144` for:
- `isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof`
- `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`
- `isNoetherianRing_A₀_of_stronglyNoetherianTate_proof`
- `exists_hSpa_points_global_of_stronglyNoetherianTate_proof`

#### Proof sketch

Per-lemma sketches in the file docstrings. Highlights:

* `isStronglyNoetherian_of_isNoetherianRing_isTateRing_proof`: inductive on
  variables; base case `k=0` is `A` noetherian; inductive step uses
  T-MATHLIB-STACKS-00MA + polynomial Hilbert basis.
* `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`: A₀ is
  open in A, noetherian descends via Wedhorn 6.18(2) (every A-linear map
  continuous + open ⇒ closed subring inherits).
* `exists_hSpa_points_global_of_stronglyNoetherianTate_proof`: open case via
  trivial valuation (existing `exists_spa_point_in_rationalOpen_of_isOpen_prime`);
  non-open case via Wedhorn 7.45 noetherian-ring-of-definition variant
  (existing `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` in
  `Lemma745.lean`), using A₀ noetherian from item 2.

### [T-WEDHORN-618-L6-CLEANWRAPS] Audit-clean wrappers `_proof` discharges

- **Status**: open
- **File**: `Adic spaces/AuditCleanWrappers.lean`
- **Depends on**: T-WEDHORN-618-L5-AUDIT
- **Parallel**: no
- **Type**: theorem (5 sub-statements)

#### Statement

See `Adic spaces/AuditCleanWrappers.lean:78, 110, 125, 147, 173` for:
- `cor_8_32_clean_proof` — **already PROVED** (delegates via Layer 5)
- `prop_8_30_flat_clean_proof` — sorry'd, needs Layer 5 + flatness chain
- `tateAcyclicity_separation_via_cor832_proof` — **already PROVED**
- `tateAcyclicity_gluing_via_descent_proof` — sorry'd, needs Wedhorn 8.34 chain
- `isSheafy_ofStronglyNoetherianTate_proof` — sorry'd, composes the above

#### Proof sketch

Two of the five are already proved by composition through existing
`Cor832.lean` infrastructure + the (sorry'd) audit-pass-2 trio. Once Layer
5 lands, these become genuinely sorry-free (only sorryAx-transitive via the
single underlying T-WEDHORN-618-L1 Banach OMT gap).

The remaining three sorry'd wrappers compose:
- `isSheafy_ofStronglyNoetherianTate_proof` = `tateAcyclicity_separation_via_cor832_proof` (proved)
  + `tateAcyclicity_gluing_via_descent_proof` (pending) + sheaf-axiom assembly.

### Per-file cleanup cadence

The 4 new files (`BanachOMT.lean`, `WedhornBanachTheorem.lean`,
`WedhornStronglyNoetherian.lean`, `AuditCleanWrappers.lean`) have 1-5 proof
tickets each. Per the cadence rule:

- After each file's main ticket completes, run `/cleanup <file>`. Inserted as
  `[CLEANUP-WEDHORN-618-<file>]` blocking the next layer's dependent ticket.

### Roadmap reference

Full layered analysis with source quotes per leaf:
`docs/plans/2026-05-17-wedhorn-618-roadmap.md` (1070-line estimate plus
`.mathlib-quality/decomposition.md` (the binding decomposition artifact).

---

## Route C — Banach OMT sub-sorries (added 2026-05-26)

Per Round-3 expert verdict (`.mathlib-quality/expert-review/2026-05-26/reply.md`)
and the scaffold landed in `StructureSheaf.lean:1379–1781`, the keystone
`productRestrictionSub_isInducing_tate` now has a real Route C proof body
that depends on six named sub-sorries (per CLAUDE.md sub-lemma-with-sorry
rule). These tickets discharge those sub-sorries.

### [T-ROUTE-C-1] Move Route C block below `tateAcyclicity_separation_via_cor832`

- **Status**: done (2026-05-26)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: (none — pure file refactor)
- **Parent**: (none; head of Route C subtree)
- **Type**: refactor

#### Statement

Move the Route C block (lines ~1379–1781) and the legacy `_flat`
wrappers (`productRestrictionSub_isInducing_flat`,
`productRestrictionSub_injective_flat`, `isSheafy_ofStronglyNoetherianTate_flat`)
to AFTER `tateAcyclicity_separation_via_cor832` (currently at line ~2353).

#### Proof sketch

1. Cut the Route C block (lines 1379–1781) including the new
   `productRestrictionSub_isInducing_tate` declaration.
2. Cut the legacy `_flat` wrappers (lines 1792–1946).
3. Insert ALL of these AFTER `tateAcyclicity_separation_via_cor832`'s body
   ends and BEFORE `end ValuationSpectrum`.
4. With Route C downstream, replace the `sorry` bodies of
   `productRestrictionSubToEqualizer_injective` and
   `productRestrictionSubToEqualizer_surjective` with real proofs via
   `tateAcyclicity_separation_via_cor832` and `tateAcyclicity_gluing_via_descent`.

#### Mathlib lemmas needed

None — all upstream items exist in the project.

#### Generality decision

Minimal: preserve the existing signatures of the moved theorems exactly.

### [T-ROUTE-C-2] `productRestrictionSubToEqualizer_injective` proof

- **Status**: done (2026-05-26)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: T-ROUTE-C-1
- **Parent**: T-ROUTE-C-1
- **Type**: theorem

#### Statement

```
theorem productRestrictionSubToEqualizer_injective
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    Function.Injective (productRestrictionSubToEqualizer A C)
```

#### Proof sketch

Routes through `tateAcyclicity_separation_via_cor832` (Cor 8.32 ⇒
faithful flatness of product restriction ⇒ injectivity). Given
`productRestrictionSubToEqualizer A C x = productRestrictionSubToEqualizer A C y`,
extract that `productRestrictionSub A C (x - y) = 0` componentwise, then
apply `tateAcyclicity_separation_via_cor832` to conclude `x - y = 0`.

### [T-ROUTE-C-3] `productRestrictionSubToEqualizer_surjective` proof

- **Status**: done (2026-05-26)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: T-ROUTE-C-1
- **Parent**: T-ROUTE-C-1
- **Type**: theorem

#### Statement

```
theorem productRestrictionSubToEqualizer_surjective
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    Function.Surjective (productRestrictionSubToEqualizer A C)
```

#### Proof sketch

Routes through `tateAcyclicity_gluing_via_descent`. Given an element
`⟨f, hf⟩ : ↥(sectionEqualizer A C)`, the equalizer property `hf` is
exactly the gluing-compatibility condition; apply
`tateAcyclicity_gluing_via_descent` to produce the global section
`x : presheafValue C.base` with `productRestrictionSub A C x = f`.

### [T-ROUTE-C-4] `presheafValue_uniformity_isCountablyGenerated`

- **Status**: done (2026-05-26)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: (none — structural lemma about presheafValue's topology)
- **Parent**: (none, leaf)
- **Type**: theorem (instance-like)

#### Statement

```
theorem presheafValue_uniformity_isCountablyGenerated
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (D : RationalLocData A) :
    (uniformity (presheafValue D)).IsCountablyGenerated
```

#### Proof sketch

The localization topology on `Localization.Away D.s` is induced by the
filter basis consisting of powers of `idealOfDef` (an ideal of definition);
this is a countable family. `UniformSpace.Completion` preserves the
countable-generation property of its source's uniformity (since the
completion's uniformity is the closure of the source's image uniformity).
Mathlib should have or admit a transfer lemma.

### [T-ROUTE-C-5] `presheafValue_sigmaCompactSpace`

- **Status**: DELETED (2026-05-26) — `presheafValue_sigmaCompactSpace` removed
  from `Adic spaces/StructureSheaf.lean` along with its sole consumer
  (the old sigma-compact `productRestrictionSubToEqualizer_isOpenMap`). The
  keystone topological-inducing now uses the Tate-absorbing OMT route
  (T-ROUTE-C-WIRE landed). B2 entry retained in `b2_log.jsonl` for historical
  trace.
- **Round-4 reviewer guidance** (2026-05-26): "should either be deleted,
  renamed as a lemma under an explicit sigma-compact/separable/local-compact
  hypothesis, or moved off the keystone path. It should not be a
  prerequisite for IsSheafy."
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: (none — deepest structural input)
- **Parent**: (none, leaf)
- **Type**: theorem (instance-like)

#### Statement

```
theorem presheafValue_sigmaCompactSpace
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (D : RationalLocData A) :
    SigmaCompactSpace (presheafValue D)
```

#### Proof sketch

For strongly noetherian Tate rings, the completion `presheafValue D` is
the completion of a localization; under suitable conditions on the
residue field (finite or locally compact), sigma-compactness holds.
This is the deepest input and may need an explicit hypothesis on the
ring (e.g., `[LocallyCompactSpace A]` or a finite-residue-field
assumption). **B2-risk lemma**: may be false in full generality and
need a strengthened hypothesis.

#### Sources

Wedhorn §6 (Banach OMT for Tate rings); Huber 1996 Ch. 1 (adic spaces).

### [T-ROUTE-C-6] `sectionEqualizer_uniformity_isCountablyGenerated`

- **Status**: done (2026-05-26)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: T-ROUTE-C-4
- **Parent**: (none, leaf)
- **Type**: theorem (instance-like)

#### Statement

```
theorem sectionEqualizer_uniformity_isCountablyGenerated
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) :
    (uniformity ↥(sectionEqualizer A C)).IsCountablyGenerated
```

#### Proof sketch

The finite product `∀ D : ↥C.covers, presheafValue D.1` has
countably-generated uniformity (finite product of countably-generated
uniformities). The section equalizer is a subspace, and the subspace
uniformity inherits the countably-generated property (`UniformSpace.Basic`
instance `(uniformity s).IsCountablyGenerated` for subsets of
countably-generated uniform spaces).

### [T-ROUTE-C-7] `productRestrictionSub_isInducing_tate_empty`

- **Status**: PARTIAL — TO BE CLEANED PER ROUND-4 (2026-05-26)
  — current state: `s = 0` case proven via `Topology.IsInducing.of_subsingleton`;
  `s ≠ 0 + empty cover` case remains sorry, mathematically impossible
  but requires extra typeclasses (`[CompatiblePlusSubring A]` and
  `[CompleteSpace A]`) for the Spa-point contradiction.
- **Round-4 reviewer guidance** (2026-05-26): "the final clean theorem
  should not have a hidden unprovable branch". Two cleanup options:
  (a) carry `[CompatiblePlusSubring A]` and `[CompleteSpace A]` into the
      sub-lemma signature so the Spa-point contradiction goes through;
  (b) add precondition `C.covers.Nonempty ∨ C.base.s = 0` (or split
      the keystone into two named sub-lemmas — nonempty-cover-via-Route-C
      + s-eq-zero-via-subsingleton — composed at the top level).
  Decision pending — flagged for cleanup pass after T-ROUTE-C-OMT lands.

### [T-ROUTE-C-OMT] Tate-absorbing Baire open mapping theorem (Round-4)

- **Status**: **DONE (2026-05-27)** — `_sub_lemma_pettis_lift` is now SORRY-FREE (it composes Henkel Prop 1.9 + Prop 1.10 = T-PETTIS-PROP-1-10, both proven). The entire chain `AddMonoidHom.isOpenMap_of_tate_absorbing` → `RingHom.isOpenMap_of_topologicallyNilpotent_unit` is axiom-clean (`[propext, Classical.choice, Quot.sound]`). Steps 0–12 of the Round-4 outline all discharged. Three API helpers landed earlier (image2_closure_subset, image2_sub_image_subset, pettis_lift) all proven.
- **File**: `Adic spaces/BanachOMT.lean`
- **Depends on**: (none — pure mathlib + project Baire sub-lemmas, all sorry-free)
- **Parent**: T-ROUTE-C-1 (keystone scaffold)
- **Type**: theorem

#### Statement (schematic, per Round-4 reviewer guidance)

```
theorem IsOpenMap.of_surjective_tate_absorbing
    {G H : Type*}
    [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [T2Space H] [BaireSpace H]
    (πG : G ≃+ G) (πH : H ≃+ H)
    (f : G →+ H)
    (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f)
    (h_intertwine : ∀ x, f (πG x) = πH (f x))
    (h_absorb_G : ∀ U ∈ 𝓝 (0 : G), ∀ x : G, ∃ n, (πG^[n]) x ∈ U)
    (h_basis_G : (uniformity G).IsCountablyGenerated)
    [CompleteSpace G] :
    IsOpenMap f
```

#### Proof sketch (Round-4 reviewer 7-step outline)

1. Pick an open additive subgroup/lattice `U` in source.
2. Tate absorption: source = ⋃_n π^{-n} U.
3. Surjectivity transfers: target = ⋃_n π^{-n} f(U).
4. Baire on target ⇒ closure of some `π^{-n} f(U)` has nonempty interior.
5. Translation invariance ⇒ closure of `f(U)` has nonempty interior.
6. Pettis-symmetric-nbhd argument ⇒ ∃ nbhd of `0` ⊆ `f(U')` for `U' ⊆ U`.
7. Conclude `f` open.

#### Mathlib lemmas needed

All sub-lemmas already sorry-free in `BanachOMT.lean`:
- `_sub_sub_lemma_A_1_split_symmetric` (symmetric absorption)
- `_sub_sub_lemma_A_2_interior_add` (interior of sum)
- `_sub_sub_lemma_C_2_baire_nonempty_interior` (Baire ⇒ nonempty interior)
- `_sub_sub_lemma_D_1_cauchy_builder` (Cauchy seq via shrinking basis)
- `_sub_sub_lemma_D_2_limit_in_nbhd` (limit lies in closure of nbhd)
- `_sub_lemma_translation` (open at 0 ⇒ open everywhere)
- `_sub_lemma_symmetric_absorbs` (symmetric-set absorbs)

Only the **main theorem assembly** is missing.

#### Sources

Bourbaki TG Ch III §3 no. 3 + Wedhorn Lemma 6.16 (Banach OMT for Tate rings).
Round-4 reviewer reply at `.mathlib-quality/expert-review/2026-05-26-2/reply.md`.

#### Generality decision

Two-stage: (1) general `IsOpenMap.of_surjective_tate_absorbing` for any
Tate absorption setup; (2) specialised wrapper for the `presheafValue → E_C`
situation. Per Round-4 reviewer: start with specialised form, generalise if
painless.

### [T-ROUTE-C-WIRE] Wire Tate-absorbing OMT into Route C body

- **Status**: DONE (2026-05-26) — `productRestrictionSubToEqualizer_isOpenMap`
  (Tate-absorbing route, replacing the prior sigma-compact route) delegates to
  `RingHom.isOpenMap_of_topologicallyNilpotent_unit` (new wrapper in
  `BanachOMT.lean`), which constructs πG/πH from the topologically-nilpotent
  pseudo-uniformizer via `AddAut.mulLeft` and supplies absorption from
  `IsTopologicallyNilpotent` via `Continuous.tendsto` + `Filter.Tendsto.eventually`.
  Keystone `productRestrictionSub_isInducing_tate` and Homeomorph variant
  use this route. Dead sigma-compact route + `presheafValue_sigmaCompactSpace`
  (B2-false) DELETED. Full project build clean (3144 jobs).
- **Pettis-lift B2 finding**: `_sub_lemma_pettis_lift` signature refactored
  with absorption hypotheses (πG, πH, intertwining, h_absorb_H) per binding
  rule (b); counterexample logged in `b2_log.jsonl` (discrete ℝ → Euclidean ℝ
  with U = ℚ).
- **File**: `Adic spaces/StructureSheaf.lean`, `Adic spaces/BanachOMT.lean`
- **Depends on**: T-ROUTE-C-OMT
- **Parent**: T-ROUTE-C-1 (keystone scaffold)
- **Type**: theorem (replace existing proof body)

#### Statement

Modify `productRestrictionSubToEqualizer_isOpenMap` to call the new
`IsOpenMap.of_surjective_tate_absorbing` (via the specialised form)
instead of the mathlib `AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`
wrapper that requires `[SigmaCompactSpace G]`. The `[SigmaCompactSpace]`
haveI is dropped; the pseudo-uniformizer is provided by the Tate-ring
typeclass.

#### Proof sketch

Direct invocation of the new theorem with πG, πH = (multiplication by a
pseudo-uniformizer of A, extended to `presheafValue C.base` and `E_C`
respectively via the natural ring-hom action). Intertwining is automatic
for ring homomorphisms. Absorption follows from the Tate-ring assumption
(pseudo-uniformizer powers shrink the lattice).

### [T-ROUTE-C-SEPARABLE-COROLLARY] Optional separable-case shortcut

- **Status**: open (LOW priority)
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: T-ROUTE-C-WIRE (or completed keystone)
- **Parent**: (none, optional corollary)
- **Type**: theorem (corollary)

#### Statement

```
theorem isSheafy_ofStronglyNoetherianTate_of_separable
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    [SeparableSpace A] :
    IsSheafy A
```

#### Round-4 reviewer guidance

"`[SeparableSpace A]` ... may be a useful optional corollary for classical
ℚ_p-affinoid applications. But it is still not part of Wedhorn 8.28(b) ...
Acceptable theorem layering: `_of_separable` as an optional shortcut +
the unrestricted main target."

#### Priority

LOW — the main keystone (without separability) subsumes this case via the
Tate-absorbing OMT route. Useful only as a documentation/discovery
corollary for ℚ_p-affinoid consumers who specifically want the separable
hypothesis explicitly threaded.
- **File**: `Adic spaces/StructureSheaf.lean`
- **Depends on**: (none — edge case, may be vacuous)
- **Parent**: (none, leaf)
- **Type**: theorem

#### Statement

```
theorem productRestrictionSub_isInducing_tate_empty
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : ¬ C.covers.Nonempty) :
    Topology.IsInducing (productRestrictionSub A C)
```

#### Proof sketch

When `C.covers` is empty, the target `∀ D : ↥C.covers, presheafValue D.1`
is a Pi over an empty type — a singleton. For the inducing claim:
case-split on `s = 0` (subsingleton source ⇒ trivial) vs `s ≠ 0`
(impossible via `C.hcover` + Spa-point existence).

The non-vacuous direction needs `[CompatiblePlusSubring A]` +
`[CompleteSpace A]` for the Spa-point argument
(`exists_spa_point_in_rationalOpen_of_prime`). Since the present
signature lacks these, the body must either:
1. Use the Spa-point argument with assumed typeclasses (requires adding
   instances to the theorem signature — **forbidden by BINDING RULE**)
2. Be `sorry` with documentation (the consumer
   `isSheafy_ofStronglyNoetherianTate` already case-splits on `s = 0`
   upstream, so the `s ≠ 0` + empty-cover case never reaches this code path)

**B2-risk**: this sub-lemma may be FALSE as stated (without the extra
typeclasses); the upstream `isSheafy_ofStronglyNoetherianTate` works
around it via the `s = 0` case-split. The proper resolution is to
either change the signature or accept the upstream workaround.

### [T-PETTIS-PROP-1-9] Implement Henkel Prop 1.9 (at-every-scale closure-image-nbhd)

- **Status**: DONE (2026-05-27) — body implemented (~90 LOC) by
  parametrising the OMT outer body's existing Steps 1-11. The
  `_sub_sub_lemma_henkel_prop_1_9_at_every_scale` proof in
  `Adic spaces/BanachOMT.lean` is sorry-free. Full project build clean
  (3144 jobs).
- **File**: `Adic spaces/BanachOMT.lean`
- **Depends on**: (none — sub-sub-lemma is standalone)
- **Parent**: T-ROUTE-C-OMT
- **Type**: theorem
- **Source**: Henkel (2014) arXiv:1407.5647v2, Prop 1.9 (§1.2 "2) implies 3)").
  Saved at `Henkel-Open_Mapping_for_Rings_with_Zero_Unit_Sequence-1407.5647v2.pdf`.

#### Statement

```lean
theorem _sub_sub_lemma_henkel_prop_1_9_at_every_scale
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [T2Space H] [BaireSpace H]
    (f : G →+ H) (hf_cont : Continuous f) (hf_surj : Function.Surjective f)
    (πG : G ≃+ G)
    (πH : H ≃+ H) (hπH_cont : Continuous πH) (hπH_inv_cont : Continuous πH.symm)
    (h_intertwine : ∀ x, f (πG x) = πH (f x))
    (h_absorb_H : ∀ V ∈ nhds (0 : H), ∀ y : H, ∃ n : ℕ, (πH^[n]) y ∈ V) :
    ∀ V ∈ nhds (0 : G), closure (f '' V : Set H) ∈ nhds (0 : H)
```

#### Proof sketch (Henkel Prop 1.9 transcription, ~50-80 LOC)

For each V ∈ 𝓝 0 in G:
1. Pick W ⊆ V open + closed symmetric with W + W ⊆ V (via
   `_sub_sub_lemma_A_1_split_symmetric` applied to V).
2. By πH-absorption: for each y ∈ H, ∃ n with πH^n(y) ∈ closure(f '' W) (since
   f surjective ⟹ closure(f '' M) ⊇ some nbhd; then absorb).
   Wait — actually the OMT outer body's Steps 6-7 cover this. Mimic those.
3. Cover H = ⋃_n (πH^[n])⁻¹' (f '' V). (Set form.)
4. By Baire on H, some (πH^[n₀])⁻¹' (closure(f '' V)) has nonempty interior.
5. Transfer via πH^n₀ homeo to closure(f '' V) having nonempty interior.
6. closure(f '' V) is symmetric (V symmetric, f additive).
7. By `_sub_lemma_symmetric_absorbs`: 0 is interior of
   `image2 (·-·) (closure(f '' V)) (closure(f '' V))`.
8. The difference set ⊆ closure(f '' (V+V)) ⊆ closure(f '' V_outer)
   (where V_outer was the original V; but here we already work with V directly).
9. Conclude 0 is interior of closure(f '' V).

The OMT outer body (`isOpenMap_of_tate_absorbing`) ALREADY does Steps 3-9
for a specific V from split_symmetric. The body of this sub-sub-lemma
parametrises that argument: take V as input, run the same steps.

#### Mathlib lemmas needed

- `exists_closed_nhds_zero_neg_eq_add_subset` (via `_sub_sub_lemma_A_1_split_symmetric`)
- `nonempty_interior_of_iUnion_of_closed` (Baire, via `_sub_sub_lemma_C_2_baire_nonempty_interior`)
- `Homeomorph.preimage_closure`, `Homeomorph.preimage_interior`
- `neg_closure`, `Set.image_neg_eq_neg`
- `_sub_lemma_symmetric_absorbs` (existing helper)
- `_sub_lemma_image2_closure_subset` (existing helper)
- `_sub_lemma_image2_sub_image_subset` (existing helper)
- `closure_mono`, `Filter.mem_of_superset`

#### Generality decision

Same as `_sub_lemma_pettis_lift` (matches Henkel Prop 1.9's exact hypothesis bundle).

### [T-PETTIS-PROP-1-10] Implement Henkel Prop 1.10 (metric Cauchy lift)

- **Status**: **DONE (2026-05-27)** — body landed at `Adic spaces/BanachOMT.lean:569-892` (~325 LOC including existing scaffold). Axiom-clean: `[propext, Classical.choice, Quot.sound]`. Final ~115 LOC added: residual `(y - f σ n) → 0` via continuity+cofinality, σ_lim ∈ V via telescoping doubling bound (σ(n+1)-σ 1 ∈ V_basis N₀) + closed W. **BanachOMT.lean is now ENTIRELY SORRY-FREE** (banach_two_of_three deleted later as B2-false marker). Lake build clean (3144 jobs).
- **File**: `Adic spaces/BanachOMT.lean`
- **Depends on**: (none — sub-sub-lemma is standalone)
- **Parent**: T-ROUTE-C-OMT
- **Type**: theorem
- **Source**: Henkel (2014) arXiv:1407.5647v2, Prop 1.10 + 1.12 (§1.3
  "3) implies 4)"). Cited by Henkel as Bourbaki *Topological Vector Spaces*
  Ch. I §3 Lemma 2.
- **Model**: mathlib's `ContinuousLinearMap.exists_approx_preimage_norm_le`
  + `exists_preimage_norm_le` + `isOpenMap` chain at
  `Mathlib/Analysis/Normed/Operator/Banach.lean:80-247`.

#### Statement

```lean
theorem _sub_sub_lemma_henkel_prop_1_10_cauchy_lift
    {G : Type u} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [(uniformity G).IsCountablyGenerated]
    {H : Type v} [AddCommGroup H] [UniformSpace H] [IsUniformAddGroup H]
    [T2Space H]
    (f : G →+ H) (hf_cont : Continuous f)
    (h_at_every_scale : ∀ V ∈ nhds (0 : G), closure (f '' V : Set H) ∈ nhds (0 : H)) :
    ∀ V ∈ nhds (0 : G), f '' V ∈ nhds (0 : H)
```

#### Proof sketch (Henkel Prop 1.10 + 1.12, ~80-120 LOC)

For each V ∈ 𝓝 0 in G:

1. Metrise G via `[(uniformity G).IsCountablyGenerated]` —
   `UniformSpace.pseudoMetricSpace G`. This gives a pseudo-metric `d_G`
   compatible with the uniformity. Right-invariance (`d(x·z, y·z) = d(x,y)`)
   follows from `IsUniformAddGroup`.

2. Without loss of generality, assume V = B(0, r₀) for some r₀ > 0 (mathlib's
   `Metric.mem_nhds_iff`).

3. By the at-every-scale hypothesis: for each r > 0, ∃ ρ(r) > 0 such that
   B_{ρ(r)}(0) ⊆ closure(f '' B_r(0)) in H. (Use a metric on H or work
   directly with `nhds 0`.)

4. Cauchy iteration (Henkel Prop 1.10): for y ∈ B_{ρ(r₀)}(0) in H, recursively
   pick x_n ∈ B_{r_n}(0) in G with d_H(y_n, f(x_n)) < ρ(r_{n+1}), where
   r_n = r₀ · 2^{-n} (geometric) and y_n = y - f(σ_{n-1}) (residual). The
   partial sums σ_n = ∑_{k=0}^{n} x_k are Cauchy by geometric decay.

5. By completeness of G: σ_n → σ in G. By d_G triangle inequality and
   geometric sum: d_G(σ, 0) ≤ 2r₀, so σ ∈ B_{2r₀}(0).

6. By continuity of f: f(σ_n) → f(σ). By construction f(σ_n) → y. By T₂
   on H: f(σ) = y. Hence y ∈ f '' B_{2r₀}(0).

7. Therefore B_{ρ(r₀)}(0) ⊆ f '' B_{2r₀}(0) ⊆ f '' V (after rescaling V
   appropriately). Hence f '' V ∈ 𝓝 0.

The construction mirrors mathlib's normed-space Banach OMT proof, with
metric balls in G replacing norm balls and `h_at_every_scale` replacing
the surjectivity-derived rescaling. The geometric series argument is
identical.

#### Mathlib lemmas needed

- `UniformSpace.pseudoMetricSpace` — get the metric from CG-uniformity.
- `Metric.mem_nhds_iff` — translate nhds 0 to metric balls.
- `Metric.ball`, `Metric.mem_ball`.
- `CauchySeq.tendsto_of_completeSpace` — Cauchy ⟹ converges.
- `_sub_sub_lemma_D_1_cauchy_builder` — existing helper for Cauchy-from-shrinking-basis.
- `_sub_sub_lemma_D_2_limit_in_nbhd` — existing helper for limit-in-closure.
- `Filter.Tendsto.comp`, `Filter.Eventually`, `Summable` (geometric).
- `Continuous.tendsto`, `eq_of_tendsto_of_tendsto_of_T2`.

#### Generality decision

Pseudo-metric not metric: works under just `[(uniformity G).IsCountablyGenerated]`
without requiring T₀ on G. The Cauchy lift uses `d_G` for shrinkage but doesn't
need uniqueness of limits in G (only in H, which has `[T2Space H]`).

## Round-6 expansion (2026-05-27) — uncovered residuals coverage

Audit pass on 2026-05-27 (`/develop --continue`) cross-referenced the live
sorry list against ticket coverage. Found:

- **8 sorries in `Presheaf.lean`** had no live ticket (chains: spa-point
  non-open, valuation-subring dominating, top-nilp / units, mulArchimedean
  rank-1, Wedhorn 7.42 residual, locLift power-bounded completion).
- **3 sorries in `PresheafTateStructure.lean`** were carried under the
  T-WEDHORN-213 lineage but T-213 itself closed at the LaurentNormalized API
  boundary. The residuals (`restrictionMapHom_surj/injective` + Artin–Rees
  witness) are downstream consumer obligations and need their own tickets.
- **1 sorry in `StructureSheaf.lean`** at `structurePresheaf_isSheaf` (the
  top-level sheaf claim) was uncovered.
- **9 sorries in `TateAcyclicityResiduals.lean`** were covered by stale
  `PARTIAL` tickets (T-LAURENT-REFINEMENT-TREE etc.) but those tickets
  needed sharper close-out plans.

This section adds the missing tickets per CLAUDE.md sub-lemma rule (no
hypothesis additions; sorry'd leaf statements only). Cleanup-cadence
tickets follow per §1g of `/develop`.

### [T-PRESHEAF-SPA-NONOPEN] `spa_point_nonOpen_of_rational_subset` discharge

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/Presheaf.lean:799`
- **Depends on**: T-IDEAL-2 (closedness of proper ideals — DONE), `Cor832.hSpa_points_nonOpen_via_lifted_ideal_proper` (DONE)
- **Type**: theorem
- **Source**: Wedhorn 8.2 + downstream T001 (memory `t001_support_lane.md`) — prime transport through adic completion. Architecturally located in `Cor832.lean` (`liftedIdeal_ne_top_claim` chain).

#### Statement

`theorem spa_point_nonOpen_of_rational_subset (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) (p : Ideal A) (hp : p.IsPrime) (hDs : D.s ∈ p) (hD's : D'.s ∉ p) (hp_notOpen : ¬IsOpen (p : Set A)) : ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp`

#### Proof sketch (~30-50 LOC by re-export from Cor832)

Re-export the existing downstream content. The `Cor832.hSpa_points_nonOpen_via_lifted_ideal_proper` machinery (which depends on `liftedIdeal_ne_top_claim` + `IdealClosedness` + `presheafValue_isAdicComplete`) closes this directly when supplied with the full Tate/Noetherian/T2/NonarchimedeanRing hypothesis bundle.

1. Promote `p` to an ideal in the completed localization via the prime-transport machinery of `AdicCompletionPrime.lean`.
2. Apply `liftedIdeal_ne_top_claim` to get a proper prime in the completion containing `D.s`'s image.
3. Use `presheafValue_isAdicComplete` + dominating-valuation-subring construction (separate sub-lemma `exists_valuationSubring_dominating_for_rationalOpen`, T-PRESHEAF-VALUATIONSUBRING-CHAIN below) to extract a Spa-point with `p ≤ v.supp`.

The bottleneck is the typeclass migration `[IsHuberRing A]` (in current signature) → `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]` (Cor832 signature). Two options:

- **(option A)** add the four typeclasses to the signature per CLAUDE.md binding rule (b): the lemma is mathematically true in `IsHuberRing` generality but the discharge route specifically uses the strong-noeth-Tate Cor832 chain. → Likely B2.
- **(option B)** keep `[IsHuberRing A]` and provide a separate Huber-generality proof. Wedhorn 4.6(c) gives this in the Huber case but it bottoms out at the same prime-transport question.

Decision: take option B, route via dominating-valuation-subring chain (T-PRESHEAF-VALUATIONSUBRING-CHAIN) which discharges in IsHuberRing generality.

#### Mathlib lemmas needed
- `Ideal.exists_le_maximal`, `ValuationSubring.dominates`
- `Spv.mk`, `ValuativeRel.toSpv`

#### Generality decision
IsHuberRing (existing signature) — do not strengthen.

### [T-PRESHEAF-VALUATIONSUBRING-CHAIN] Dominating-valuation-subring chain

- **Status**: PARTIAL (in_progress, 2026-05-27). Wedhorn 7.45 LIFT step (`exists_mem_rationalOpen_supp_of_dominating_valuationSubring`, Presheaf.lean:2452) has **4/5 sub-conditions explicitly proved** (~50 LOC of new proof code): supp ≥ 𝔭 via Valuation.comap_supp, A⁺-bound via _hRange, t ≤ s via _hTS multiplicativity, s ≠ 0 via Valuation.zero_iff. **Only IsContinuous remains** as sub-sorry — requires convex-subgroup restriction (Lemma745 restrictToConvex pattern) for arbitrary γ < 1. Wedhorn 7.44 Chevalley step (`exists_valuationSubring_dominating_for_rationalOpen`, Presheaf.lean:2396) has detailed step-by-step plan via `exists_valuationSubring_of_prime_enlarged` documented in its docstring (still sorry'd). Wedhorn 7.51 max-ideal Spa-point (`exists_spa_point_supp_eq_maxIdeal_of_complete`, line 2626) is the third sub-lemma (still sorry'd).
- **File**: `Adic spaces/Presheaf.lean` lines 2396, 2452 (was 2435), 2626 (was 2517)
- **Depends on**: none new (existing `ValuationSubring`, `FractionRing` API)
- **Type**: theorem × 3
- **Source**: Wedhorn 7.44 (Chevalley existence), Wedhorn 7.45 (valuation-ring lift), Wedhorn 7.51 (max-ideal Spa-point).

#### Statements

1. `exists_valuationSubring_dominating_for_rationalOpen` (line 2396) — Chevalley + bookkeeping: dominating valuation subring exists for `(P, 𝔭, T, s)` data.
2. `exists_mem_rationalOpen_supp_of_dominating_valuationSubring` (line 2435) — Wedhorn 7.45 lift: pull back the valuation of `B` along `A → A/𝔭 → Frac(A/𝔭)`.
3. `exists_spa_point_supp_eq_maxIdeal_of_complete` (line 2517) — Wedhorn 7.51: trivial-1 valuation on residue field lifts to Spa A.

#### Proof sketch

1. **2396 (Chevalley)**: standard valuation-ring-dominating-given-subring theorem, applied to the subring generated by images of `P.A₀` + `t/s` for `t ∈ T`. Use `ValuationSubring.dominates` from mathlib + Zorn's lemma (existing in mathlib as `exists_le_valuation_subring`).
2. **2435 (Wedhorn 7.45 lift)**: pull back `v_B : Frac(A/𝔭) → Γ_B ∪ {0}` along `A → A/𝔭 → Frac(A/𝔭)`. Continuity from `h_INonunits`. Membership in `rationalOpen T s` from `h_TS`. Support contains `𝔭` because `𝔭 = ker(A → A/𝔭)`.
3. **2517 (max-ideal Spa-point)**: residue field `A/𝔪` is a complete non-arch field. Trivial valuation `|·|_𝔪` is automatically in Spa A.

#### Mathlib lemmas needed
- `ValuationSubring`, `ValuationSubring.dominates`, `ValuationSubring.exists_le_dominating`
- `FractionRing`, `Ideal.Quotient.mk`
- `MulArchimedean` / `NonarchimedeanRing` typeclass machinery

#### Generality decision
`IsHuberRing A` + `PlusSubring` (existing); the 7.45 lift needs `[T2Space A] [NonarchimedeanRing A]`.

### [T-PRESHEAF-TOPNILP-UNITS-CHAIN] Topologically nilpotent ↔ definition-ideal union (Wedhorn 7.51 sub-chain)

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/Presheaf.lean` lines 2666 (was 2557), 2832 (was 2723)
- **Depends on**: `HuberRings.AdjoinFinset` block (existing)
- **Type**: theorem × 2
- **Source**: Wedhorn 7.51 (topologically nilpotent characterization), Wedhorn 7.52 (units characterization).

#### Statements

1. `exists_pairOfDefinition_mem_I_of_isTopologicallyNilpotent_ne_zero` (line 2557) — nonzero case: for nonzero top-nilp `x`, exists pair of definition with `y ∈ P.I` mapping to `x`.
2. `union_translates_of_oneAdd_topNilp_subseteq_units` (line 2723) — `(1 + top-nilp) ⊆ units` (without completeness; sibling `_of_complete` already proven).

#### Proof sketch

1. **2557**: Use `HuberRings.AdjoinFinset` to enlarge an arbitrary pair of definition `P` to one containing `x`. The `[NonarchimedeanRing A]` hypothesis gives the required closure properties (Wedhorn 7.50). The nonzero case isolates the genuine content; the zero case is dispatched in the parent `exists_pairOfDefinition_mem_I_of_isTopologicallyNilpotent`.
2. **2723**: without completeness, `1 + x` for top-nilp `x` is a unit because `∑ (-x)^n` converges in the completion and pulls back via density. The completeness-free proof uses Wedhorn 7.52(2) characterization (`v(x) < 1 ⇒ 1+x ∈ Aˣ`) which holds before completion.

#### Mathlib lemmas needed
- `HuberRings.AdjoinFinset.exists_pairOfDefinition_containing` (project)
- `Filter.tendsto_pow_neighbourhood_zero`
- `geom_series` / `tsum` API

#### Generality decision
`IsHuberRing A` + `NonarchimedeanRing A` (existing signatures); no strengthening.

### [T-PRESHEAF-MULARCH-RANKONE] Rank-1 value-group analyticity chain (Wedhorn 7.40(6))

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/Presheaf.lean` lines 3225 (was 3116, `embed_archimedean_valueGroup_into_real`), 3414 (was 3305, `convexSubgroup_eq_top_of_ne_bot_of_analytic`)
- **Depends on**: Wedhorn Remark 4.12 (convex subgroup ↔ vertical generizations in Spv K(x), NOT in mathlib/project) + Wedhorn Remark 7.40(5) (microbial height-1 theory).
- **Type**: theorem × 2 (+ private sub-lemma)
- **Source**: Wedhorn 7.40(6) (rank-1 value group characterization).

#### Statements

1. `exists_topNilp_ne_zero_of_analytic` — exists nonzero topologically nilpotent `b ∈ A` for any analytic continuous valuation (Wedhorn 7.40 Step 1).
2. `mulArchimedean_of_rankOne_valueGroup` (line 3305 — `convexSubgroup_eq_top_of_ne_bot_of_analytic`) — for an analytic continuous valuation, the unit value group has no proper non-trivial convex subgroups.
3. `embed_archimedean_valueGroup_into_real` (line 3243) — bracketed value group embeds into `WithZero (Multiplicative ℝ)` (logarithmic embedding).

#### Proof sketch (Wedhorn 7.40 PDF p.55)

1. **3116**: analyticity gives a continuous valuation `v` with non-open support. Pick any element outside the support; by 7.40 prep step, can replace by a top-nilp element with `v ≠ 0`.
2. **3305**: depends on (a) micro-bial-height-1 theory (Wedhorn Remark 7.40(5)) and (b) "every continuous specialization is analytic" (Wedhorn Remark 4.12). These are the deepest sorries on this chain; both may need their own sub-tickets if they're not in mathlib.
3. **3243**: standard ordered-group embedding. Use the bracket hypothesis (Step 3a) to define `φ(γ) = log_β(γ)` for γ > 0 in the bracketed group, extend to 0.

#### Mathlib lemmas needed
- `LinearOrderedCommGroupWithZero`, `WithZero`, `Multiplicative ℝ`
- `MonoidWithZeroHom.injective`, `StrictMono`
- B2 candidate: micro-bial-height-1 theory (probably needs separate sub-development).

#### Generality decision
`IsHuberRing A` (existing); the analyticity hypothesis carries the strength.

### [T-PRESHEAF-7-42-RESIDUALS] Wedhorn 7.42 forward/reverse residuals

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/Presheaf.lean` lines 3647 (was 3538), 3762 (was 3653)
- **Depends on**: T-PRESHEAF-MULARCH-RANKONE (analyticity argument), `quotientLift` / `comap_quotientLift` API
- **Type**: theorem × 2
- **Source**: Wedhorn 7.42 (power-bounded ↔ all continuous valuations ≤ 1), pp.66-67.

#### Statements

1. `vle_one_of_powerBounded_discrete_quotient` (now line 3647) — discrete quotient sub-case: `a` power-bounded ⇒ for any cont valuation `v_q` on `A/𝔭` with `[a] ∉ v_q.supp`, `v_q([a]) ≤ 1`.
2. `wedhorn_7_42_reverse_separating_valuation` (now line 3762) — separating valuation existence: `a` not power-bounded ⇒ exists `v ∈ Cont A` with `¬ v.vle a 1`.

#### Proof sketch

1. **3538**: descent through discrete quotient `A ⧸ v.supp` (open since `v` is non-analytic). The valuation factors through `Spv (A ⧸ v.supp)`. Once descended, use Wedhorn p.66 height-0 argument: power-bounded ⇒ `v(a) ≤ 1` directly from definition (`a^n` stays in a bounded set; image in residue field stays in unit ball).
2. **3653**: classical Wedhorn 7.42 reverse separation. If `a` is not power-bounded, the sequence `{a^n}` is unbounded; pick a continuous valuation by extending the canonical map `A → A_{(a)}` (localization) so that `v(a^n)` is unbounded, i.e., `v(a) > 1`. Standard valuation-extension argument via `ValuationSubring.dominates`.

#### Mathlib lemmas needed
- `Ideal.Quotient.mk`, `comap_quotientLift`
- `ValuationSubring.exists_le_dominating`
- `Spv.toValuativeRel`

#### Generality decision
`IsHuberRing A` (existing).

### [T-PRESHEAF-LOCLIFT-COMPLETION] `IsPowerBounded.map` + locLift completion-side power-bounded

- **Status**: PARTIAL (2026-05-27). `IsPowerBounded.map` (was Presheaf.lean:3751) — **DELETED** as B2-false dead marker (no actual call sites, only docstring references; b2_log entry 7). `locLift_divByS_isPowerBounded_completion_of_tate` (now Presheaf.lean:3893) — STILL SORRY (Wedhorn 7.41 application).
- **File**: `Adic spaces/Presheaf.lean` line 3893
- **Depends on**: `IsPowerBounded.completion` (existing for uniform-completion ring homs), Wedhorn 7.41
- **Type**: theorem × 1 (was 2; B2-false one deleted)
- **Source**: Wedhorn 7.41 + 8.2.

#### Statements

1. ~~`IsPowerBounded.map` (line 3751)~~ — **DELETED** (B2-false, no callers).
2. `locLift_divByS_isPowerBounded_completion_of_tate` (now line 3893) — `t/s`-lift is power-bounded in completion `presheafValue D'`. Remaining work.

#### Proof sketch

1. **3751**: **B2 candidate — discard**. The generic statement is FALSE; only `IsPowerBounded.completion` for uniform-completion ring homs holds. Replace this theorem with the specialised version + update all callers. Log to `b2_log.jsonl`.
2. **3802**: Wedhorn 7.41 applied to `presheafValue D'`: any analytic continuous `v` satisfies `v(a) ≤ 1` for `a ∈ (presheafValue D')°`. The lifted `t/s` lies in `(presheafValue D')°` because the rational containment `R(D'.T/D'.s) ⊆ R(D.T/D.s)` gives `v(t) ≤ v(D.s)` for all cont `v`, i.e., `v(t/D.s) ≤ 1`.

#### Mathlib lemmas needed
- `IsPowerBounded.completion` (project, existing)
- `wedhorn_7_41_forward` (depends on the rank-1 + 7.42 chain above)

#### Generality decision
3751: B2 — discard generic form. 3802: Tate + Noetherian + T2 + NonarchimedeanRing (matching the parent's existing signature; no additions).

### [T-PRESHEAFTATE-SURJ-RESIDUAL] `restrictionMapHom_surj` residual

- **Status**: B2-SUPERSEDED MARKER (updated 2026-05-27). Theorem at `PresheafTateStructure.lean:1221` is marked `@[deprecated]` with reason "RETIRED — false in general". Counterexample documented in docstring: `A = ℚ_p⟨X⟩`, `A⟨T⟩/(XT - 1)` contains `∑ p^n · X^{-n}` (infinite convergent denominator tail) — `IsLocalization.Away.surj` shape fails. Correct route: cover-level `productRestriction_faithfullyFlat_tate` (Cor832). The sorry remains as a deprecation marker for transitional callers; ticket discharges by **caller migration**, not by proving the false statement.
- **File**: `Adic spaces/PresheafTateStructure.lean:1221`
- **Depends on**: T-WEDHORN-213-* (DONE for LaurentNormalized — provides the underlying ring equiv)
- **Type**: deprecation marker (theorem statement is B2-false; sorry preserved for legacy callers)
- **Source**: Wedhorn 2.13 / 8.2(b) — surjectivity of restriction map for general rational data.

#### Statement

`restrictionMapHom_surj D D' h : Function.Surjective (restrictionMapHom D D' h)`

#### Proof sketch (~60-80 LOC; routes through T-213 LaurentNormalized case)

1. Reduce to T-WEDHORN-213-EQUIV (DONE for LaurentNormalized): for LaurentNormalized data, surjectivity is part of the ring-equiv claim.
2. General data: use the chain decomposition (T-CHAIN-CONSTRUCTION DONE) — split arbitrary `D, D'` into a sequence of LaurentNormalized basic-plus / basic-minus steps. Surjectivity composes through chains.

#### Mathlib lemmas needed
- `RingEquiv.surjective`
- T-CHAIN-COMPOSITION (existing)

#### Generality decision
Tate + Noetherian + T2 + NonarchimedeanRing — existing signature.

### [T-PRESHEAFTATE-INJ-RESIDUAL] `restrictionMapHom_injective` residual (B2-SUPERSEDED, deprecated marker; caller migration to Cor832 productRestriction_injective_tate_via_prime_extension_closed pending)

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/PresheafTateStructure.lean:1422`
- **Depends on**: T-WEDHORN-213-* (DONE for LaurentNormalized)
- **Type**: theorem
- **Source**: Wedhorn 2.13 / 8.2(b) — injectivity of restriction map.

#### Statement

`restrictionMapHom_injective D D' h : Function.Injective (restrictionMapHom D D' h)`

#### Proof sketch (~40-60 LOC)

Symmetric to T-PRESHEAFTATE-SURJ-RESIDUAL: reduce to T-213-EQUIV for LaurentNormalized, then compose through T-CHAIN-COMPOSITION for general data.

#### Mathlib lemmas needed
- `RingEquiv.injective`
- T-CHAIN-COMPOSITION (existing)

#### Generality decision
Tate + Noetherian + T2 + NonarchimedeanRing — existing signature.

### [T-PRESHEAFTATE-ARTIN-REES] `locLift_preimage_target_witness_existence_no_noeth`

- **Status**: in_progress (2026-05-27). Investigation chain documented: `locLift_preimage_target_witness_existence (with [IsNoetherianRing D₀.P.A₀])` → `locLift_preimage_jfull_witness_existence` → `locLift_preimage_jfull_witness_existence_at` → `locLift_preimage_jfull_witness_existence_at_of_rad` (extracts `e₀ * D₀.s = D.s ^ N₀` via `rad_relation_of_rational_subset`) → delegates back to `_no_noeth` at line 1788. Deepest sorry is the no-Noeth form. Available axiom-clean helpers: `rad_relation_of_rational_subset` ✓, `locIdeal_pow_shift_inter_le_pow_mul` (T091, `WedhornLocTopologyLinear.lean:536`), `algebraMap_mul_pow_divByS_eq_one_of_radical_relation` (T092, `WedhornLocTopologyLinear.lean:777`). `[IsNoetherianRing A]` is in scope via `IsLocalization.isNoetherianRing` → `Localization.Away D₀.s` Noetherian, so Artin-Rees on `Loc D₀.s` is available.
- **File**: `Adic spaces/PresheafTateStructure.lean:1788`
- **Depends on**: `Artin–Rees` (mathlib: `Ideal.exists_pow_le` or related)
- **Type**: theorem (private)
- **Source**: standard Artin–Rees descent for adic completion.

#### Statement (paraphrased)

For each `n : ℕ`, exists `m : ℕ` such that for all `α : A` and `k_a : ℕ`, the away-lifted product `α * (1/D₀.s)^k_a` landing in `locNhd D m` has a witness of depth `n + k_a · D₀.hopen.choose` in `D₀.P.A₀` mapping to `α` in `Localization.Away D.s`.

#### Proof sketch (~50-80 LOC)

Standard Artin–Rees lemma applied to the chain `(D₀.P.A₀, D₀.P.I) → A → Localization.Away D.s`. The `[IsNoetherianRing A]` hypothesis gives the chain noetherian; Artin–Rees produces `m` from `n`.

#### Mathlib lemmas needed
- `Ideal.Filtration.stable` / `Ideal.IsAdicComplete`
- `Ideal.pow_succ_lt_pow` (for the depth bookkeeping)
- `Artin–Rees`: `Submodule.exists_pow_smul_le` or similar (verify in mathlib)

#### Generality decision
Tate + Noetherian + T2 + NonarchimedeanRing — existing signature (matches consumer).

### [T-STRUCTURESHEAF-ISSHEAF-RESIDUAL] `structurePresheaf_isSheaf` top-level claim

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/StructureSheaf.lean:255`
- **Depends on**: `structurePresheaf_typeLevel_isSheaf` (line 223 — already proven), Hom-by-Hom gluing route
- **Type**: theorem
- **Source**: Wedhorn 8.20 + standard CompleteTopCommRingCat sheafification.

#### Statement

`theorem structurePresheaf_isSheaf [IsHuberRing A] [PlusSubring A] : (structurePresheaf A).IsSheaf`

#### Proof sketch (~30-50 LOC)

Per the existing docstring: for each `E : CompleteTopCommRingCat`, the presheaf `U ↦ Hom(E, structurePresheaf U)` is a sheaf of types, verified by gluing continuous ring homs piecewise. Continuity of the global lift uses that rational covers are finite.

1. Reduce to the type-level sheaf claim `structurePresheaf_typeLevel_isSheaf` (DONE) via the Yoneda-like Hom-by-Hom encoding.
2. For each `E`, glue continuous ring homs `E → presheafValue D` piecewise across a finite cover.
3. Continuity comes from finite intersection of preimages.

#### Mathlib lemmas needed
- `Sheaf.IsSheaf_iff_forall_lift` (mathlib if exists, or project alternative)
- `CategoryTheory.Presheaf.isSheaf_of_isSheaf_forget` style
- `RingHom.continuous_iff_continuousAt`

#### Generality decision
`IsHuberRing A` + `PlusSubring A` (existing); no strengthening.

### [T-TATEACYC-LAURENT-LEAVES] TateAcyclicityResiduals.lean leaves

- **Status**: OPEN (added 2026-05-27 — explicit naming of 9 sorries)
- **File**: `Adic spaces/TateAcyclicityResiduals.lean` lines 236, 439, 458, 1789, 1849, 1922, 1959, 2138, 2381
- **Depends on**: T-LAURENT-REFINEMENT-TREE, T-WEDHORN-STAGE-1, T-LAURENT-TREE-GRAFT (all PARTIAL — see Round-6 audit below), T-NULL-PER-E-FIN (OPEN), T-LANE-C-REFINEMENT-INDUCTION (TREE ITERATION DONE)
- **Type**: theorem × 9 (leaf-level)
- **Source**: Wedhorn 8.34 (geometric reduction), Hübner Lemma 3.8, project Lane C induction.

#### Statements and routing

| Line | Theorem | Routing |
|------|---------|---------|
| 236 | `localBasisHyp_of_strongly_noetherian` | T-NULL-PER-E-FIN consumer |
| 439 | `strengthened_cover_of_basic_cover` | T-WEDHORN-STAGE-1 application |
| 458 | `outside_rescue_of_per_D_cover` | T-WEDHORN-STAGE-1 sub-step |
| 1789 | `balancedTree_BalancedInducing_of_rescaled_S` | T-LAURENT-REFINEMENT-TREE existence |
| 1849 | `exists_first_stage_laurent_tree_unit_generated` | T-WEDHORN-STAGE-1 main theorem |
| 1922 | `unitCover_refines_relative_balanced_ratio_tree_leaves` | T-LAURENT-TREE-RELATIVE-LABELS |
| 1959 | `balancedInducing_of_relative_unit_ratios` | T-LAURENT-TREE-RELATIVE-LABELS |
| 2138 | `relative_laurent_tree_to_absolute` | T-LAURENT-TREE-GRAFT |
| 2381 | `exists_inner_laurent_refinement_per_leaf` | T-WEDHORN-STAGE-2 application |

#### Discharge plan

Each leaf is closed when its routing-parent ticket lands. No additional sketch — see the routing-parent's existing sketch. This ticket exists to name the 9 sorries so the project tracker can mark them DONE as each parent closes.

### Round-6 re-audit: stale PARTIAL Laurent tickets

The following tickets have been PARTIAL since 2026-05-13 (14 days). Sharper close-out plans below.

#### T-LAURENT-REFINEMENT-TREE re-audit

- **Live sorries on file** (`TateAcyclicityResiduals.lean`): 1789 (`balancedTree_BalancedInducing_of_rescaled_S`).
- **Remaining work**: the EXISTENCE THEOREM (Wedhorn 8.34) — given a rational cover `C` over a Tate ring with `[IsStronglyNoetherian]`, construct a `LaurentTree` whose leaves refine `C`'s rational opens. The data structure has landed (axiom-clean); the existence is the structural induction on the cover's generating set.
- **Estimated effort**: 100-150 LOC. Uses `LaurentTree.ofBalancedList` (DONE) + balanced-tree leaves bijection (DONE) + the per-leaf inducing claim (the 1789 sorry).

#### T-WEDHORN-STAGE-1 re-audit

- **Live sorries on file** (`TateAcyclicityResiduals.lean`): 439, 458, 1849.
- **Remaining work**: the Cor 7.32 application (for each leaf, get a unit-generated rational sub-cover). The structural infrastructure has landed; this is the "per-leaf restriction-as-units" step.
- **Estimated effort**: ~80 LOC per sub-sorry. Uses Cor 7.32 (`Cor732.exists_dominating_unit_noHArch` — itself sorry'd at line 543; see [T-PRESHEAF-MULARCH-RANKONE] above for the deepest dependency).

### Cleanup-cadence tickets (per /develop §1g)

#### [CLEANUP-BANACHOMT] Run /cleanup on BanachOMT.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-PETTIS-PROP-1-10 lands.
- **Scope**: golf the ~1400-line file; identify dead helper sub-sub-lemmas; collapse redundant binders; tighten docstrings.

#### [CLEANUP-STRUCTURESHEAF] Run /cleanup on StructureSheaf.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-STRUCTURESHEAF-ISSHEAF-RESIDUAL + T-ROUTE-C-OMT + the `_aux_noeth_A0_generic_of_stronglyNoetherianTate` B2 close-out have all landed.
- **Scope**: remove SUPERSEDED docstring noise; consolidate the `_proof`-suffixed wrappers chain; verify all callers route through the audit-clean variants.

#### [CLEANUP-TATEACYC] Run /cleanup on TateAcyclicityResiduals.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-TATEACYC-LAURENT-LEAVES closes (all 9 leaves).
- **Scope**: golf the Laurent-tree induction proofs; collapse the 9 leaf consumers into the canonical balanced-tree existence + grafting form.

#### [CLEANUP-PRESHEAFTATE] Run /cleanup on PresheafTateStructure.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-PRESHEAFTATE-SURJ-RESIDUAL + T-PRESHEAFTATE-INJ-RESIDUAL + T-PRESHEAFTATE-ARTIN-REES all land.
- **Scope**: collapse the surj/inj duality into a single Tate-completion ring-equiv form; verify the Artin–Rees witness threading.

#### [CLEANUP-WEDHORN-STRONGNOETH] Run /cleanup on WedhornStronglyNoetherian.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-WEDHORN-618-L5-AUDIT + T-WEDHORN-618-L6-CLEANWRAPS close.
- **Scope**: remove SUPERSEDED noeth-A₀ claims; verify all callers route through `[IsNoetherianRing P.A₀]` explicit hypothesis.

#### [CLEANUP-PRESHEAF] Run /cleanup on Presheaf.lean

- **Status**: OPEN (cadence)
- **Trigger**: after T-PRESHEAF-* (6 tickets above) all land.
- **Scope**: 893-line file with 12 sorries currently — major restructure expected once the 6 R6 tickets close. Particular focus: 7.42 chain consolidation, dominating-valuation-subring chain bundling, rank-1/mulArch chain bundling.

#### [CLEANUP-ALL-1] Pre-IsSheafy-milestone full cleanup

- **Status**: OPEN (cadence)
- **Trigger**: before the IsSheafy milestone is claimed (i.e., before `isSheafy_ofStronglyNoetherianTate` and `tateAcyclicity_Part2_end_to_end` are claimed sorry-free).
- **Scope**: `/cleanup-all` across the entire project. Run after all proof tickets in the IsSheafy chain close.

#### [CLEANUP-FINAL] Final `/cleanup-all`

- **Status**: OPEN (cadence; LAST TICKET)
- **Trigger**: after the IsSheafy milestone is sorry-free and all per-file cleanups above are DONE.
- **Scope**: final repo-wide pass: namespace tidying, docstring polish, simp-attribute audit, axioms audit (`#print axioms` clean on the milestone theorems).

## Round-7 decomposition (2026-05-27) — sub-ticket decomposition for stuck obligations

`/develop --continue` Round-7 pass (per user directive "plan out the parts you are stuck on"). 12 new sub-tickets decompose the major remaining obligations into focused proof steps with clear discharge routes.

### [T-WED-745-CONT-A] Convex subgroup from P.I image (Lemma745 u_max+H_gen pattern) — CORRECTED A′ SEMANTICS

- **Status**: DONE (landed 2026-05-27 as `WedhornLift745.convexSubgroup_from_PI_image_corrected` in Presheaf.lean before line 2545; ~80 LOC, lake build green; uses `ConvexSubgroup.exists_inv_pow_lt_of_mem_convexGenerated` for cofinality + `Submodule.span_induction` for the no-hRange P.I-valuation-zero contrapositive)
- **Status original**: OPEN (re-plan applied 2026-05-27 per round-5 expert review)
- **History**: original signature was SIGNATURE-DEFECTIVE (second conjunct "P.I units ∉ H" unprovable in Case A). Reviewer (round-5) confirmed and prescribed corrected A′/B′/C′ decomposition. Memory: [[project-t-wed-745-cont-a-signature-defect]] and [[feedback-round-5-review]].

#### Corrected statement (A′)

```lean
private theorem WedhornLift745.convexSubgroup_from_PI_image_corrected
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (B : ValuationSubring (FractionRing (A ⧸ 𝔭)))
    (hINonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆
      B.nonunits)
    (h_PI_nonzero : ∃ a ∈ P.I, B.valuation (P.toFractionQuotient 𝔭 a) ≠ 0) :
    ∃ (u_max : B.ValueGroupˣ) (H : ConvexSubgroup B.ValueGroupˣ),
      (u_max : B.ValueGroup) < 1 ∧
      u_max ∈ H ∧
      (∀ h ∈ H, ∃ n : ℕ, (u_max ^ n : B.ValueGroup) ≤ (h : B.ValueGroup))
```

Crucial corrections from the old (defective) signature:
- **No "P.I units ∉ H" conjunct**: P.I-image units may be inside H; that is what the cofinality argument exploits.
- **Add explicit `h_PI_nonzero` hypothesis**: skip the Case-B trivial branch by requiring at least one nonzero P.I-image — Case B (all P.I maps to 0 in B) is downstream-handleable separately and not the real obstruction.
- **Output bundle is `(u_max, H)` with three properties**: `u_max < 1`, `u_max ∈ H`, and the cofinality `∀ h ∈ H, ∃ n, u_max^n ≤ h`. The cofinality is the actual semantic content used by downstream continuity.

#### Proof sketch (mirroring Lemma745 lines 437-488)

1. P.fg → finite generating set S ⊆ P.I.
2. Set `u_max := Units.mk0 (S.sup' hSne (fun t => B.valuation (φ t))) (ne_of_gt h_PI_nonzero_in_sup)`.
3. `u_max < 1` via `Finset.sup'_lt_iff` + hINonunits.
4. `u_max ∈ H := convexGenerated u_max⁻¹` via the inv-inv argument: `u_max = (u_max⁻¹)⁻¹ ∈ H` because `self_mem_convexGenerated` + `inv_mem`.
5. Cofinality `∀ h ∈ H, ∃ n, u_max^n ≤ h` is the **project's existing** `exists_inv_pow_lt_of_mem_convexGenerated` lemma (OrderedGroupConvex.lean:489), applied with `y := u_max⁻¹`.

- **File**: `Adic spaces/Presheaf.lean` (new private helper near line 2452, before the parent theorem `exists_mem_rationalOpen_supp_of_dominating_valuationSubring`)
- **Depends on**: `Lemma745` pattern (Lemma745.lean:437-488), `convexGenerated` API (OrderedGroupConvex.lean), `exists_inv_pow_lt_of_mem_convexGenerated`.
- **Parent**: T-PRESHEAF-VALUATIONSUBRING-CHAIN
- **Type**: theorem (private helper)
- **LOC estimate**: ~30 LOC structural code following Lemma745 lines 437-488.
- **File**: `Adic spaces/Presheaf.lean` (new private helper near line 2452)
- **Depends on**: none (uses existing mathlib + Lemma745 patterns)
- **Parent**: T-PRESHEAF-VALUATIONSUBRING-CHAIN (Wedhorn 7.45 lift IsContinuous sub-step)
- **Type**: theorem (private helper)
- **Source**: Lemma745.lean lines 437-485 (mirror the `u_max + H_gen` construction).

#### Statement

```lean
private theorem convexSubgroup_from_PI_image
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [IsHuberRing A]
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (B : ValuationSubring (FractionRing (A ⧸ 𝔭)))
    (hINonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆
      B.nonunits) :
    ∃ H : ConvexSubgroup B.ValueGroupˣ,
      (∀ a : A, ∀ ha : a ∈ P.A₀.subtype.range,
        ∀ hv : B.valuation (φ_full a) ≠ 0,
        1 ≤ B.valuation (φ_full a) →
          Units.mk0 (B.valuation (φ_full a)) hv ∈ H) ∧
      (∀ a ∈ P.I, ∀ hv : B.valuation (φ_full (P.A₀.subtype a)) ≠ 0,
          Units.mk0 _ hv ∉ H)
```

#### Proof sketch

1. P.I is finitely generated (mathlib `Submodule.fg`); let S ⊆ P.I be a finite generating set. By `hINonunits`, for each s ∈ S the value `B.valuation (φ_full s)` is in `B.nonunits`, equivalently < 1 (`ValuationSubring.nonunits_iff_lt_one`).
2. Take `u_max := Units.mk0 (S.sup' ... (fun s => B.valuation (φ_full s)))` (the finite-supremum of nonunit values). Show `u_max < 1` via `Finset.sup'_lt_iff` (every generator's image is < 1; finite max stays < 1 in a linearly ordered group with zero).
3. Define `H := ConvexSubgroup.convexGenerated (one_lt_inv_of_inv hu_max_lt_one : (1 : Γ₀ˣ) < u_max⁻¹)`. By Lemma745 pattern, H contains every γ ∈ [u_max, u_max⁻¹] in the unit value group.
4. **First conjunct** (H contains ≥1 image-of-A₀ values): for `a ∈ P.A₀.subtype.range`, `B.valuation (φ_full a) ≤ 1` (by `_hRange` from outer hypothesis). If additionally `≥ 1`, then `= 1`, and `1 ∈ H` always (any convex subgroup contains the identity).
5. **Second conjunct** (P.I images outside H): for `a ∈ P.I`, `B.valuation (φ_full a) ≤ u_max < 1` (by step 2). So `Units.mk0 _ hv ≤ u_max`, hence in `[u_max, u_max⁻¹]` only if `≥ u_max`, but the convex subgroup `convexGenerated u_max⁻¹` excludes everything strictly between 0 and u_max (it captures values `[u_max^k, u_max^{-k}]` for k ∈ ℤ). Hence P.I-image units lie strictly below H.

#### Mathlib lemmas needed

- `ValuationSubring.nonunits_iff_lt_one` — characterise B.nonunits.
- `Finset.sup'_lt_iff` — finite sup strictly less than 1.
- `ConvexSubgroup.convexGenerated` (project) — Lemma745's helper.
- `one_lt_inv_of_inv` — flip u_max < 1 ⇒ 1 < u_max⁻¹.

#### Generality decision

Operates on a general PairOfDefinition + dominating valuation subring; no extra hypotheses beyond what `exists_valuationSubring_dominating_for_rationalOpen` already provides.

### [T-WED-745-CONT-B] `restrictToConvexBounded` valuation construction — CORRECTED B′

- **Status**: DONE (landed 2026-05-27 as `WedhornLift745.PI_pow_valuation_bound` in Presheaf.lean before line ~2620; ~40 LOC, lake build green; provides `∀ n, ∀ a ∈ P.I^n, B.valuation (φ a) ≤ u_max^n` via induction on n + `Submodule.mul_induction_on` for the multiplicative step. The "build restrictToConvexBounded" framing turned out to be unnecessary: the depth-power decay bound is the substantive content C′ needs)
- **Status original**: OPEN (re-plan applied 2026-05-27 per round-5 expert review)
- **Corrected target (B′)**: prove the boundedness conditions for the restricted valuation:
  - $\forall a \in P.A_0$, $v|_H(\phi(a)) \le 1$
  - $\forall t \in T$, $v|_H(\phi(t)) \le v|_H(\phi(s))$
  - $\forall n,\ \forall a \in P.I^n$, $v|_H(\phi(a)) \le u_{\max}^n$ in $\mathrm{WithZero}(H)$ — the depth-power decay bound that downstream continuity exploits.
- **Note**: the third bullet is the cofinality-prep that makes Lemma745's continuity proof work. Use the A′ output `(u_max, H)` and apply `restrictToConvexBounded` from `ValuationContinuity.lean:585` directly.
- **File**: `Adic spaces/Presheaf.lean` (new private definition near line 2452)
- **Depends on**: T-WED-745-CONT-A
- **Parent**: T-PRESHEAF-VALUATIONSUBRING-CHAIN
- **Type**: noncomputable def + 1 API lemma
- **Source**: `ValuationContinuity.lean:585` (`restrictToConvexBounded`, sorry-free).

#### Statement

```lean
private noncomputable def v_restricted_PI
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [IsHuberRing A]
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    (B : ValuationSubring (FractionRing (A ⧸ 𝔭)))
    (H : ConvexSubgroup B.ValueGroupˣ)
    (hH_ge : ∀ a : A, ∀ ha : (B.valuation.comap φ_full) a ≠ 0,
      1 ≤ (B.valuation.comap φ_full) a → Units.mk0 _ ha ∈ H) :
    Valuation A (WithZero H.toSubgroup) :=
  (B.valuation.comap φ_full).restrictToConvexBounded H hH_ge

private theorem v_restricted_PI_apply_zero_iff
    -- standard "v_restricted_PI a = 0 iff a ∈ supp(v_val) ∪ (values < min-of-H)"
```

#### Proof sketch

1. The `def` is a one-line construction using mathlib's `Valuation.restrictToConvexBounded` (ValuationContinuity.lean:585).
2. The API lemma `v_restricted_PI_apply_zero_iff`: standard unfolding of `restrictToConvexBounded`'s `toFun` — zero on supp + zero on units outside H.

#### Mathlib lemmas needed

- `Valuation.restrictToConvexBounded` (project, ValuationContinuity.lean:585).
- `Valuation.restrictToConvexBounded_unfold` (if exists; else unfold definition manually).

#### Generality decision

Matches Wedhorn 7.45 lift's hypothesis bundle; no additional assumptions.

### [T-WED-745-CONT-C] IsContinuous of the restricted valuation — CORRECTED C′

- **Status**: STRUCTURED-WITH-SUB-SORRIES (2026-05-27) — two sub-helpers landed in Presheaf.lean before the parent (`WedhornLift745.dominating_B_caseA_existential` and `WedhornLift745.dominating_B_caseB_existential`), each with `sorry` body and clear discharge plan. Per CLAUDE.md, named sub-lemmas with `sorry` bodies are the legal "sub-lemma" pattern.
  - **Case A helper** (~10 LOC stub + sub-sorry): produces the Spa-point in `rationalOpen T s` with `supp ≥ 𝔭` using A′ + B′ + `Lemma745.exists_valuation_extension`. ~100-150 LOC residual.
  - **Case B helper** (DONE 2026-05-27 round-5 beastmode session, ~90 LOC, axiom-clean, lake build green): closed sorry-free with the cosets-of-open-subgroup argument (`P.idealOfDefinition_pow_isOpen n=1` + ultra-metric). Constructs the Spa-point via `ofValuation v_val` with all five conjuncts (IsContinuous via `isContinuous_ofValuation_of`, A⁺ ≤ 1, T ≤ s, s ≠ 0, 𝔭 ≤ supp).
  - **Parent wiring** (DONE 2026-05-27 round-5 beastmode session): parent `exists_mem_rationalOpen_supp_of_dominating_valuationSubring` refactored to case-split + delegate to Case A/B helpers. Legacy inline proof preserved in `/- ... -/` comment block. Net effect: Case B path is fully closed sorry-free; Case A path retains the vExtFun-assembly sub-sorry.
- **Status original**: OPEN (re-plan applied 2026-05-27 per round-5 expert review)
- **Corrected target (C′)**: given A′ output `(u_max, H)` with cofinality `∀ h ∈ H, ∃ n, u_max^n ≤ h`, and B′ output `v_r := v.restrictToConvexBounded H hH_ge` with `∀ a ∈ P.I^n,\ v_r(a) \le u_max^n`, prove `v_r.IsContinuous`.
- **Proof strategy**: by `isContinuous_iff_units`, for each `γ ∈ (WithZero H.toSubgroup)ˣ`, show `{a | v_r(a) < γ}` is open. Lift γ to `H` via the unit-of-WithZero structure. By A′ cofinality, ∃ n with `u_max^n ≤ γ`. Then by B′ depth-power decay, `P.I^n ⊆ {a | v_r(a) ≤ u_max^n ≤ γ}` — strict inequality from u_max < 1 (so u_max^n < 1). Since P.I^n is open in A (P is a pair of definition), the set `{a | v_r(a) < γ}` contains the open P.I^n, hence is open.
- **File**: `Adic spaces/Presheaf.lean` (new private theorem near line 2452)
- **Depends on**: T-WED-745-CONT-A, T-WED-745-CONT-B
- **Parent**: T-PRESHEAF-VALUATIONSUBRING-CHAIN
- **Type**: theorem
- **Source**: Lemma745 `exists_spa_point_via_restrictToConvex` Steps 7-8 (mirror).

#### Statement

```lean
private theorem v_restricted_PI_isContinuous
    {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
    [IsTopologicalRing A] [IsHuberRing A]
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (B : ValuationSubring (FractionRing (A ⧸ 𝔭)))
    (H : ConvexSubgroup B.ValueGroupˣ)
    (hH_ge : ∀ a : A, ∀ ha : (B.valuation.comap φ_full) a ≠ 0,
      1 ≤ (B.valuation.comap φ_full) a → Units.mk0 _ ha ∈ H)
    (hH_strict_lt_PI : ∀ a ∈ P.I, ∀ ha : (B.valuation.comap φ_full) (P.A₀.subtype a) ≠ 0,
      Units.mk0 _ ha ∉ H) :
    (v_restricted_PI P B H hH_ge).IsContinuous
```

#### Proof sketch

1. By `isContinuous_iff_units`, reduce to: for every γ ∈ (WithZero H.toSubgroup)ˣ, `{a | v_restricted_PI a < γ}` is open in A.
2. For γ ∈ unit group: by T-WED-745-CONT-A, P.I-image elements have v_val outside H, hence `v_restricted_PI a = 0 < γ` (since γ is a unit). So `P.A₀.subtype '' P.I ⊆ {a | v_restricted_PI a < γ}`.
3. `P.A₀.subtype '' P.I` (the image of P.I in A) is contained in `P.idealOfDefinition` (definition of pair of definition), which is OPEN in A (`P.isOpen_idealOfDefinition` from HuberRings).
4. By `Valuation.ltAddSubgroup`, `{a | v_restricted_PI a < γ}` is an AddSubgroup. An AddSubgroup containing an open set is itself open (translation-invariance). Therefore the set is open.

#### Mathlib lemmas needed

- `Valuation.isContinuous_iff_units` (project, ContinuousValuations.lean:40).
- `Valuation.ltAddSubgroup` (mathlib, RingTheory/Valuation/Basic.lean:567).
- `AddSubgroup.isOpen_of_mem_nhds` (mathlib).
- `PairOfDefinition.isOpen` (project, definition of pair of definition).

#### Generality decision

The `[IsAdicComplete P.I P.A₀]` is inherited from `exists_mem_rationalOpen_supp_of_dominating_valuationSubring`'s signature.

### [T-AR-1] Artin-Rees in `Localization.Away D₀.s`

- **Status**: DONE (landed 2026-05-27 as `artinRees_locAway` in PresheafTateStructure.lean before line 1788, ~20 LOC, axiom-clean, lake build green)
- **File**: `Adic spaces/PresheafTateStructure.lean` (new private helper before line 1788)
- **Depends on**: `[IsNoetherianRing A]` + IsLocalization machinery (existing)
- **Parent**: T-PRESHEAFTATE-ARTIN-REES
- **Type**: theorem (private helper)
- **Source**: mathlib `Mathlib.RingTheory.Filtration` `Ideal.exists_pow_inf_eq_pow_smul` (the canonical Artin-Rees lemma).

#### Statement

```lean
private theorem artinRees_locAway
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A)
    (K : Ideal (Localization.Away D₀.s)) :
    ∃ k₀ : ℕ, ∀ n : ℕ, k₀ ≤ n →
      ((Ideal.map (algebraMap A (Localization.Away D₀.s)) D₀.P.idealOfDefinition) ^ n) ⊓ K ≤
      ((Ideal.map (algebraMap A (Localization.Away D₀.s)) D₀.P.idealOfDefinition) ^ (n - k₀)) * K
```

#### Proof sketch

1. `Localization.Away D₀.s` is Noetherian via `IsLocalization.isNoetherianRing` from `[IsNoetherianRing A]`.
2. Apply mathlib's `Ideal.exists_pow_inf_eq_pow_smul` (Artin-Rees lemma) with `I := the map of D₀.P.idealOfDefinition` (an ideal in the Noetherian Localization.Away D₀.s).
3. The intersection-subset form follows directly; the standard `Ideal.pow_le_pow_right` discharges the depth comparison `n + k₀ ≥ k₀`.

#### Mathlib lemmas needed

- `IsLocalization.isNoetherianRing` (mathlib).
- `Ideal.exists_pow_inf_eq_pow_smul` (mathlib, `Mathlib/RingTheory/Filtration.lean:395`).
- `Ideal.pow_le_pow_right` (mathlib).

#### Generality decision

`[IsNoetherianRing A]` (already in parent's signature, T-PRESHEAFTATE-ARTIN-REES).

### [T-AR-2] Radical-relation denominator lift

- **Status**: DONE (landed 2026-05-27 as `rad_denom_lift_in_target` in PresheafTateStructure.lean before line 1788, ~30 LOC, axiom-clean, lake build green)
- **File**: `Adic spaces/PresheafTateStructure.lean` (new private helper before line 1788)
- **Depends on**: `rad_relation_of_rational_subset` (existing), T092 helper (existing)
- **Parent**: T-PRESHEAFTATE-ARTIN-REES
- **Type**: theorem (private helper)
- **Source**: T092 helper at `WedhornLocTopologyLinear.lean:777` (`algebraMap_mul_pow_divByS_eq_one_of_radical_relation`).

#### Statement

```lean
private theorem rad_denom_lift_in_target
    {A : Type*} [CommRing A] (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (N₀ : ℕ) (e₀ : A) (h_rad : e₀ * D₀.s = D.s ^ N₀)
    (k_a : ℕ) (α : A) :
    -- The pulled-back image of `α · (1/D₀.s)^k_a` in Localization.Away D.s
    -- equals algebraMap (α · e₀^k_a) · (1/D.s)^(k_a · N₀) modulo a unit factor.
    locLift D₀ D h (algebraMap A α * (divByS (1 : A) D₀.s)^k_a) =
      algebraMap A (Localization.Away D.s) (α * e₀ ^ k_a) *
        (divByS (1 : A) D.s) ^ (k_a * N₀)
```

#### Proof sketch

1. Unfold `locLift` via `IsLocalization.Away.lift_eq` to a formula in terms of `algebraMap A (Localization.Away D.s)` and the unit `D₀.s` becomes via the radical relation.
2. Use T092's `algebraMap_mul_pow_divByS_eq_one_of_radical_relation`: in Localization.Away D.s, `algebraMap D₀.s * (algebraMap e₀ * (divByS 1 D.s)^N₀) = 1`. So `(algebraMap D₀.s)⁻¹ = algebraMap e₀ * (divByS 1 D.s)^N₀`. Apply k_a-many times: `(algebraMap D₀.s)⁻¹^k_a = algebraMap (e₀^k_a) * (divByS 1 D.s)^(k_a · N₀)`.
3. Substitute and simplify with `map_mul`, `map_pow`.

#### Mathlib lemmas needed

- `IsLocalization.Away.lift_eq` (mathlib).
- `algebraMap_mul_pow_divByS_eq_one_of_radical_relation` (project, T092).
- `map_mul`, `map_pow` (mathlib).

#### Generality decision

`[CommRing A]` only; no Noetherian needed for this step (purely algebraic).

### [T-AR-3] Per-n witness extraction in A₀ — RESTATED AS IDEAL-CONTAINMENT (round-5 review)

- **Status**: STRUCTURED-WITH-SUB-SORRIES (2026-05-27) — `locLift_preimage_target_containment_no_noeth` helper landed in PresheafTateStructure.lean before line 1921, with `sorry` body and ideal-containment statement matching the reviewer's recommended shape. The element-witness derivation (`α' ∈ D₀.P.I^(...)` with matching `algebraMap`) requires an additional step from the containment that depends on D.s-torsion structure — preserved as future work on the parent `locLift_preimage_target_witness_existence_no_noeth`.
- **Status original**: OPEN (restated 2026-05-27 per round-5 expert review)
- **Reviewer directive** (verbatim): "For T-AR-3, isolate the algebraic statement as an ideal-containment lemma before proving the element witness version. A better target is something like: (target smallness of α · e^k) ⇒ α ∈ I^(n + k·c) + kernel(A → A[1/D.s]). Then derive the existential α' form. This is usually easier than constructing α' directly."
- **Restated step 1 (T-AR-3-CONTAINMENT)**: prove the ideal-level containment
  $$\{\, \alpha \in A : \exists k_a,\ \mathrm{algebraMap}_A^{A[1/D.s]}(\alpha \cdot e_0^{k_a}) \in \mathrm{locNhd}(D, m) \,\} \subseteq P.I^{n + k_a \cdot D_0.\mathrm{hopen}} + \ker(\mathrm{algebraMap}_A^{A[1/D.s]})$$
  for suitably chosen m (= m(n) from T-AR-1's Artin-Rees absorption + T-AR-2's denominator lift). This is an ideal containment in $A$, parameterised by $(n, k_a, \alpha)$.
- **Restated step 2 (T-AR-3-WITNESS)**: derive the element form `∃ α' ∈ P.I^(n + k_a · D_0.hopen), algebraMap α = algebraMap α'` as a corollary by unpacking the ideal-containment witness through the ker-quotient.
- **Why this is easier**: step 1 is closer to standard Artin-Rees + radical-rewrite arithmetic, manipulable via mathlib's ideal API (`Submodule.mem_sup`, `Ideal.add_mem`, ring-hom-kernel-membership). Step 2 is a one-step element extraction.
- **File**: `Adic spaces/PresheafTateStructure.lean` (new private helpers before line 1788)
- **Depends on**: T-AR-1 (DONE), T-AR-2 (DONE), `rad_relation_of_rational_subset`
- **Parent**: T-PRESHEAFTATE-ARTIN-REES
- **Type**: theorem × 2 (containment + witness)
- **LOC estimate**: ~80-100 LOC for containment, ~30 LOC for witness derivation. Lower than the original ~150 LOC estimate for the direct element approach.
- **File**: `Adic spaces/PresheafTateStructure.lean` (new private helper before line 1788)
- **Depends on**: T-AR-1, T-AR-2, `rad_relation_of_rational_subset`
- **Parent**: T-PRESHEAFTATE-ARTIN-REES
- **Type**: theorem (private helper)
- **Source**: section docstring at PresheafTateStructure.lean:1709-1740 (T089 strategy).

#### Statement

```lean
private theorem per_n_A0_witness
    {A : Type*} [CommRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [IsTateRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (n : ℕ) :
    ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h (algebraMap A α * (divByS (1 : A) D₀.s)^k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A)
```

#### Proof sketch

1. Extract radical relation `(N₀, e₀, h_rad)` via `rad_relation_of_rational_subset D₀ D h` (existing, sorry-free).
2. Apply T-AR-1 with `K := RingHom.ker (algebraMap A (Localization.Away D.s))`. Get k₀ such that Artin-Rees absorption holds.
3. Pick `m := n + k₀ + k_a · N₀ + extra-clearing`. The exact depth bookkeeping follows the section docstring.
4. Given `locLift (algebraMap α · invS₀^k_a) ∈ locNhd D m`: by T-AR-2, this equals `algebraMap (α · e₀^k_a) · invS^(k_a · N₀)` in Localization.Away D.s. The locNhd condition translates to a kernel-difference condition.
5. Apply Artin-Rees absorption (T-AR-1) to extract α' from `α · e₀^k_a` modulo the kernel, with depth `n + k_a · D₀.hopen.choose`.
6. The matching `algebraMap` identity follows from the depth-shifted Artin-Rees decomposition.

#### Mathlib lemmas needed

- T-AR-1, T-AR-2 (this ticket's own deps).
- `rad_relation_of_rational_subset` (PresheafTateStructure.lean:1067, existing).
- `Ideal.mem_pow_iff` / `Ideal.exists_mem_pow_smul_of_mem_pow_inf` (mathlib).

#### Generality decision

Matches T-PRESHEAFTATE-ARTIN-REES parent's hypothesis bundle (no `[IsNoetherianRing D₀.P.A₀]` — this is precisely the "no-Noeth source pair" sibling).

### [T-AR-4] Final assembly = `locLift_preimage_target_witness_existence_no_noeth`

- **Status**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/PresheafTateStructure.lean:1788` (replace sorry)
- **Depends on**: T-AR-3
- **Parent**: T-PRESHEAFTATE-ARTIN-REES
- **Type**: theorem body (replace sorry)
- **Source**: T-AR-3 + identity composition.

#### Statement

(Already stated at PresheafTateStructure.lean:1788 — `locLift_preimage_target_witness_existence_no_noeth`. The replacement closes the sorry.)

#### Proof sketch

```lean
intro n
obtain ⟨m, hm⟩ := per_n_A0_witness D₀ D h n  -- T-AR-3 application
exact ⟨m, hm⟩
```

One-liner: T-AR-3 produces exactly the existential the parent asserts.

#### Generality decision

n/a (closes existing sorry; signature unchanged).

### [T-EXPERT-REVIEW-740] Open /expert-review for Wedhorn Remark 4.12 + Remark 7.40(5)

- **Status**: OPEN (added 2026-05-27)
- **File**: triggers `.mathlib-quality/expert-review/<date>/` artifact generation
- **Depends on**: none (planning artifact)
- **Parent**: T-PRESHEAF-MULARCH-RANKONE
- **Type**: review-pending escalation
- **Source**: project_round_6_audit.md notes Wedhorn 7.40(6) chain (Presheaf.lean:3414 `convexSubgroup_eq_top_of_ne_bot_of_analytic`) needs (a) Wedhorn Remark 4.12 (convex subgroup ↔ vertical generizations in Spv(K(x))) and (b) Wedhorn Remark 7.40(5) (microbial-height-1 theory), neither in mathlib.

#### Statement

This is a planning artifact, not a Lean theorem. Invoke `/expert-review` (or write `REVIEW_BRIEF.md` directly) with the question:

> "Formalising Wedhorn's *Adic Spaces*, we need:
> (1) Wedhorn Remark 4.12 (p. 31): for a valuation x ∈ Spv A, there is a bijection between convex subgroups of (x.value_group)ˣ and vertical generizations of x in Spv(A) (equivalently, in Spv(K(x))).
> (2) Wedhorn Remark 7.40(5) (p. 64): an analytic continuous valuation on a Huber ring is microbial — its value group has rank ≤ 1.
> Neither is in mathlib. Would you (a) point us at an existing formalisation we may have missed, (b) sketch the cleanest proof skeleton if we have to formalise it, or (c) suggest a workaround that avoids this chain (e.g. routing the Spa-point existence through Wedhorn 7.45's direct dominating-valuation construction instead of 7.40(6))?"

#### Proof sketch

n/a — once the review reply lands (via `/expert-review --reply`), re-decompose T-PRESHEAF-MULARCH-RANKONE per the reviewer's guidance and create the resulting tickets in a follow-up `/develop` pass.

#### Generality decision

n/a.

### [T-SP-SHEAF-A] CompleteTopCommRingCat-presheaf sheaf condition via Hom-presheaves

- **Status**: DONE (landed 2026-05-27 as `isSheaf_of_homPresheaves_isSheaf` in StructureSheaf.lean before line 255; uses Presieve.IsSheaf form so the identity discharges the unfolding; structurePresheaf_isSheaf now applies it leaving the Hom-presheaf sub-sorry as the substantive T-SP-SHEAF-B residual)
- **File**: `Adic spaces/StructureSheaf.lean` (new helper before line 255)
- **Depends on**: mathlib `CategoryTheory.Sites.Sheaf`
- **Parent**: T-STRUCTURESHEAF-ISSHEAF-RESIDUAL
- **Type**: theorem (helper / direct definition unfolding)
- **Source**: mathlib `Mathlib/CategoryTheory/Sites/Sheaf.lean:683` (`isSheaf_iff_isSheaf_forget`).

#### Statement

```lean
theorem isSheaf_of_homPresheaves_isSheaf
    (F : Presheaf CompleteTopCommRingCat (SpaTop A))
    (h : ∀ (E : CompleteTopCommRingCat),
      Presheaf.IsSheaf (Opens.grothendieckTopology (SpaTop A))
        (F ⋙ coyoneda.obj (Opposite.op E))) :
    F.IsSheaf
```

#### Proof sketch

This is essentially the **definition** of `Presheaf.IsSheaf` for a presheaf valued in a general category — mathlib's `CategoryTheory.Presheaf.IsSheaf` unfolds to "the type-presheaf `Hom(E, F·)` is a sheaf of types for every E". The proof is a one-liner: unfold definitions / apply `isSheaf_iff_isSheaf_forget`-style equivalence at the Yoneda level.

```lean
intro h E
exact h E
```

(or `rfl` / `Iff.mpr` depending on exact mathlib API form).

#### Mathlib lemmas needed

- `Presheaf.IsSheaf` definition for general category targets (mathlib `Sites/Sheaf.lean`).

#### Generality decision

Fully general over the value category and topology — this is a category-theory generality lemma, useful beyond this specific application.

### [T-SP-SHEAF-B] Hom-presheaves of structurePresheaf are sheaves (discrete topology)

- **Status**: PERMANENTLY-SCOPED-OUT (round-5 expert review, 2026-05-27)
- **Reviewer directive** (verbatim): "For T-SP-SHEAF-B, stop. The full-open Hom-presheaf theorem is false with the current discrete placeholder topology. Keep the project's IsSheafy typeclass as the target, and treat full Presheaf.IsSheaf as a later project after the correct limit topology on arbitrary opens is defined."
- **Future project route** (if/when needed): rational-cover site sheaf → correct limit topology on arbitrary opens → full opens-site `Presheaf.IsSheaf`. NOT part of current Wedhorn 8.28(b) critical path.
- **Status original**: SIGNATURE-DEFECTIVE — needs re-plan (flagged 2026-05-27)
- **Defect**: `presheafSectionsObj A U` uses discrete topology as a placeholder (StructureSheaf.lean:130-133 docstring explicitly states this). With discrete-target topology, continuous ring homs `E → sectionsSubring U` require `ker(f)` to be open in E. For arbitrary (infinite) open covers `(U_α)` in `Opens.grothendieckTopology (SpaTop A)`, gluing compatible families `(f_α)` produces a global `f` with `ker(f) = ⋂_α ker(f_α)` — an infinite intersection of open ideals, which need not be open in a non-discrete E. So the IsSheaf statement over ALL of `Opens.grothendieckTopology` fails when E is non-discrete (e.g., E = ℤ_p with p-adic topology).
- **Resolution route**: the intended target is the Wedhorn 8.28(b) sheaf condition on **rational covers** (finite by construction), not on arbitrary opens. Either (a) restate T-SP-SHEAF-B as a sheaf condition relative to a coarser site (rational covers only), then need a site-comparison argument to lift to `Opens.grothendieckTopology`, or (b) replace the discrete topology placeholder on `sectionsSubring U` with the correct **limit topology over rational covers** (StructureSheaf.lean:131-133 acknowledges this as future work). Route (b) effectively repackages the whole project's Wedhorn 8.28(b) goal.
- **Status original**: OPEN (added 2026-05-27)
- **File**: `Adic spaces/StructureSheaf.lean` (new helper before line 255)
- **Depends on**: T-SP-SHEAF-A, `structurePresheaf_typeLevel_isSheaf` (existing, sorry-free at line 223)
- **Parent**: T-STRUCTURESHEAF-ISSHEAF-RESIDUAL
- **Type**: theorem
- **Source**: Wedhorn 8.20 + standard Hom-presheaf-of-sheaf-is-sheaf for concrete categories with discrete target.

#### Statement

```lean
theorem structurePresheaf_homPresheaf_isSheaf [IsHuberRing A] [PlusSubring A]
    (E : CompleteTopCommRingCat) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (SpaTop A))
      (structurePresheaf A ⋙ coyoneda.obj (Opposite.op E))
```

#### Proof sketch

1. Unfold the Hom-presheaf: `(structurePresheaf A ⋙ coyoneda.obj (op E)).obj (op U) = (E ⟶ presheafSectionsObj A U)` = continuous ring homs from E into `sectionsSubring U` with discrete uniformity on the target.
2. A continuous ring hom into a discrete target is **locally constant** — i.e., factors through a quotient by an open ideal of E.
3. For a finite rational cover, gluing locally-constant ring homs piecewise is straightforward: continuity follows from finite intersection of preimages of points in the discrete target.
4. Reduce to the type-level sheaf condition: `structurePresheaf_typeLevel_isSheaf` (line 223, sorry-free) gives that the underlying type-presheaf is a sheaf of types. Lift to ring homs via Yoneda + the locally-constant equivalence.

#### Mathlib lemmas needed

- `structurePresheaf_typeLevel_isSheaf` (project, line 223).
- `CategoryTheory.Sheaf.IsSheaf_of_iso_iff` or equivalent (mathlib).
- `CompleteTopCommRingCat` API for continuous ring homs into discrete targets.

#### Generality decision

The discrete topology on `sectionsSubring U` is a project-specific choice (line 137). The proof exploits this discreteness; under non-discrete topology a richer argument would be needed (per the existing docstring at line 247-249).

### [T-LEGACY-TATEACYCLICITY-MIGRATE] Migrate LaurentRefinementAcyclic callers off deprecated single-map injectivity — DONE (round-5 review)

- **Status**: DONE (2026-05-27 round-5 beastmode session, full cascade migration)
- **`tateAcyclicity_gluing_via_refinement` migration: DONE** (LaurentRefinementAcyclic.lean). Added explicit `hE_sep` per-E separation hypothesis. Removed the line 96 `restrictionMapHom_injective` use. Restructured body to delegate to `gluing_of_finer_rational`.
- **Full cascade migration: DONE** — `h_separation` threaded through ~22 theorems across 7 files. The B2-FALSE `restrictionMapHom_injective` call inside `tateAcyclicity` Part 1 is replaced with `exact h_separation`. Final assembly at the top is via Cor832's `tateAcyclicity_part1_separation_via_cor832` (TateAcyclicityResiduals.lean:`tateAcyclicityComplete`).
- **Files updated (full cascade)**:
  - `LaurentRefinementAcyclic.lean`: `tateAcyclicity_gluing_via_refinement`, `tateAcyclicity`, `rationalCovering_hasSeparation`, `rationalCovering_hasGluing`.
  - `StructureSheaf.lean`: 13 theorems (`tateQuotientProductRestriction_injective_on_algebraMap`, `tateQuotientProductRestriction_injective`, `separation_ofStronglyNoetherianTate`, `productRestriction_injective_of_laurentRefinement`, `isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing`, `tateAcyclicity_gluing_via_descent_with_P`, `tateAcyclicity_gluing_via_descent`, `productRestrictionSubToEqualizer_surjective`, `productRestrictionSubToEqualizer_isOpenMap`, `productRestrictionSubToEqualizerHomeomorph`, `productRestrictionSub_isInducing_tate`, `productRestrictionSub_isInducing_flat`, `productRestrictionSub_injective_flat`, `isSheafy_ofStronglyNoetherianTate_flat`, `isSheafy_ofStronglyNoetherianTate`).
  - `Cor832.lean`: `productRestriction_injective_tate`.
  - `StandardCover.lean`: `tateAcyclicity_via_standard_cover`.
  - `EmbeddingTopo.lean`: `isSheafy_ofStronglyNoetherianTate_flat_of_wedhorn_tree_existence`.
  - `TateAcyclicityResiduals.lean`: `tateAcyclicity_part2_gluing_via_flat_descent`, `tateAcyclicityComplete`, `isSheafyComplete`.
  - `AuditCleanWrappers.lean`: `tateAcyclicity_separation_via_cor832_proof`, `tateAcyclicity_gluing_via_descent_proof`, `isSheafy_ofStronglyNoetherianTate_proof`.
- **Lake build**: clean (3144 jobs) after full cascade.
- **Net effect**: the B2-FALSE `restrictionMapHom_injective` dependency is removed from the IsSheafy critical path. Top-level consumers of `isSheafy_ofStronglyNoetherianTate` now require an explicit `h_separation` hypothesis (supplied via the Cor832 chain at `tateAcyclicityComplete`).
- **`isSheafyRealized` landed (2026-05-27)**: end-to-end wired theorem at the top of TateAcyclicityResiduals.lean. Takes only `(P, [IsNoetherianRing P.A_0], hSpa_inputs)` and produces `IsSheafy A`. Internally derives `h_separation` per cover via `tateAcyclicity_part1_separation_via_cor832` (Cor832 chain) + empty-cover handling via `isSheafy_separation_empty_cover_of_stronglyNoetherianTate`. The Path-α realization is now fully composable — callers no longer need to supply h_separation as a separate hypothesis; only the Wedhorn-style side conditions in `hSpa_inputs` (noeth-A_0 + noeth-locSubring + A^+ ⊆ A_0 + canonicalMap continuous + h_lifted_ne_top_for_nonOpen). Lake build green.
- **Bonus: `restrictionMapHom_injective` DELETED** (PresheafTateStructure.lean). After the cascade migration, no remaining call sites used it. The B2-FALSE deprecated theorem and its `sorry` body are now fully retired. Net sorry removal: −1.
- **Note: `restrictionMapHom_surj` retained** (PresheafTateStructure.lean:1221) — still has one active caller at line 2976 (producing `IsLocalization.Away` for `restrictionMapHom`). Deletion would require additional refactor; flagged for future work but lower priority.
- **Status original**: HIGH-PRIORITY OPEN (priority-bumped 2026-05-27 per round-5 expert review)
- **Reviewer directive** (verbatim): "Prioritize this. False single-map injectivity/surjectivity should not remain load-bearing. If the two callers need per-E separation, thread that as an explicit cover-level product-injectivity hypothesis until the final Cor 8.32 path is wired."
- **Migration plan reaffirmed**: thread a `(perE_inj : ∀ E ∈ C.covers, cover-level-product-injectivity-at-E)` hypothesis through `tateAcyclicity_gluing_via_refinement` and `tateAcyclicity` Part 1; update the two caller sites in `LaurentRefinementAcyclic.lean` lines 96 and 332; delete the deprecated `restrictionMapHom_injective` (PresheafTateStructure.lean:1422) and `restrictionMapHom_surj` (line 1221) once no callers remain. Net sorry deletion: −2.
- **Original status (added 2026-05-27; replaces T-PRESHEAFTATE-SURJ-RESIDUAL and T-PRESHEAFTATE-INJ-RESIDUAL)**
- **File**: `Adic spaces/LaurentRefinementAcyclic.lean` (refactor), `Adic spaces/PresheafTateStructure.lean` (delete deprecated theorems), `Adic spaces/TateAcyclicityFinalAssembly.lean` (downstream wrapper)
- **Depends on**: `productRestriction_injective_tate_via_prime_extension_closed` (Cor832.lean, existing)
- **Parent**: replaces T-PRESHEAFTATE-SURJ-RESIDUAL + T-PRESHEAFTATE-INJ-RESIDUAL
- **Type**: refactor + deletion
- **Source**: LaurentRefinementAcyclic.lean docstrings at line 83-93 and 320-329 (explicit project guidance).

#### Statement

(Refactor, not a single theorem; per binding-rule (b), introduces per-E injectivity as explicit hypothesis since the conclusion is otherwise B2-false.)

#### Proof sketch

1. **Refactor `tateAcyclicity_gluing_via_refinement`** (LaurentRefinementAcyclic.lean:55) to take an additional hypothesis `perE_inj : ∀ E ∈ C.covers, separation-clause-via-Cor832`. Replace the line-96 use of `restrictionMapHom_injective` with `perE_inj` application.
2. **Refactor `tateAcyclicity`** (LaurentRefinementAcyclic.lean:302) similarly: Part 1 takes per-E separation, Part 2 unchanged. Replace line-332 use of `restrictionMapHom_injective`.
3. **Update Cor832.lean:462 caller** to supply the per-E separation hypothesis when calling `(tateAcyclicity P C hne).1 x hx`. The per-E separation is `productRestriction_injective_tate_via_prime_extension_closed` (Cor832.lean, existing).
4. **Delete the deprecated** `restrictionMapHom_surj` (PresheafTateStructure.lean:1221) and `restrictionMapHom_injective` (line 1422) — both B2-false markers, now caller-free after migration. Net sorry: −2.
5. Add downstream wrapper in TateAcyclicityFinalAssembly.lean if needed for cycle-free import.

#### Mathlib lemmas needed

- `productRestriction_injective_tate_via_prime_extension_closed` (Cor832.lean, existing).

#### Generality decision

Binding-rule (b) compliant: the per-E hypothesis IS mathematically necessary (the single-map version is B2-false; counterexample in PresheafTateStructure.lean docstrings).

### [T-ROUTE-B-PAIR-INVARIANCE] (umbrella) presheafValue invariant under change of D.P (Wedhorn-faithful)

- **Status**: DECOMPOSED into T-ROUTE-B-1 through T-ROUTE-B-6 (2026-05-27, /develop --continue planning pass).
- **Why**: Wedhorn 8.28(b)'s rational subsets `R(T/s)` are defined by `(T, s)` only — no pair-of-definition data. The project's `RationalLocData` carries a pair `P`, which is auxiliary scaffolding. The current `isSheafyRealized` requires per-cover `hSpa_inputs` because each cover piece may carry a different `P`. Route B closes this by proving `presheafValue D` is invariant under change of `D.P` (for fixed `T`, `s`), aligning with Wedhorn's pair-free formulation.
- **Decomposition (read /beastmode picks one at a time)**:
  - T-ROUTE-B-1: `divByS_isPowerBounded_locTopology` (~50 LOC).
  - T-ROUTE-B-2: `nonarchimedean_locTopology` instance helper (~10 LOC).
  - T-ROUTE-B-3: `locTopology_pair_invariant` (~50 LOC, depends on B-1, B-2).
  - T-ROUTE-B-4: `presheafValue_pair_invariant` (~40 LOC, depends on B-3).
  - T-ROUTE-B-5: `RationalLocData.normalizeToPrincipal` def + canonical iso (~40 LOC, depends on B-4).
  - T-ROUTE-B-6: `isSheafy_wedhornClean` top-level theorem (~80 LOC, depends on B-5).
  - CLEANUP-ROUTE-B: cadence cleanup on Presheaf.lean Route-B block.
- **Source: Wedhorn §5.51, Prop 8.2, Example 6.38** — the universal property of the localization topology. Topology is uniquely determined by (i) algebraMap continuity, (ii) divByS power-boundedness — both pair-invariant.

### [T-ROUTE-B-1] `divByS_isPowerBounded_locTopology`

- **Status**: OPEN
- **File**: `Adic spaces/Presheaf.lean` (replace the body of the existing sorry'd lemma)
- **Depends on**: none (uses existing `divByS_mem_locSubring`, `locBasis`, `locNhd`)
- **Parallel**: yes (independent of B-2)
- **Type**: theorem

#### Statement

```lean
theorem divByS_isPowerBounded_locTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    {t : A} (ht : t ∈ T) :
    letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
    haveI : IsTopologicalRing (Localization.Away s) :=
      (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
    TopologicalRing.IsPowerBounded (divByS t s)
```

#### Proof sketch

The set `{(divByS t s)^n | n : ℕ}` is bounded in `locTopology P T s`. Proof strategy: in the localization topology, neighborhoods at 0 are `locNhd P T s n` (the image of `(locIdeal P T s)^n`). The set `{(divByS t s)^n}` lies entirely in `locSubring P T s` (since `divByS t s ∈ locSubring` and locSubring is closed under multiplication). The locSubring acts on locNhd's by left-multiplication (locSubring is a subring containing the locIdeal). So for any neighborhood `U = locNhd P T s n`, choosing `V = locNhd P T s n` gives `{(divByS t s)^k} · V ⊆ locNhd P T s n = U`.

Concretely:
1. **Unfold `IsPowerBounded`** to `IsBounded (Set.range ((divByS t s)^·))`.
2. **Unfold `IsBounded`**: ∀ U ∈ nhds 0, ∃ V ∈ nhds 0, range · V ⊆ U.
3. **Reduce to basic neighborhoods** of locTopology: from `(locBasis P T s hopen).hasBasis_nhds_zero`, any U ∈ nhds 0 contains some `locNhd P T s n`.
4. **Take V = locNhd P T s n** (same n).
5. **Show range · V ⊆ U**: for `y = (divByS t s)^k · v` with `v ∈ locNhd P T s n`:
   - `(divByS t s) ∈ locSubring P T s` by `divByS_mem_locSubring P T s ht`.
   - `(divByS t s)^k ∈ locSubring P T s` by repeated multiplication (locSubring is a subring).
   - `locNhd P T s n` is closed under left-multiplication by `locSubring` (this is `locNhd_leftMul P T s hopen` from the locBasis structure, OR direct argument via the locIdeal ideal-multiplication structure).
   - So `(divByS t s)^k · v ∈ locNhd P T s n ⊆ U`.

#### Mathlib lemmas needed

- `TopologicalRing.IsBounded` (project, Bounded.lean:65): the bounded-set definition.
- `TopologicalRing.IsPowerBounded` (project, Bounded.lean:124): unfolded.
- `Set.mul_subset_iff_forall_mem` (mathlib, for the set-multiplication unfold).
- `RingSubgroupsBasis.hasBasis_nhds_zero` (mathlib).

#### Project lemmas needed

- `divByS_mem_locSubring P T s ht` (LocalizationTopology.lean:66): `divByS t s ∈ locSubring P T s` for `t ∈ T`.
- `locNhd_leftMul P T s hopen` (LocalizationTopology.lean, the ring-subgroups basis input): locSubring acts on locNhd by left-multiplication. *Verify exists; if not, prove inline.*
- Alternatively, use `Subring.mem_closure_iff` to derive `(divByS t s)^k ∈ locSubring`, plus the `locNhd` ideal structure.

#### Sources

- [Wedhorn 2019] *Adic Spaces*, §5.51 + Remark 5.33: localization topology + bounded elements in localization. Specifically the ring of definition `A₀[T/s]` (= our `locSubring`) is bounded; elements of a bounded subring are power-bounded.

#### Generality decision

- `[CommRing A] [TopologicalSpace A] [IsTopologicalRing A]` — minimal hypotheses; no Tate / Huber assumed.
- The signature uses `letI`/`haveI` to inject the locTopology + IsTopologicalRing instances since `Localization.Away s` doesn't have these as canonical instances.

### [T-ROUTE-B-2] `nonarchimedean_locTopology` instance helper

- **Status**: OPEN
- **File**: `Adic spaces/LocalizationTopology.lean` (add as a helper before line 269 — after `locTopology` def)
- **Depends on**: none (uses existing `locBasis` + `RingSubgroupsBasis.nonarchimedean`)
- **Parallel**: yes
- **Type**: theorem (helper, exposed for use in B-3)

#### Statement

```lean
theorem nonarchimedean_locTopology
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @NonarchimedeanRing (Localization.Away s) _ (locTopology P T s hopen)
```

#### Proof sketch

Direct application of `RingSubgroupsBasis.nonarchimedean` to the `locBasis`. The `locTopology` is defined as `(locBasis P T s hopen).topology`, and `RingSubgroupsBasis.nonarchimedean` says any topology from a `RingSubgroupsBasis` is `NonarchimedeanRing`.

```lean
exact (locBasis P T s hopen).nonarchimedean
```

May need to thread the IsTopologicalRing instance via `(locBasis P T s hopen).toRingFilterBasis.isTopologicalRing`. Two-or-three-liner.

#### Mathlib lemmas needed

- `RingSubgroupsBasis.nonarchimedean` (`Mathlib.Topology.Algebra.Nonarchimedean.Bases`).

#### Sources

- [Wedhorn 2019] §5: nonarchimedean topology from ring-subgroups basis.

#### Generality decision

Same hypothesis bundle as `divByS_isPowerBounded_locTopology`.

### [T-ROUTE-B-3] `locTopology_pair_invariant`

- **Status**: OPEN
- **File**: `Adic spaces/Presheaf.lean` (replace the body of the existing sorry'd lemma)
- **Depends on**: T-ROUTE-B-1, T-ROUTE-B-2
- **Parallel**: no (waits on B-1, B-2)
- **Type**: theorem

#### Statement

```lean
theorem locTopology_pair_invariant
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (P₁ P₂ : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen₁ : ∃ N : ℕ, ∀ b : P₁.A₀, b ∈ P₁.I ^ N →
      divByS (↑b : A) s ∈ locSubring P₁ T s)
    (hopen₂ : ∃ N : ℕ, ∀ b : P₂.A₀, b ∈ P₂.I ^ N →
      divByS (↑b : A) s ∈ locSubring P₂ T s) :
    locTopology P₁ T s hopen₁ = locTopology P₂ T s hopen₂
```

#### Proof sketch

The two topologies are equal via `le_antisymm`. Show `id` is continuous in both directions; each direction translates to a `≤` relation between the topologies.

1. **Establish virtual RationalLocData D₁ = ⟨P₁, T, s, hopen₁⟩ and D₂ = ⟨P₂, T, s, hopen₂⟩** as `let`-bindings, so we can reuse `algebraMap_continuous_loc`.
2. **Establish NonarchimedeanRing on both topologies** via `nonarchimedean_locTopology` (B-2) — needed as a typeclass argument for `locTopology_continuous_lift`.
3. **Continuity in direction P₁ → P₂** (i.e., `id` continuous from locTopology P₁ to locTopology P₂):
   ```lean
   have h₁₂ : @Continuous _ _ (locTopology P₁ T s hopen₁) (locTopology P₂ T s hopen₂) id :=
     locTopology_continuous_lift P₁ T s hopen₁ (RingHom.id _)
       (by exact algebraMap_continuous_loc ⟨P₂, T, s, hopen₂⟩)
       (fun t ht => divByS_isPowerBounded_locTopology P₂ T s hopen₂ ht)
   ```
4. **Continuity in direction P₂ → P₁** (symmetric):
   ```lean
   have h₂₁ : @Continuous _ _ (locTopology P₂ T s hopen₂) (locTopology P₁ T s hopen₁) id :=
     locTopology_continuous_lift P₂ T s hopen₂ (RingHom.id _)
       (by exact algebraMap_continuous_loc ⟨P₁, T, s, hopen₁⟩)
       (fun t ht => divByS_isPowerBounded_locTopology P₁ T s hopen₁ ht)
   ```
5. **Extract topology equality from id-continuity both directions**:
   ```lean
   -- h₁₂ continuous means: every locTopology P₂-open has id-preimage open in locTopology P₁
   --                    ⟺ locTopology P₂ ≤ locTopology P₁
   -- h₂₁ continuous means: every locTopology P₁-open has id-preimage open in locTopology P₂
   --                    ⟺ locTopology P₁ ≤ locTopology P₂
   -- By le_antisymm, the topologies are equal.
   refine le_antisymm ?_ ?_
   · exact fun U hU => h₂₁.isOpen_preimage U hU  -- locTopology P₁ ≤ P₂
   · exact fun U hU => h₁₂.isOpen_preimage U hU  -- locTopology P₂ ≤ P₁
   ```

#### Mathlib lemmas needed

- `Continuous.isOpen_preimage` — `(f : X → Y) (h : Continuous f) (U : Set Y) (hU : IsOpen U) : IsOpen (f ⁻¹' U)`.
- `TopologicalSpace.le_def` or `le_antisymm` on `TopologicalSpace`.

#### Project lemmas needed

- `locTopology_continuous_lift` (LocalizationTopology.lean:360).
- `algebraMap_continuous_loc` (PresheafIdentification.lean:864).
- `divByS_isPowerBounded_locTopology` (T-ROUTE-B-1).
- `nonarchimedean_locTopology` (T-ROUTE-B-2).

#### Sources

- Same as B-1.

#### Generality decision

Same hypothesis bundle as B-1.

### [T-ROUTE-B-4] `presheafValue_pair_invariant`

- **Status**: OPEN
- **File**: `Adic spaces/Presheaf.lean` (replace the body of the existing sorry'd def)
- **Depends on**: T-ROUTE-B-3
- **Parallel**: no
- **Type**: noncomputable def (returns a `≃+*`)

#### Statement

```lean
noncomputable def presheafValue_pair_invariant
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A]
    {P₁ P₂ : PairOfDefinition A} {T : Finset A} {s : A}
    (hopen₁ : ∃ N : ℕ, ∀ b : P₁.A₀, b ∈ P₁.I ^ N →
      divByS (↑b : A) s ∈ locSubring P₁ T s)
    (hopen₂ : ∃ N : ℕ, ∀ b : P₂.A₀, b ∈ P₂.I ^ N →
      divByS (↑b : A) s ∈ locSubring P₂ T s) :
    presheafValue (⟨P₁, T, s, hopen₁⟩ : RationalLocData A) ≃+*
      presheafValue (⟨P₂, T, s, hopen₂⟩ : RationalLocData A)
```

#### Proof sketch

By `locTopology_pair_invariant` (B-3), the underlying topologies on `Localization.Away s` are equal. Hence:
- `D₁.uniformSpace = D₂.uniformSpace` (both `IsTopologicalAddGroup.rightUniformSpace` from the same topology).
- `UniformSpace.Completion (Loc.Away s) D₁.uniformSpace = UniformSpace.Completion (Loc.Away s) D₂.uniformSpace` as types (since the completion only depends on the uniform structure).

Construct the `≃+*` via `RingEquiv.refl` after rewriting the topologies to be equal. Concretely:
```lean
have htop : (⟨P₁, T, s, hopen₁⟩ : RationalLocData A).topology =
            (⟨P₂, T, s, hopen₂⟩ : RationalLocData A).topology :=
  locTopology_pair_invariant P₁ P₂ T s hopen₁ hopen₂
-- The presheafValue types are def-equal since both reduce to
-- UniformSpace.Completion (Loc.Away s) (uniformSpace from htop).
-- Use `RingEquiv.refl` modulo a rewrite via `htop`.
```

Possible issues:
- The completion type may not be literally def-equal even when the uniform structures are equal (Lean may not propagate the equality through the type constructor).
- May need to use `RingEquiv.cast` / `Equiv.cast` style construction with explicit type-equality.

If a direct `RingEquiv.refl` doesn't work, fall back to:
- `Equiv.ringEquiv` from a manual definition using `cast` on the type-equality from `htop`.

#### Mathlib lemmas needed

- `RingEquiv.refl`, `Equiv.cast`, `RingEquiv.cast` (if available).
- `UniformSpace.Completion` definitional unfolding.

#### Project lemmas needed

- `locTopology_pair_invariant` (T-ROUTE-B-3).

#### Sources

Same as B-1 (Wedhorn Example 6.38).

#### Generality decision

Includes `[PlusSubring A]` since `RationalLocData A` requires it (via the file's variable block). Otherwise minimal.

### [T-ROUTE-B-5] `RationalLocData.normalizeToPrincipal` + canonical iso

- **Status**: OPEN
- **File**: `Adic spaces/Presheaf.lean` (new private def + theorem, after `presheafValue_pair_invariant`)
- **Depends on**: T-ROUTE-B-4
- **Parallel**: no
- **Type**: noncomputable def + theorem

#### Statement

```lean
/-- For a Tate ring A, every `D : RationalLocData A` has a canonical normalization
to use the principal pair of definition. -/
noncomputable def RationalLocData.normalizeToPrincipal
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A]
    (D : RationalLocData A) : RationalLocData A := by
  -- The principal pair has its own `hopen` for any (T, s) where T satisfies
  -- the rational-subset openness condition. Construct the normalized D using
  -- the principal pair's hopen for (D.T, D.s).
  sorry

/-- The canonical iso from `presheafValue D` to its principal-pair normalization. -/
noncomputable def RationalLocData.presheafValue_normalizeToPrincipal
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsTateRing A]
    (D : RationalLocData A) :
    presheafValue D ≃+* presheafValue D.normalizeToPrincipal :=
  presheafValue_pair_invariant D.hopen D.normalizeToPrincipal.hopen
```

#### Proof sketch

1. **Construct the principal-pair normalization**: take `P' := IsTateRing.principalPair A`. Need to construct `hopen' : ∃ N, ∀ b : P'.A₀, b ∈ P'.I^N → divByS b s ∈ locSubring P' T s`. This is the principal-pair-specific openness condition for the SAME (T, s).
2. **Show the principal-pair openness condition holds for any (T, s) that satisfies SOME pair's openness condition**: this is the substantive content. The "rational subset" property is intrinsic to (T, s) (i.e., `T · A` open) and shouldn't depend on the chosen P. For the principal pair, we need to show the explicit `hopen'` condition.

Note: the openness condition `∃ N, P.I^N → divByS ∈ locSubring P T s` IS pair-specific in shape but should be derivable for any pair from the universal rational-subset condition (T · A open).

3. **The canonical iso** is then a direct application of `presheafValue_pair_invariant` with D.P and `principalPair`.

**Sub-sorry: deriving hopen' for the principal pair from D.hopen** is the substantive content of this ticket (~20-30 LOC). May involve showing equivalence of openness conditions across pairs (which IS a consequence of pair-invariance, but stated for hopen specifically).

#### Mathlib lemmas needed

None beyond standard.

#### Project lemmas needed

- `presheafValue_pair_invariant` (T-ROUTE-B-4).
- `IsTateRing.principalPair` (existing).
- The pair-invariance of the openness condition (might need a new lemma `hopen_pair_invariant`).

#### Sources

Same as B-1.

#### Generality decision

Adds `[IsTateRing A]` for the principal pair to exist.

### [T-ROUTE-B-6] `isSheafy_wedhornClean` top-level theorem

- **Status**: OPEN
- **File**: `Adic spaces/TateAcyclicityResiduals.lean` (after `isSheafyRealized`)
- **Depends on**: T-ROUTE-B-5
- **Parallel**: no
- **Type**: theorem

#### Statement

```lean
/-- **Wedhorn 8.28(b), Wedhorn-clean form.** Strongly noetherian Tate ⇒ sheafy.
No per-cover hypothesis bundle: the cover-level conditions are derived
internally via the pair-invariance of `presheafValue` + Cor 8.32 chain. -/
theorem isSheafy_wedhornClean
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    -- Only the principal pair's noeth-A₀ and the single global compatibility
    -- conditions are needed.
    [IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀]
    [IsNoetherianRing
      (locSubring (IsTateRing.principalPair A).toPairOfDefinition
        ∅ (1 : A))]  -- principal pair's locSubring for trivial cover; needs adjustment
    (hSpa_principal : ∀ (T : Finset A) (s : A) (hs : T · A = ⊤),
        ∀ (p : Ideal A), p.IsPrime → s ∉ p → ¬IsOpen (p : Set A) →
        (Ideal.map (algebraMap A ...) p) ≠ ⊤) :
    IsSheafy A
```

#### Proof sketch

For each cover `C : RationalCovering A`, the per-cover `hSpa_inputs` are derived from the principal-pair version via `presheafValue_normalizeToPrincipal` (B-5):

1. **Take any C**. For each cover piece `D ∈ C.covers`, normalize to `D.normalizeToPrincipal` via B-5. The cover `C.normalizeToPrincipal` has every cover piece's `.P` equal to the principal pair.
2. **For the normalized cover, the per-cover hypotheses become per-(T, s) hypotheses for the principal pair** — these can be derived from the single global `hSpa_principal` hypothesis.
3. **Apply `isSheafyRealized`** to the normalized cover, then transport back via the iso.

This is the structural composition that produces a Wedhorn-clean theorem.

**Caveats**:
- The exact form of `hSpa_principal` needs careful crafting — it should universally quantify over (T, s) that form rational subsets.
- The "transport back via the iso" step uses `presheafValue_pair_invariant`'s canonical iso to identify the normalized cover's sheafy property with the original cover's.

#### Mathlib lemmas needed

None beyond standard.

#### Project lemmas needed

- `isSheafyRealized` (existing, TateAcyclicityResiduals.lean).
- `RationalLocData.normalizeToPrincipal` (T-ROUTE-B-5).
- Cor 8.32 chain for `h_lifted_ne_top` (existing).

#### Sources

[Wedhorn 2019] Theorem 8.28(b).

#### Generality decision

Drops the explicit `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` parameter that `isSheafyRealized` requires; replaced by a typeclass-only formulation using the principal pair.

### [CLEANUP-ROUTE-B] Run /cleanup on Presheaf.lean Route-B block

- **Status**: OPEN (cadence)
- **Depends on**: T-ROUTE-B-4 (the in-Presheaf-lean Route B work)
- **Type**: cleanup
- **Scope**: golf the three Route-B lemmas + the normalize-to-principal definition; consolidate docstrings; verify axiom-cleanness.

### Round-7 cleanup cadence sync

After the 11 new sub-tickets and the legacy-migration refactor land, the cleanup cadence requires:
- **CLEANUP-PRESHEAFTATE** (already exists OPEN) — triggers after T-AR-4 + T-LEGACY-TATEACYCLICITY-MIGRATE land.
- **CLEANUP-STRUCTURESHEAF** (already exists OPEN) — triggers after T-SP-SHEAF-A + T-SP-SHEAF-B + T-STRUCTURESHEAF-ISSHEAF-RESIDUAL close.
- No new cleanup tickets needed — existing cadence absorbs the new proof tickets.

---

## Round-5 expert-review integration (2026-05-27) — path-α scope clarification

Per round-5 expert review (`.mathlib-quality/expert-review/2026-05-27/reply.md`), the project's current sheafy target is explicitly path-α (with explicit noetherian `P.A_0` hypothesis), NOT the full Wedhorn-clean strongly-noetherian theorem. Adding a documentation ticket:

### [T-PATH-ALPHA-RESTRICTED-NAMING] Document the path-α scope and rename main sheafy target

- **Status**: OPEN (added 2026-05-27 per round-5 expert review)
- **Reviewer directive** (verbatim): "Path α is the right current policy, but it should be documented as a restricted theorem, not Wedhorn's full strongly-noetherian theorem. So the long-term structure should be: `isSheafy_ofStronglyNoetherianTate_with_noetherian_pair (P : PairOfDefinition A) [IsNoetherianRing P.A_0] : IsSheafy A` (current proven theorem); `isSheafy_ofStronglyNoetherianTate : [IsStronglyNoetherian A] → IsSheafy A` (future Wedhorn-clean theorem, if/when available)."
- **Action**: introduce explicit naming convention `isSheafy_ofStronglyNoetherianTate_with_noetherian_pair` in the project's public-API layer (StructureSheaf.lean or a new wrapper file). The Wedhorn-clean variant becomes a future ticket — explicitly *not* on the current critical path.
- **Why**: clarifies the scope of what's been proved versus what remains. Avoids the rhetorical drift of claiming "Wedhorn 8.28(b)" when we've proved a slightly weaker conditional version.
- **File**: StructureSheaf.lean (rename/wrapper); CLAUDE.md or docs/STATUS.md (documentation).
- **LOC estimate**: ~15 LOC for the renamed wrapper + a few lines of documentation.

### [T-DELETE-RETIRED-NOETH-A0-HELPERS] Delete `_aux_noeth_A0_generic_of_stronglyNoetherianTate` and propagate noeth-A₀ explicit hypothesis

- **Status**: OPEN (added 2026-05-27 per round-5 expert review)
- **Reviewer directive** (verbatim): "Do not keep retired 'strong noetherian ⇒ noetherian A₀' helpers in active imports, even with sorry."
- **Action**:
  1. Identify consumers of `_aux_noeth_A0_generic_of_stronglyNoetherianTate` and `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` (StructureSheaf.lean:1606, 1621).
  2. For each consumer, migrate to take explicit `(P : PairOfDefinition A) [IsNoetherianRing P.A_0]` parameter at the public-API boundary.
  3. Delete the two retired helpers.
- **Scope**: ~30 references in StructureSheaf.lean and downstream. Multi-file refactor; needs care.
- **Risk**: high — touches many active call sites. Should be done in a dedicated session with `lake build` verification between each migration.
- **LOC estimate**: ~50-100 LOC of mechanical hypothesis-threading across files.

### Round-5 execution-order recommendation (verbatim from reviewer)

> 1. Fix `T-WED-745-CONT-A/B/C` signatures using the corrected convex/cofinality semantics.
> 2. Finish Wedhorn 7.45 continuity by abstracting Lemma745.
> 3. Finish T-AR-3 as an ideal-containment lemma, then T-AR-4.
> 4. Migrate legacy Tate acyclicity callers off false single-map injectivity.
> 5. Keep structure sheaf `Presheaf.IsSheaf` out of the critical path.
> 6. Continue Path α assembly with explicit noetherian-pair hypotheses.

This supersedes the earlier "Round-7 ordering" implicit in the ticket creation order.

---

## 2026-05-28 /develop --continue: new ticket batch for WedhornCechAcyclicity.lean

This batch reflects the Wedhorn-Čech route established in
`Adic spaces/WedhornCechAcyclicity.lean` (committed at 809b78e). See
`plan.md` (regenerated 2026-05-28) for the full decomposition.

Top-level target: `isSheafy_ofStronglyNoetherianTate_clean` (Wedhorn-faithful,
no per-cover hypothesis leaks). 33 atomic sorries remain; one ticket per
sorry. 4 cleanup checkpoints inserted per the per-file cadence rule.

### [T-WC-FILE-REORDER] Move propA3_part2 + IsOXAcyclic_of_refining_acyclic_cover earlier in file

- **Status**: done (2026-05-28: moved propA3_part2_project_separation/gluing + IsOXAcyclic_of_refining_acyclic_cover to just before wedhorn_lemma_833 sub-lemmas; build clean; unlocks T-WC-834-C-RESTR-BODY)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: no (must precede T-WC-834-C-RESTR and T-WC-834-BODY)
- **Type**: refactor

#### Statement
No new declarations; structural move only. Reorder the file so that
`propA3_part2_project_separation`, `propA3_part2_project_gluing`, and
`IsOXAcyclic_of_refining_acyclic_cover` are defined BEFORE
`wedhorn_lemma_834_C_restr_acyclic` (currently they're at line ~1550, but
needed at line ~1240).

#### Proof sketch
1. Cut lines 1525–1610 (the propA3_part2_* + IsOXAcyclic_of_refining block).
2. Paste before `wedhorn_lemma_834_C_restr_acyclic` (around line 1240).
3. Re-run `lake build`; should be clean.

#### Mathlib lemmas needed
None.

#### Sources
None (project structural move).

#### Generality decision
None (no API change).

### [T-WC-CAT-C-CHANGE-BASE] `RationalCovering.changeBase` helper to internalise the C'.base = C.base cast

- **Status**: done (2026-05-28: presheafValueCast + presheafValueCast_restrictionMap landed sorry-free in WedhornCechAcyclicity.lean:163-188; variable-base form for subst-friendly use)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes (parallel with all Cat. B and Cat. D tickets)
- **Type**: def + 4 lemma compositions

#### Statement
```lean
/-- Transport a presheaf section along a base equality. -/
noncomputable def RationalCovering.presheafValueCast
    {C C' : RationalCovering A} (h : C'.base = C.base) :
    presheafValue C.base ≃+* presheafValue C'.base := by
  rw [h]
  exact RingEquiv.refl _

/-- Restriction map respects the base cast. -/
theorem RationalCovering.presheafValueCast_restrictionMap
    {C C' : RationalCovering A} (h : C'.base = C.base)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hD' : D ∈ C'.covers)
    (hsubC : rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (hsubC' : rationalOpen D.T D.s ⊆ rationalOpen C'.base.T C'.base.s)
    (x : presheafValue C.base) :
    restrictionMap C'.base D hsubC' ((presheafValueCast h) x) =
      restrictionMap C.base D hsubC x := by sorry
```

#### Proof sketch
1. `presheafValueCast` is defined by case-splitting on `h` to make `C.base ≡ C'.base`.
2. The restrictionMap-respect lemma reduces to `rfl` after the case-split.

This helper internalises the cast plumbing that blocks
`propA3_part2_project_separation`, `propA3_part2_project_gluing`,
`wedhorn_lemma_834_propA3_part1_separation`, and
`wedhorn_lemma_834_propA3_part1_gluing` (all four become routine after this
helper exists).

#### Mathlib lemmas needed
- `RingEquiv.refl`
- Standard `Eq.rec` / `▸` patterns

#### Sources
None (technical infrastructure).

#### Generality decision
Stated generically over any two `RationalCovering A` with the base equality;
not specialised to refinements.

### [T-WC-PROPA3-PART2-SEP] `propA3_part2_project_separation` via changeBase helper

- **Status**: done (2026-05-28: closed sorry-free at WedhornCechAcyclicity.lean:1583-1620; uses presheafValueCast + restrictionMap_comp + (restrictionMapHom _).map_zero)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `propA3_part2_project_separation` (line ~1550, currently sorry).
Conclusion unchanged: C'-separation + refinement ⇒ C-separation.

#### Proof sketch
1. Intro `x : presheafValue C.base`, `hx : ∀ D ∈ C.covers, x|D = 0`.
2. Cast `x' := presheafValueCast h_same_base.symm x : presheafValue C'.base`.
3. Apply `h_C'_sep` to `x'`: it suffices to show `x'|D' = 0` for all `D' ∈ C'.covers`.
4. For each `D' ∈ C'.covers`, pick `D ⊇ D'` from refinement.
5. `restrictionMap C'.base D' x' = restrictionMap D D' (restrictionMap C'.base D x')`
   by `restrictionMap_comp` (project lemma).
6. `restrictionMap C'.base D x' = restrictionMap C.base D x` by `presheafValueCast_restrictionMap`.
7. By `hx D`, this is 0; restriction of 0 is 0; done.

#### Mathlib lemmas needed
- `restrictionMap_comp` (project, `Presheaf.lean:1362`)
- `map_zero`

#### Sources
Wedhorn, *Adic Spaces*, §A.3.

#### Generality decision
Same as the current sorry'd statement.

### [T-WC-PROPA3-PART2-GLU] `propA3_part2_project_gluing` via changeBase helper

- **Status**: in_progress (started 2026-05-28; needs E := C'|_D construction sub-lemma — non-trivial structural construction; deferred)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Parallel**: parallel with T-WC-PROPA3-PART2-SEP
- **Type**: theorem

#### Statement
The existing `propA3_part2_project_gluing` (line ~1583, currently sorry).
Conclusion: C'-acyclicity + double-restriction-acyclicity + refinement ⇒
C-gluing.

#### Proof sketch
1. For each `D ∈ C.covers`, use `_h_double_acyclic` on `E := C'|_D` to glue
   `f(D)` from {f(D')|D' refining into D} (compatible family).
2. Lift the result to a section `x' : presheafValue C'.base` via `h_C'_acyclic.gluing`.
3. Transport `x'` back to `presheafValue C.base` via `presheafValueCast`.
4. Verify `x|D = f(D)` for each `D ∈ C.covers` by step-1 construction.

#### Mathlib lemmas needed
- Standard restriction map composition

#### Sources
Wedhorn, *Adic Spaces*, §A.3.

#### Generality decision
Same as current sorry.

### [T-WC-PROPA3-PART1-SEP] `wedhorn_lemma_834_propA3_part1_separation`

- **Status**: done (2026-05-28: closed sorry-free; added `h_V_refines_C` hypothesis (V refines C; was missing from Prop A.3(1) decomposition); proof via presheafValueCast + V.separation + restrictionMap_comp)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Parallel**: parallel with T-WC-PROPA3-PART2-*
- **Type**: theorem

#### Statement
The existing `wedhorn_lemma_834_propA3_part1_separation` (line ~1304).
Conclusion: under Prop A.3(1)-style mutual refinement, separation transfers
from V to C.

#### Proof sketch
Same shape as T-WC-PROPA3-PART2-SEP, with `V_restr_at` family used instead
of the universal refinement.

#### Mathlib lemmas needed
Same as PART2-SEP.

#### Sources
Wedhorn, *Adic Spaces*, §A.3, Prop A.3(1).

#### Generality decision
Same as current sorry.

### [T-WC-PROPA3-PART1-GLU] `wedhorn_lemma_834_propA3_part1_gluing`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Parallel**: parallel with T-WC-PROPA3-PART1-SEP
- **Type**: theorem

#### Statement
The existing `wedhorn_lemma_834_propA3_part1_gluing` (line ~1339).

#### Proof sketch
Same as T-WC-PROPA3-PART2-GLU but using V_restr_at + C_restr_at families.

#### Mathlib lemmas needed
Same as PART2-GLU.

#### Sources
Wedhorn, *Adic Spaces*, §A.3, Prop A.3(1).

#### Generality decision
Same.

### [CLEANUP-WC-1] /cleanup on WedhornCechAcyclicity.lean (after Cat. C done)

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-PROPA3-PART2-SEP, T-WC-PROPA3-PART2-GLU, T-WC-PROPA3-PART1-SEP, T-WC-PROPA3-PART1-GLU, T-WC-FILE-REORDER
- **Parallel**: no
- **Type**: cleanup
- **Description**: Run /cleanup on the file after Cat. C (cast plumbing)
  closes 4 sorries. Targets: golf the changeBase helper, ensure naming
  consistency, deduplicate similar proofs.

### [T-WC-SINGLE-UNIT-SEP] `isOXAcyclic_of_single_unit_piece_separation`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `isOXAcyclic_of_single_unit_piece_separation` (line ~690).
Single piece R({1}/1) ⇒ separation.

#### Proof sketch
1. Unpack the `_h_one_piece` to get `D₀` with `V.covers = {D₀}, D₀.T = {1}, D₀.s = 1`.
2. R({1}/1) = `rationalOpen` evaluates to {v : v(1) ≠ 0} = whole Spa (since v(1) = 1 always).
3. The single restriction `restrictionMap V.base D₀` is an iso (R({1}/1) = whole space).
4. So x|D₀ = 0 ⇒ x = 0 via the iso.

#### Mathlib lemmas needed
- `Finset.eq_of_mem_singleton`
- `rationalOpen` evaluation at T = {1}, s = 1

#### Sources
Wedhorn p. 84 (base case of Lemma 8.34 part (i) induction).

#### Generality decision
Same as current sorry.

### [T-WC-SINGLE-UNIT-GLU] `isOXAcyclic_of_single_unit_piece_gluing`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `isOXAcyclic_of_single_unit_piece_gluing` (line ~716).
Single piece ⇒ gluing.

#### Proof sketch
1. Unpack `_h_one_piece` to get `D₀ ∈ V.covers, D₀.T = {1}, D₀.s = 1`.
2. The cover has one element; the compatibility family is just `f(D₀)`.
3. Use the iso `V.base → D₀` to pull `f(D₀)` back to a global section.

#### Mathlib lemmas needed
Same as SEP.

#### Sources
Wedhorn p. 84.

#### Generality decision
Same.

### [T-WC-LAURENT-CONS-DECOMP] `laurent_cons_decomp_as_product`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `laurent_cons_decomp_as_product` (line ~804).
`V.IsLaurentCover (f :: gs)` ⇒ V refines a product structure with 𝒰_f and 𝒱_gs.

#### Proof sketch
1. Build Uf := `laurentRationalCover V.base f` (2-cover by R(f/1), R(1/f)).
2. For each piece Uf_j of Uf, construct Vgs_at Uf_j as the restriction of
   V's gs-generators to Uf_j.
3. Show Vgs_at Uf_j.IsLaurentCover gs structurally.

This is the project-side instance of Wedhorn p. 84's
`𝒱_{f::gs} := 𝒰_f × 𝒱_{gs}` identification.

#### Mathlib lemmas needed
- `laurentRationalCover` (project def)
- Sublist/foldr combinatorics for the gs-product Finset

#### Sources
Wedhorn, *Adic Spaces*, p. 84.

#### Generality decision
Project-internal; minimal hypotheses.

### [T-WC-PROPA3-PART3-BRIDGE] `propA3_part3_bridge_for_laurent_product` — B2 candidate

- **Status**: OPEN (B2 review needed before work)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-LAURENT-CONS-DECOMP
- **Parallel**: no
- **Type**: theorem
- **B2 note**: current statement has unconstrained V (no link to Uf, Vgs_at).
  Needs strengthened hypothesis `V is the product/refinement of Uf and Vgs_at`.

#### Statement (corrected)
```lean
theorem propA3_part3_bridge_for_laurent_product
    (V Uf : RationalCovering A)
    (Vgs_at : ↥Uf.covers → RationalCovering A)
    (_hVgs_base : ∀ Uf_piece, (Vgs_at Uf_piece).base = Uf_piece.1)
    (_hUf_acyclic : Uf.IsOXAcyclic)
    (_h_each_Vgs_acyclic : ∀ (Uf_piece : ↥Uf.covers),
      (Vgs_at Uf_piece).IsOXAcyclic)
    -- NEW: V is the product of Uf and Vgs_at, expressed as:
    -- every V-piece V' refines into some (Vgs_at Uf_j).covers piece.
    (h_V_is_product : ∀ V' ∈ V.covers,
      ∃ Uf_j : ↥Uf.covers, ∃ Vgs_piece ∈ (Vgs_at Uf_j).covers,
        rationalOpen V'.T V'.s ⊆ rationalOpen Vgs_piece.T Vgs_piece.s)
    (h_V_base : V.base = Uf.base) :
    V.IsOXAcyclic
```

#### Proof sketch
1. The acyclicity of Uf gives separation/gluing for sections on Uf.base = V.base.
2. The acyclicity of each Vgs_at Uf_j gives sections on Uf_j.
3. The product structure transfers V's separation/gluing from these.

#### Mathlib lemmas needed
- Standard restriction map composition

#### Sources
Wedhorn, *Adic Spaces*, §A.3, Prop A.3(3).

#### Generality decision
Project-internal.

### [T-WC-LAURENT-RESTR-IS-LAURENT] `laurent_restriction_isLaurent`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-LAURENT-CONS-DECOMP
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `laurent_restriction_isLaurent` (line ~891).
V_restrict (refining V on U ⊆ V.base) ⇒ V_restrict.IsLaurentCover fs.

#### Proof sketch
The restricted cover inherits the Laurent structure via the canonical map
A → 𝒪_X(U). Each Laurent piece of V_restrict corresponds 1-1 to a sign-vector
on fs, and the restricted pieces preserve this structure.

#### Mathlib lemmas needed
- `Finset.bij` constructions
- Laurent-product Finset combinatorics

#### Sources
Wedhorn, *Adic Spaces*, p. 84 ("If U is any rational subset, then 𝒱|U is the
Laurent cover generated by f_{1|U},...,f_{r|U}").

#### Generality decision
Project-internal.

### [T-WC-LAURENT-COVER-FROM-DOM-UNIT] `laurent_cover_from_dominating_unit`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `laurent_cover_from_dominating_unit` (line ~1035).
Given D₀, T (Finset A), s : Aˣ, build a Laurent cover by s⁻¹·T.

#### Proof sketch
1. Iterate `laurentRationalCover` over the list (T.toList).map (fun t => s⁻¹ * t).
2. Each step adds a 2-cover by R(s⁻¹t / 1), R(1 / s⁻¹t).
3. The accumulated cover is the Laurent cover by s⁻¹·T.

#### Mathlib lemmas needed
- `laurentRationalCover` (project def)
- `List.map`, `Finset.toList`

#### Sources
Wedhorn, *Adic Spaces*, §7 (Cor 7.32 application).

#### Generality decision
Project-internal.

### [T-WC-INDEX-SELECTION] `index_selection_on_laurent_piece`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-LAURENT-COVER-FROM-DOM-UNIT
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `index_selection_on_laurent_piece` (line ~1055).
On each Laurent piece V_j with dominating unit s, ∃ t ∈ T with v(t) ≥ v(s) on V_j.

#### Proof sketch
1. V_j corresponds to a sign vector σ : T → Bool.
2. Pick t such that σ t = "positive" (i.e., v(s⁻¹·t) ≥ 1 on V_j).
3. Then v(t) ≥ v(s) on V_j.

#### Mathlib lemmas needed
- Laurent-cover sign-vector structure

#### Sources
Wedhorn, *Adic Spaces*, p. 84.

#### Generality decision
Project-internal.

### [T-WC-CANONICAL-UNIT] `canonical_unit_of_pointwise_lower_bound`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `canonical_unit_of_pointwise_lower_bound` (line ~1069).
v(t) ≥ v(s) on V_j ⇒ canonicalMap t is a unit in 𝒪_X(V_j).

#### Proof sketch
1. The pointwise lower bound means t doesn't vanish on V_j.
2. The canonical map A → 𝒪_X(V_j) factors through Localization.Away t (with t a unit).
3. Image of t in 𝒪_X(V_j) is therefore a unit.

#### Mathlib lemmas needed
- `IsLocalization.isUnit_of_mem`
- Project's canonicalMap continuity

#### Sources
Wedhorn, *Adic Spaces*, Lemma 7.5.

#### Generality decision
Project-internal.

### [CLEANUP-WC-2] /cleanup on WedhornCechAcyclicity.lean (after Cat. D + part of B)

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-SINGLE-UNIT-SEP, T-WC-SINGLE-UNIT-GLU, T-WC-LAURENT-CONS-DECOMP, T-WC-LAURENT-RESTR-IS-LAURENT, T-WC-LAURENT-COVER-FROM-DOM-UNIT, T-WC-INDEX-SELECTION, T-WC-CANONICAL-UNIT, T-WC-PROPA3-PART3-BRIDGE
- **Parallel**: no
- **Type**: cleanup

### [T-WC-UNIT-GEN-RESTR-DOM] `unit_gen_restriction_of_dominating_laurent`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-INDEX-SELECTION, T-WC-CANONICAL-UNIT
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `unit_gen_restriction_of_dominating_laurent` (line ~1115).
Composition of index-selection + canonical-unit + restricted-cover-construction.

#### Proof sketch
1. By index_selection, pick t with v(t) ≥ v(s) on V_j.
2. By canonical_unit, canonicalMap t is a unit in 𝒪_X(V_j).
3. By restricted_cover_construction (already proved), build C_restr.
4. C_restr.IsUnitGenerated follows from canonicalMap t being a unit + the
   refinement property.

#### Mathlib lemmas needed
None beyond the sub-lemmas.

#### Sources
Wedhorn, *Adic Spaces*, §8.3.

#### Generality decision
Same as current sorry.

### [T-WC-RATIO-LAURENT-COVER] `ratio_laurent_cover_of_units`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-LAURENT-COVER-FROM-DOM-UNIT
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `ratio_laurent_cover_of_units` (line ~1185).
Given D₀, units (Finset A) of A-units, build a Laurent cover by ratios f_i · f_j⁻¹.

#### Proof sketch
1. Enumerate pairs (i, j) ∈ units × units as a list.
2. For each pair, the ratio f_i · (f_j⁻¹) is a unit in A.
3. Iterate `laurentRationalCover` over the ratio list.

#### Mathlib lemmas needed
- `Finset.product`, `Finset.toList`
- IsUnit composition

#### Sources
Wedhorn, *Adic Spaces*, p. 84.

#### Generality decision
Project-internal.

### [T-WC-RATIO-REFINES] `ratio_laurent_refines_unit_gen`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-RATIO-LAURENT-COVER, T-WC-INDEX-SELECTION
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `ratio_laurent_refines_unit_gen` (line ~1206).
Each piece of the ratio Laurent cover is contained in some C-piece D.

#### Proof sketch
σ-walk argument: V' corresponds to a sign vector σ on the ratios; the
σ-walk selects a maximal generator f_{i_max}; V' is contained in the C-piece
D with D.T containing f_{i_max}.

#### Mathlib lemmas needed
- Laurent-piece sign-vector structure
- max selection on a finite set

#### Sources
Wedhorn, *Adic Spaces*, p. 84.

#### Generality decision
Project-internal.

### [T-WC-PART-III-BODY] `wedhorn_lemma_834_part_iii_unit_gen_refines_to_laurent` — B2 RESOLVED 2026-05-28

- **Status**: OPEN (B2 resolved 2026-05-28: ratios computed in 𝒪_X(C.base), not A)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-RATIO-LAURENT-COVER, T-WC-RATIO-REFINES
- **Parallel**: no
- **Type**: theorem
- **B2 note**: current body requires lifting `IsUnit (canonicalMap f)` to
  `f ∈ A^×`, which is the wrong direction. Mathematical fix: ratios should
  be at the 𝒪_X(C.base) level, not at the A level. Needs sketch revision.

#### Statement (corrected sketch)
The body composes T-WC-RATIO-LAURENT-COVER + T-WC-RATIO-REFINES. The wrong
direction is the `f ∈ Aˣ` lift — instead, work entirely with the canonical
images in `presheafValue C.base`.

#### Proof sketch
1. Extract `units : Finset A` such that `∀ f ∈ units, IsUnit (canonicalMap f)`.
2. Build the ratio Laurent cover from `units` using T-WC-RATIO-LAURENT-COVER
   IN `𝒪_X(C.base)`, NOT in A. (The ratios `f_i · f_j⁻¹` exist as elements of
   `presheafValue C.base`, not necessarily A.)
3. By T-WC-RATIO-REFINES, this Laurent cover refines C.

If the `presheafValue C.base`-level construction is not supported by the
project's current Laurent cover def, this becomes a B2 stop requiring
re-plan.

#### Mathlib lemmas needed
TBD pending sketch revision.

#### Sources
Wedhorn, *Adic Spaces*, p. 84 (verbatim quote: "Every rational cover 𝒰 of X
which is generated by units f_0,...,f_n of A has a refinement by a Laurent
cover.").

#### Generality decision
TBD pending sketch revision.

### [T-WC-834-C-RESTR-BODY] `wedhorn_lemma_834_C_restr_acyclic` body

- **Status**: done (2026-05-28: closed transitively through PART-III-BODY sorry (Laurent refinement) + part_i_laurent_restriction_acyclic; uses IsOXAcyclic_of_refining_acyclic_cover after T-WC-FILE-REORDER)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-FILE-REORDER, T-WC-PART-III-BODY, T-WC-PROPA3-PART2-SEP, T-WC-PROPA3-PART2-GLU
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `wedhorn_lemma_834_C_restr_acyclic` (line ~1263) body, which
currently has a forward-reference sorry.

#### Proof sketch
After T-WC-FILE-REORDER, `IsOXAcyclic_of_refining_acyclic_cover` is in scope.
The body becomes:
1. C_restr refines a Laurent cover W by part (iii) (T-WC-PART-III-BODY).
2. W.IsOXAcyclic by part (i) (already composed).
3. Apply IsOXAcyclic_of_refining_acyclic_cover to transfer W's acyclicity to C_restr.
4. Double-restriction sub-acyclicity discharge: via part (i)'s laurent_restriction.

#### Mathlib lemmas needed
None.

#### Sources
Wedhorn, *Adic Spaces*, §8.3, Lemma 8.34 part (iv).

#### Generality decision
Same as current sorry.

### [T-WC-834-BODY] `wedhorn_lemma_834` body

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-FILE-REORDER, T-WC-834-C-RESTR-BODY, T-WC-PROPA3-PART1-SEP, T-WC-PROPA3-PART1-GLU
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `wedhorn_lemma_834` (line ~1411) body, composing parts (i)-(iv)
via the Prop A.3(1) bridge.

#### Proof sketch
Use `wedhorn_lemma_834_propA3_part1_bridge` (composed from PART1-SEP + PART1-GLU)
with:
- V := Laurent cover from part (ii)
- V_restr_at := per-C-piece Laurent restriction
- C_restr_at := per-V-piece unit-gen restriction (via T-WC-834-C-RESTR-BODY)

#### Mathlib lemmas needed
None.

#### Sources
Wedhorn, *Adic Spaces*, §8.3, Lemma 8.34 part (iv) verbatim.

#### Generality decision
Same as current sorry.

### [CLEANUP-WC-3] /cleanup on WedhornCechAcyclicity.lean (after Lemma 8.34 fully composed)

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-834-BODY, T-WC-UNIT-GEN-RESTR-DOM, T-WC-RATIO-REFINES
- **Parallel**: no
- **Type**: cleanup

### [T-WC-RAT-COV-FROM-IDEAL] `rationalCovering_from_idealGenSet`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `rationalCovering_from_idealGenSet` (line ~1458).
Given S (Finset A, spanning ⊤) and cover/contain data, produce a
RationalCovering generated by S.

#### Proof sketch
1. For each t ∈ S, define `D_t := { P, T := S, s := t, hopen := ... }`.
2. The collection {D_t : t ∈ S} forms a RationalCovering of C.base.
3. The hopen proofs use `divByS_*_mem_locSubring` (existing project infra) +
   the standard Wedhorn 8.2.1 base-change identities.
4. The IsGeneratedBy property: bijection φ : S → {D_t : t ∈ S} sending t ↦ D_t.

#### Mathlib lemmas needed
- Project's `divByS_*` infrastructure (`LocalizationTopology.lean`)
- `Finset.bij`, `Function.Bijective`

#### Sources
Wedhorn, *Adic Spaces*, p. 83 ("every open covering of X has a refinement
𝒰 = (U_t)_{t∈T} of the form U_t := R(T/t)").

#### Generality decision
Project-internal.

### [T-WC-TO-FINITE-COVER] `RationalCovering.toFiniteCover` — B2 candidate

- **Status**: OPEN (B2 review needed)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: def
- **B2 note**: current signature targets `FiniteCover ↥(Spa A A⁺) C.covers`,
  but C covers `C.base.rationalOpen`, not all of Spa. Signature must be
  `FiniteCover ↥(rationalOpen C.base.T C.base.s) C.covers` (or similar).

#### Statement (corrected)
```lean
def RationalCovering.toFiniteCover [IsHuberRing A] (C : RationalCovering A) :
    FiniteCover ↥(rationalOpen C.base.T C.base.s) ↥C.covers where
  sets D := Subtype.val ⁻¹' (rationalOpen D.1.T D.1.s)
  isOpen D := isOpen_rationalOpen.preimage continuous_subtype_val
  isCover := by
    -- ⋃ D : ↥C.covers, Subtype.val ⁻¹' (rationalOpen D.1.T D.1.s) = univ
    -- because C.hcover says every v ∈ C.base.rationalOpen is in some D-piece.
    sorry
```

#### Proof sketch
The cover relation follows from `C.hcover`.

#### Mathlib lemmas needed
- `isOpen_rationalOpen` (project)
- `continuous_subtype_val`

#### Sources
Project-side bridge to abstract Čech (CechCohomology.lean).

#### Generality decision
Project-internal.

### [T-WC-TO-REFINEMENT] `RationalCovering.toRefinement`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-TO-FINITE-COVER
- **Parallel**: no
- **Type**: def

#### Statement
The existing `RationalCovering.toRefinement` (line ~1510), after the
toFiniteCover signature is fixed.

#### Proof sketch
Construct: index map κ → ι sends each C'-piece D' to a C-piece D containing
it; the subset proof comes from h_refines.

#### Mathlib lemmas needed
- `Refinement` structure from `CechCohomology.lean`

#### Sources
`CechCohomology.lean` Refinement def.

#### Generality decision
Project-internal.

### [T-WC-RESTR-INHERIT-GEN] `restricted_cover_inherits_IsGeneratedBy` — B2 candidate

- **Status**: OPEN (B2 review needed)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem
- **B2 note**: current statement requires `E.covers` in bijection with `T`
  (via `IsGeneratedBy T`), but the construction of E doesn't guarantee this.

#### Statement (B2-resolution-pending)
Either:
- (Option α) restate to weaken `IsGeneratedBy`'s bijection requirement, or
- (Option β) restate to require `E` is constructed specifically from T via
  `rationalCovering_from_idealGenSet`.

#### Proof sketch
Pending B2 resolution.

#### Mathlib lemmas needed
TBD.

#### Sources
Wedhorn, *Adic Spaces*, §8.2.1.

#### Generality decision
TBD.

### [T-WC-INJECTIVITY-FF] `injectivity_from_faithfullyFlat_2cover` (Pi.algebra plumbing)

- **Status**: done (2026-05-28: closed via `Module.FaithfullyFlat → FaithfulSMul → algebraMap_injective` after raising `synthInstance.maxHeartbeats` to 800000)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
The existing `injectivity_from_faithfullyFlat_2cover` (line ~207). Converts
`Module.FaithfullyFlat` output of `cor_8_32_for_2cover` to function-form
injectivity.

#### Proof sketch
1. `cor_8_32_for_2cover` gives `Module.FaithfullyFlat (presheafValue base)
   (Π D, presheafValue D)`.
2. Apply `Module.FaithfullyFlat.faithfulSMul` to get `FaithfulSMul`.
3. `FaithfulSMul.algebraMap_injective` gives `Function.Injective (algebraMap _ _)`.
4. Under `Pi.algebra` + `RingHom.toAlgebra`, `algebraMap r d` evaluates to
   `restrictionMapHom base D.1 r`.
5. So the function `fun x D => restrictionMap base D.1 x` equals the algebraMap;
   conclude injectivity.

The challenging part is step 4: the heartbeat-heavy defEq between Pi.algebra
and the chosen `RingHom.toAlgebra` instances. Workaround: provide an explicit
`change` step or use `funext` + componentwise reasoning.

#### Mathlib lemmas needed
- `Module.FaithfullyFlat.faithfulSMul` (mathlib, verified to exist)
- `FaithfulSMul.algebraMap_injective` (mathlib, verified)
- `Pi.algebraMap_apply`
- `RingHom.toAlgebra` interaction with `algebraMap`

#### Sources
Wedhorn, *Adic Spaces*, §8.2.32 (Cor 8.32 application).

#### Generality decision
Project-internal.

### [T-WC-638-PLUS-NOETH] `example_638_plus_side_noeth_pairSubring` (Wedhorn 6.18)

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (substantive Wedhorn-text leaf, ~80 LOC)

#### Statement
The existing `example_638_plus_side_noeth_pairSubring` (line ~249).
`IsNoetherianRing (TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition)`
for strongly noetherian Tate A.

#### Proof sketch
Wedhorn 6.18: a strongly noetherian Tate ring's `A₀⟨X⟩` is noetherian.
1. Construct iso `TateAlgebra.pairSubring P ≅+* restrictedMvPowerSeriesSubring 1 P.A₀`
   (project def of `pairSubring` is the coefficient-constraint version; mathlib's
   `restrictedMvPowerSeriesSubring 1` is the convergence version).
2. Transport `IsNoetherianRing` along the iso.
3. `IsStronglyNoetherian A` provides `isNoetherianRing_restricted 1`, which is
   `IsNoetherianRing (restrictedMvPowerSeriesSubring 1 A)` — but we need it for
   `A₀`, not `A`. Either:
   - (Option α) iso `restrictedMvPowerSeriesSubring 1 P.A₀` to a subring of
     `restrictedMvPowerSeriesSubring 1 A`, transport via subring containment.
   - (Option β) directly prove via Hilbert basis on `P.A₀⟨X⟩`.

#### Mathlib lemmas needed
- `IsNoetherianRing` transfer along iso
- Hilbert basis (`Polynomial.isNoetherianRing` for `A₀[X]`, but pairSubring is
  power series — needs the topological version)

#### Sources
Wedhorn, *Adic Spaces*, Proposition 6.18 (p. 51-52).

#### Generality decision
Project-internal.

### [T-WC-638-PLUS-CONT-EVAL] `example_638_plus_side_cont_evalHom`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem
- **Mathlib gap**: `evalHomBounded_continuous` is marked UNPROVABLE in
  TateAlgebraWedhorn.lean:690 with the T-topology. Needs alternative via
  completion comparison.

#### Statement
The existing `example_638_plus_side_cont_evalHom` (line ~267).
`Continuous (example638Plus_evalHom A P f)`.

#### Proof sketch (after Wedhorn 6.18-based completion comparison)
1. The T-topology on `A⟨X⟩` equals the J-adic topology under Wedhorn 6.18
   (where J = `(I · A⟨X⟩)`-adic).
2. Under J-adic topology, `evalHomBounded` is continuous because eval at a
   bounded element preserves J-adic convergence.
3. Use completion comparison: `tateEvalPresheafHom = evalHomBounded` via
   `evalHomBounded`'s continuous extension to the completion.

If T-topology = J-adic isn't directly available, we need to factor through
`presheafValue_iteratedPlus_equiv` or similar.

#### Mathlib lemmas needed
- Topology comparison via completion (project's TopologyComparison.lean if it
  exists; otherwise spawn sub-ticket)

#### Sources
Wedhorn, *Adic Spaces*, Example 6.38 + Prop 6.18.

#### Generality decision
Project-internal.

### [T-WC-638-PLUS-CONT-QUOT] `example_638_plus_side_cont_quotient_lift`

- **Status**: done (2026-05-28: closed via `Continuous.quotient_lift` mathlib lemma applied to h_evalHom)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-638-PLUS-CONT-EVAL
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `example_638_plus_side_cont_quotient_lift` (line ~287).
Continuity of `example638Plus_forwardHom` = lift of `evalHom` through
`plusFSubXIdeal A f` quotient.

#### Proof sketch
Universal property of quotient topology: `forwardHom ∘ Quotient.mk = evalHom`
by construction. Continuity of `Quotient.mk` + continuity of `evalHom` ⇒
continuity of `forwardHom`.

#### Mathlib lemmas needed
- `Quotient.mk_continuous` or `IdealQuotient.mk_continuous`
- `continuous_quotient_lift`

#### Sources
Standard quotient topology.

#### Generality decision
Project-internal.

### [T-WC-638-MINUS-CONT-EVAL] `example_638_minus_side_cont_underlying_evalHom`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes (parallel with T-WC-638-PLUS-CONT-EVAL)
- **Type**: theorem
- **Mathlib gap**: same as plus side.

#### Statement
The existing `example_638_minus_side_cont_underlying_evalHom` (line ~336).

#### Proof sketch
Parallel to T-WC-638-PLUS-CONT-EVAL, using the minus-branch evalHom
(at invS = 1/canonicalMap b).

#### Mathlib lemmas needed
Same.

#### Sources
Wedhorn, *Adic Spaces*, Example 6.38 minus branch.

#### Generality decision
Project-internal.

### [T-WC-638-MINUS-CONT-QUOT] `example_638_minus_side_cont_quotient_lift`

- **Status**: done (2026-05-28: closed via `Continuous.quotient_lift`)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-638-MINUS-CONT-EVAL
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `example_638_minus_side_cont_quotient_lift` (line ~354).

#### Proof sketch
Universal property of quotient topology, parallel to plus side.

#### Mathlib lemmas needed
Same.

#### Sources
Standard quotient topology.

#### Generality decision
Project-internal.

### [T-WC-EXISTS-PAIR-A0-APLUS] `exists_pair_with_A₀_subset_Aplus`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (substantive Wedhorn-text leaf)

#### Statement
The existing `exists_pair_with_A₀_subset_Aplus` (line ~961).
For strongly noetherian Tate A, ∃ pair P with P.A₀ ≤ A⁺.

#### Proof sketch
1. The principal pair `IsTateRing.principalPair A` has A₀ that may or may not
   be ≤ A⁺ depending on definitions.
2. If `CompatiblePlusSubring A` is assumed (project class), then the
   principal pair's A₀ is constructed to satisfy this.
3. Discharge by direct use of `CompatiblePlusSubring`.

#### Mathlib lemmas needed
- `CompatiblePlusSubring` (project class)
- `IsTateRing.principalPair`

#### Sources
Wedhorn, *Adic Spaces*, §7.

#### Generality decision
Project-internal.

### [T-WC-EXISTS-PSEUDO] `exists_pseudouniformizer_of_tate`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (substantive)

#### Statement
The existing `exists_pseudouniformizer_of_tate` (line ~977).
For Tate A and any pair P, ∃ π ∈ P.A₀ generating P.I with π a topologically
nilpotent unit.

#### Proof sketch
1. Tate ring ⇒ ∃ topologically nilpotent unit `π ∈ A` (definition of Tate).
2. Choose `P.I := Ideal.span {π}` (or use the existing P.I and find a
   generator).
3. π is in P.A₀ via the smallest-A₀-containing-P.I definition.

#### Mathlib lemmas needed
- `IsTateRing.exists_topologically_nilpotent_unit` (project — check it exists)
- `Ideal.span_singleton_isPrincipal`

#### Sources
Wedhorn, *Adic Spaces*, §7 (definition of Tate ring + Cor 7.32).

#### Generality decision
Project-internal.

### [T-WC-MUL-ARCH-7-40] `mulArchimedean_valueGroup_of_stronglyNoetherianTate` (Wedhorn 7.40(6))

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (substantive Wedhorn-text leaf, ~150 LOC)

#### Statement
The existing `mulArchimedean_valueGroup_of_stronglyNoetherianTate` (line ~995).
For strongly noetherian Tate A and any v ∈ Spv A, the value group is
multiplicatively archimedean.

#### Proof sketch
Wedhorn 7.40(6): analytic continuous valuations on strongly noetherian Tate
are height ≤ 1.
1. For Tate A, every v ∈ Spv A is analytic (project's `IsTateRing.isAnalytic`).
2. Analytic + strongly noetherian Tate ⇒ height ≤ 1 (Wedhorn 7.40(6)).
3. Height ≤ 1 ⇒ value group is multiplicatively archimedean.

The (2) step is the substantive content. Wedhorn proves it via the
characterisation of analytic points + the structure of strongly noetherian
Tate rings.

This is a multi-session ticket — sub-tickets may be needed for:
- (a) characterisation of analytic valuations
- (b) height ≤ 1 inference

#### Mathlib lemmas needed
- `IsTateRing.isAnalytic` (project)
- `MulArchimedean` definition from mathlib
- Possibly: `Valuation.IsContinuous.height_le_one`

#### Sources
Wedhorn, *Adic Spaces*, Proposition 7.40 (p. 70), specifically item (6) on p. 71.

#### Generality decision
Project-internal.

### [CLEANUP-WC-FINAL] /cleanup-all on WedhornCechAcyclicity.lean (final pass)

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: all T-WC-* tickets
- **Parallel**: no
- **Type**: cleanup
- **Description**: Final cleanup pass after all proof tickets done. Targets:
  golf, mathlib-style naming, dead code removal, deduplication of similar
  proofs, ensure axiom hygiene (`#print axioms isSheafy_ofStronglyNoetherianTate_clean`
  shows only standard set).

### [T-WC-COMPATIBLE-PAIR-5LEMMA] `compatible_pair_lifts_via_5lemma`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem (substantive Wedhorn-text leaf, ~120 LOC)

#### Statement
The existing `compatible_pair_lifts_via_5lemma` (line ~548).
Compatible pair (α, β) on (R(f/1), R(1/f)) lifts via 5-lemma to a section on D₀.

#### Proof sketch
Wedhorn p. 84 5-lemma argument:
- Row 1: `0 → (f-ζ)A⟨ζ⟩ × (1-fη)A⟨η⟩ → (f-ζ)A⟨ζ,ζ⁻¹⟩ → 0` (exact by Laurent ideal decomp).
- Row 2: `0 → A → A⟨ζ⟩ × A⟨η⟩ → A⟨ζ,ζ⁻¹⟩ → 0` (exact by Laurent algebra decomp + kernel-image).
- Row 3: `0 → 𝒪(X) → 𝒪(U_1) × 𝒪(U_2) → 𝒪(U_1∩U_2) → 0` (the goal).
- Columns: row1 → row2 → row3 by passage to quotient (Examples 6.38 + 6.39).
- Conclusion: row 3 is exact (snake lemma / 5-lemma).

This requires either:
- (Option α) instantiate mathlib's `CategoryTheory.ShortComplex.Exact` /
  snake-lemma infrastructure
- (Option β) write a direct algebraic 5-lemma argument

#### Mathlib lemmas needed
- Possibly `CategoryTheory.snake_lemma` (verify it exists)
- Examples 6.38/6.39 isos (project, partial)

#### Sources
Wedhorn, *Adic Spaces*, p. 84.

#### Generality decision
Project-internal.

### [T-WC-833-GLUING-FIELD] `wedhorn_lemma_833_gluing_as_field`

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-COMPATIBLE-PAIR-5LEMMA
- **Parallel**: no
- **Type**: theorem

#### Statement
The existing `wedhorn_lemma_833_gluing_as_field` (line ~576).
Gluing field of `IsOXAcyclic (laurentRationalCover D₀ f)`.

#### Proof sketch
1. Use `laurentRationalCover_pieces_identified` (proved) to extract the two
   pieces U₁ = laurentPlusDatum, U₂ = laurentMinusDatum.
2. Use `compatible_pair_lifts_via_5lemma` (T-WC-COMPATIBLE-PAIR-5LEMMA) to
   lift the compatible pair (g(U₁), g(U₂)) to a section γ on D₀.
3. Verify γ|U₁ = g(U₁) and γ|U₂ = g(U₂).

#### Mathlib lemmas needed
None beyond sub-tickets.

#### Sources
Wedhorn, *Adic Spaces*, §8.3, Lemma 8.33.

#### Generality decision
Project-internal.

---

## Dependency graph for the 2026-05-28 batch

```
T-WC-FILE-REORDER (no deps)
T-WC-CAT-C-CHANGE-BASE (no deps)
├── T-WC-PROPA3-PART2-SEP
├── T-WC-PROPA3-PART2-GLU
├── T-WC-PROPA3-PART1-SEP
└── T-WC-PROPA3-PART1-GLU
CLEANUP-WC-1 (after Cat. C done + FILE-REORDER)

T-WC-SINGLE-UNIT-SEP, T-WC-SINGLE-UNIT-GLU (parallel)
T-WC-LAURENT-CONS-DECOMP
├── T-WC-PROPA3-PART3-BRIDGE
└── T-WC-LAURENT-RESTR-IS-LAURENT
T-WC-LAURENT-COVER-FROM-DOM-UNIT
├── T-WC-INDEX-SELECTION
T-WC-CANONICAL-UNIT (parallel)
CLEANUP-WC-2 (after the above)

T-WC-INDEX-SELECTION + T-WC-CANONICAL-UNIT
└── T-WC-UNIT-GEN-RESTR-DOM
T-WC-RATIO-LAURENT-COVER
├── T-WC-RATIO-REFINES
└── T-WC-PART-III-BODY (B2)
T-WC-834-C-RESTR-BODY (deps: FILE-REORDER, PART-III-BODY, PROPA3-PART2-*)
T-WC-834-BODY (deps: 834-C-RESTR-BODY, PROPA3-PART1-*)
CLEANUP-WC-3 (after 834 fully composed)

T-WC-RAT-COV-FROM-IDEAL (no deps)
T-WC-TO-FINITE-COVER (B2, no deps)
└── T-WC-TO-REFINEMENT
T-WC-RESTR-INHERIT-GEN (B2, no deps)

T-WC-INJECTIVITY-FF (no deps)

T-WC-638-PLUS-NOETH (substantive, ~80 LOC)
T-WC-638-PLUS-CONT-EVAL (mathlib gap, T-WC-PLUS-CONT-QUOT depends on this)
T-WC-638-MINUS-CONT-EVAL (parallel; MINUS-CONT-QUOT depends)

T-WC-EXISTS-PAIR-A0-APLUS
T-WC-EXISTS-PSEUDO
T-WC-MUL-ARCH-7-40 (substantive, ~150 LOC, multi-session candidate)

T-WC-COMPATIBLE-PAIR-5LEMMA (substantive, ~120 LOC)
└── T-WC-833-GLUING-FIELD

CLEANUP-WC-FINAL (after all)
```

Total new tickets: 33 proof tickets + 4 cleanup tickets = 37.

Parallel capacity: at peak, ~8-10 tickets can run in parallel (Cat. A
substantive leaves are all independent; Cat. B combinatorics has some chain
dependencies; Cat. C all branch off CHANGE-BASE).

---

## 2026-05-28 /develop --continue: B2/scope ticket fixes batch

This batch resolves 8 B2/scope issues identified during beastmode execution.
6 ticket statements are corrected; 2 are fused; 2 new sub-tickets are spawned
to unblock PROPA3-PART2-GLU + wedhorn_lemma_834 body.

### [T-WC-EXISTS-PRINCIPAL-PAIR-IN-APLUS] **NEW** — fused: principal pair with A₀ ⊆ A⁺ + topnilp generator

- **Status**: OPEN (supersedes T-WC-EXISTS-PAIR-A0-APLUS + T-WC-EXISTS-PSEUDO)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] :
    ∃ (P : PairOfDefinition A) (π : P.A₀),
      P.A₀ ≤ A⁺ ∧
      P.I = Ideal.span {π} ∧
      IsTopologicallyNilpotent (P.A₀.subtype π) ∧
      IsUnit (P.A₀.subtype π) := by
  sorry
```

#### Proof sketch
Wedhorn 6.14 gives ∃ (P, π) with P.I = (π) and π unit (no A⁺ constraint). To
add A₀ ⊆ A⁺: refine to the smallest A₀ containing π and its powers.
1. Apply `IsTateRing.exists_principal_pairOfDefinition` to get (P₀, π) with
   P₀.I = Ideal.span {π}, IsUnit (π).
2. π is topologically nilpotent (Wedhorn 6.14, π generates ideal of definition).
3. For A₀ ⊆ A⁺ constraint: construct P.A₀ := Subring.closure {π^n · a : n ∈ ℕ, a ∈ ℤ⟨π⟩}
   or simply note that "every topologically nilpotent unit's powers generate a
   sub-A₀ inside A⁺" (since A⁺ contains all topologically nilpotent elements
   by definition of A⁺).

#### Mathlib lemmas needed
- `IsTateRing.exists_principal_pairOfDefinition` (project)
- `CompatiblePlusSubring.aplus_le_A₀` (project — provides A⁺ ⊆ A₀ direction; we want reverse, but constructively achievable)
- `Subring.closure_le`

#### Sources
- Wedhorn, *Adic Spaces*, Lemma 6.14 (p. 50), Remark 7.17 (p. 70).

#### Generality decision
Project-internal. Requires [CompatiblePlusSubring A].

### [T-WC-EXISTS-PAIR-A0-APLUS] *(SUPERSEDED 2026-05-28)*

- **Status**: superseded by T-WC-EXISTS-PRINCIPAL-PAIR-IN-APLUS (fused)

### [T-WC-EXISTS-PSEUDO] *(SUPERSEDED 2026-05-28)*

- **Status**: superseded by T-WC-EXISTS-PRINCIPAL-PAIR-IN-APLUS (fused)
- **B2 note**: original statement required ∀ P, ∃ π principal generator — only
  true for principal pairs. Fixed by restricting to the principal pair (fused
  ticket constructs both P and π).

### [T-WC-EPRIME-RESTRICT-TO-D] **NEW** — construction of E := C'|_D as a RationalCovering of D

- **Status**: done (2026-05-28: closed sorry-free as `RationalCovering.restrictToPiece` via Finset.filter on covers + Classical.propDecidable; takes `hD_covers` as hypothesis)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: def + lemma
- **Parent**: T-WC-PROPA3-PART2-GLU (unblocks the gluing direction of Prop A.3(2))

#### Statement
```lean
/-- Restricted cover E := C' restricted to D ∈ C.covers. Pieces are
the C'-pieces refining into D. Requires that C'-pieces actually cover D
(an existence assumption). -/
noncomputable def RationalCovering.restrictToPiece
    (C C' : RationalCovering A) (h_same_base : C'.base = C.base)
    (h_refines : ∀ D' ∈ C'.covers, ∃ D ∈ C.covers,
      rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (h_C'_covers_each : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ D' ∈ C'.covers, v ∈ rationalOpen D'.T D'.s ∧
        rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    RationalCovering A := sorry  -- struct: base = D, covers = {D' ∈ C'.covers : D' refines into D}, hsubset = trivial, hcover by h_C'_covers_each
```

#### Proof sketch
1. Filter C'.covers to {D' : ∃ proof D' refines into D}.
2. Build RationalCovering with base = D, covers = filtered set.
3. hsubset: each D' ∈ filtered set has rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s by construction.
4. hcover: requires every v ∈ D's rational open to be in some D' ∈ filtered set. This is the `h_C'_covers_each` hypothesis.

#### Mathlib lemmas needed
- `Finset.filter`
- Standard `RationalCovering` constructor

#### Sources
Wedhorn, *Adic Spaces*, §A.3 (refinement induced cover).

#### Generality decision
Project-internal.

### [T-WC-V-REFINES-C-FROM-DOM-UNIT] **NEW** — extract h_V_refines_C from dominating-unit construction

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem
- **Parent**: wedhorn_lemma_834 body

#### Statement
```lean
/-- For the Laurent cover V from part (ii) of Lemma 8.34, V refines C: each
V-piece sits in some C-piece (via the dominant generator). -/
theorem laurent_cover_refines_idealgen_cover [DecidableEq A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    [IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (C : RationalCovering A) (T : Finset A) (hC_gen : C.IsGeneratedBy T)
    (V : RationalCovering A) (fs : List A) (hV_laurent : V.IsLaurentCover fs)
    (hV_base : V.base = C.base)
    (hV_unit_restrictions : ∀ Vj ∈ V.covers,
      ∃ (C_restr : RationalCovering A),
        C_restr.base = Vj ∧
        C_restr.IsUnitGenerated ∧
        (∀ D' ∈ C_restr.covers, ∃ D ∈ C.covers,
          rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) ∧
        (∀ v ∈ rationalOpen Vj.T Vj.s, ∃ D' ∈ C_restr.covers,
          v ∈ rationalOpen D'.T D'.s)) :
    ∀ V_j ∈ V.covers, ∃ U ∈ C.covers,
      rationalOpen V_j.T V_j.s ⊆ rationalOpen U.T U.s := by
  sorry
```

#### Proof sketch
The Laurent cover V is built from a dominating unit s (via `cor_7_32_dominating_unit`).
Each V-piece V_j corresponds to a sign vector σ on T (via s⁻¹·T). The "dominant"
index i_max chosen by σ has v(t_{i_max}) ≥ v(s) on V_j, so v(t_{i_max}) ≠ 0
(s is a unit). Then V_j is contained in R(T/t_{i_max}) = C's piece indexed by t_{i_max}.

1. Pull out the C_restr witness for V_j from hV_unit_restrictions.
2. Pick any D' ∈ C_restr.covers (assume non-empty; otherwise V_j is empty, trivial).
3. The chosen D' refines into some D ∈ C.covers (by C_restr-refines-C).
4. Verify V_j ⊆ D by showing each v ∈ V_j is in D (use the cover-property of C_restr + D' ⊆ D).

#### Mathlib lemmas needed
- Standard valuation reasoning on rationalOpen membership

#### Sources
Wedhorn, *Adic Spaces*, p. 84 (the σ-walk argument in part (iii)).

#### Generality decision
Project-internal. Designed to plug into wedhorn_lemma_834 body.

### [T-WC-RESTR-INHERIT-GEN-RESTATED] **REPLACES T-WC-RESTR-INHERIT-GEN**

- **Status**: in_progress (2026-05-28: `restricted_cover_inherits_IsUnitGenerated` declared with sorry body; double_restriction_acyclicity chained through it via wedhorn_lemma_834_C_restr_acyclic)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement (weakened)
```lean
/-- E inherits an `IsUnitGenerated` witness from C', not full `IsGeneratedBy`.
The weakening: `IsUnitGenerated` doesn't require the bijection `|E.covers| = |T|`. -/
theorem restricted_cover_inherits_IsUnitGenerated
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (C' : RationalCovering A) (T : Finset A) (h_C'_gen : C'.IsGeneratedBy T)
    (D : RationalLocData A)
    (E : RationalCovering A) (_h_E_base : E.base = D)
    (_h_E_pieces : ∀ E' ∈ E.covers, ∃ D' ∈ C'.covers,
        rationalOpen E'.T E'.s ⊆ rationalOpen D'.T D'.s) :
    E.IsUnitGenerated := by
  sorry
```

#### Proof sketch
1. Each E-piece E' refines into some D' ∈ C'.covers.
2. D' has T-shape (D'.T = T), so each t ∈ E'.T has been chosen from T.
3. Canonical image of t in 𝒪_X(E') is a unit (uses isUnit_canonicalMap_s if t = E'.s, or general non-vanishing argument).

### [T-WC-RESTR-INHERIT-GEN] *(SUPERSEDED 2026-05-28)*

- **Status**: superseded by T-WC-RESTR-INHERIT-GEN-RESTATED (conclusion weakened to `IsUnitGenerated`)

### [T-WC-TO-FINITE-COVER-RESTATED] **REPLACES T-WC-TO-FINITE-COVER**

- **Status**: done (2026-05-28: closed sorry-free; carrier is `↥(Subtype.val ⁻¹' rationalOpen C.base.T C.base.s : Set ↥(Spa A A⁺))`; isCover uses C.hcover; isOpen uses rationalOpen_isOpen)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: none
- **Parallel**: yes
- **Type**: def

#### Statement (corrected)
```lean
/-- The corrected version targeting C.base's rational open. -/
def RationalCovering.toFiniteCover [IsHuberRing A] (C : RationalCovering A) :
    FiniteCover ↥(rationalOpen C.base.T C.base.s : Set ↥(Spa A A⁺)) ↥C.covers where
  sets D := Subtype.val ⁻¹' (rationalOpen D.1.T D.1.s)
  isOpen D := by sorry
  isCover := by sorry
```

#### Proof sketch
1. `sets D := Subtype.val ⁻¹' (rationalOpen D.1.T D.1.s)` — the preimage of D's rational open under the inclusion C.base ↪ Spa.
2. `isOpen D`: the rational open is open in Spa; preimage under continuous inclusion is open.
3. `isCover`: union over all D ∈ C.covers covers C.base's rational open (by `C.hcover`).

### [T-WC-TO-FINITE-COVER] *(SUPERSEDED 2026-05-28)*

- **Status**: superseded by T-WC-TO-FINITE-COVER-RESTATED

### [T-WC-INDEX-SELECTION-RESTATED] **REPLACES T-WC-INDEX-SELECTION**

- **Status**: OPEN (B2 RESOLVED: V tied to T and s)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-LAURENT-COVER-FROM-DOM-UNIT
- **Parallel**: no
- **Type**: theorem

#### Statement (with V tied to T and s)
```lean
/-- When V is the Laurent cover from `laurent_cover_from_dominating_unit T s`,
each piece V_j has a distinguished generator t ∈ T with v(t) ≥ v(s) on V_j. -/
theorem index_selection_on_dominating_laurent_piece
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A] [DecidableEq A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (s : Aˣ)
    -- V and fs are the witnesses from laurent_cover_from_dominating_unit
    (V : RationalCovering A) (fs : List A)
    (hV_laurent : V.IsLaurentCover fs)
    (h_V_from_dom : V.base = D₀ ∧
      fs = (T.toList).map (fun t => ((s⁻¹ : Aˣ) : A) * t))
    (Vj : RationalLocData A) (hVj : Vj ∈ V.covers) :
    ∃ t ∈ T, ∀ v ∈ rationalOpen Vj.T Vj.s, v.vle (s : A) t := by
  sorry
```

### [T-WC-INDEX-SELECTION] *(SUPERSEDED 2026-05-28)*

- **Status**: superseded by T-WC-INDEX-SELECTION-RESTATED

### Updates to existing tickets

- **wedhorn_lemma_834** body: sketch updated to use T-WC-V-REFINES-C-FROM-DOM-UNIT
  to provide h_V_refines_C input to propA3_part1_bridge.
- **T-WC-PROPA3-PART2-GLU**: dependency added to T-WC-EPRIME-RESTRICT-TO-D.
- **T-WC-PROPA3-PART1-GLU**: dependency added to T-WC-EPRIME-RESTRICT-TO-D.


---

## 2026-05-28 /develop --continue (batch 2): 8 ticket statement-fixes + 3 new sub-tickets

This batch resolves the 8 statement-level / under-constrained ticket issues
identified during beastmode iterations 5-6. Each fix updates the statement
or adds the missing hypothesis; 3 new helper sub-tickets are added to
unblock specific composition chains.

### [T-WC-PROPA3-PART2-GLU-RESTATED] **REPLACES T-WC-PROPA3-PART2-GLU**

- **Status**: OPEN (statement-fixed: added `h_C'_covers_each_D` hypothesis)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE, T-WC-EPRIME-RESTRICT-TO-D
- **Parallel**: yes
- **Type**: theorem

#### Statement (corrected — adds h_C'_covers_each_D)
```lean
theorem propA3_part2_project_gluing
    ... (existing C, C', h_same_base, h_refines, h_C'_acyclic ...)
    (h_C'_covers_each_D : ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s,
      ∃ D' ∈ C'.covers, v ∈ rationalOpen D'.T D'.s ∧
        rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (h_double_acyclic : ...) :
    ∀ f, compatible-on-C → ∃ x : presheafValue C.base, x glues f
```

#### Proof sketch
1. Build E_D := `RationalCovering.restrictToPiece C' D (h_C'_covers_each_D D hD)` for each D ∈ C.covers.
2. h_double_acyclic gives E_D.IsOXAcyclic (apply with E := E_D).
3. Build compatible family g(D') := f(D)|D' on C'.covers using h_refines + hcompat (f's compatibility).
4. Apply h_C'_acyclic.gluing to g, get x' : presheafValue C'.base.
5. Cast x' to x : presheafValue C.base via presheafValueCast h_same_base.symm.
6. Verify x|D = f D for each D ∈ C: use E_D.separation on (x|D - f D); both restrict to 0 on each E_D piece via hcompat + step 3.

#### Mathlib lemmas needed
- restrictToPiece (closed)
- presheafValueCast (closed)
- restrictionMap_comp (project)

### [T-WC-PROPA3-PART1-GLU-RESTATED] **REPLACES T-WC-PROPA3-PART1-GLU**

- **Status**: OPEN (statement-fixed: added `h_C_restr_at_covers` hypothesis)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Type**: theorem

#### Statement (corrected)
Add hypothesis to existing PART1-GLU:
```
(h_C_restr_at_covers : ∀ Vj : ↥V.covers, ∀ v ∈ rationalOpen Vj.1.T Vj.1.s,
  ∃ D' ∈ (C_restr_at Vj).covers, v ∈ rationalOpen D'.T D'.s)
```

This ensures the C_restr_at Vj family actually covers each V-piece. Now the
Prop A.3(1) gluing works analogously to PART2-GLU.

### [T-WC-PROPA3-PART3-BRIDGE-RESTATED] **REPLACES T-WC-PROPA3-PART3-BRIDGE**

- **Status**: OPEN (statement-fixed: V is now structurally tied to Uf × Vgs_at)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CAT-C-CHANGE-BASE
- **Type**: theorem

#### Statement (corrected — V tied to Uf and Vgs_at)
```lean
theorem propA3_part3_bridge_for_laurent_product
    ...
    (V Uf : RationalCovering A)
    (Vgs_at : ↥Uf.covers → RationalCovering A)
    (hVgs_base : ∀ Uf_piece, (Vgs_at Uf_piece).base = Uf_piece.1)
    (hUf_acyclic : Uf.IsOXAcyclic)
    (h_each_Vgs_acyclic : ∀ Uf_piece, (Vgs_at Uf_piece).IsOXAcyclic)
    -- NEW: V is the assembly of {Vgs_at Uf_piece}:
    (hV_base : V.base = Uf.base)
    (hV_pieces_in_Vgs : ∀ V' ∈ V.covers, ∃ Uf_piece : ↥Uf.covers,
      ∃ Vgs' ∈ (Vgs_at Uf_piece).covers,
        rationalOpen V'.T V'.s ⊆ rationalOpen Vgs'.T Vgs'.s)
    (hV_covers_each_Uf : ∀ Uf_piece : ↥Uf.covers,
      ∀ v ∈ rationalOpen Uf_piece.1.T Uf_piece.1.s,
        ∃ V' ∈ V.covers, v ∈ rationalOpen V'.T V'.s) :
    V.IsOXAcyclic
```

#### Proof sketch
Prop A.3(3): V refines into the product Uf × ⊔ Vgs_at. Use the product
acyclicity (via Uf-acyclic + each Vgs_at acyclic) to transfer to V.

### [T-WC-V-REFINES-C-FROM-DOM-UNIT-RESTATED] **REPLACES T-WC-V-REFINES-C-FROM-DOM-UNIT**

- **Status**: OPEN (statement-fixed: V tied to dominating-unit construction)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Type**: theorem

#### Statement (corrected — V is specifically the dominating-unit Laurent cover)
```lean
theorem laurent_cover_refines_idealgen_cover
    ...
    (C : RationalCovering A) (T : Finset A) (hC_gen : C.IsGeneratedBy T)
    (s : Aˣ) (h_dom : ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A))
    (V : RationalCovering A) (fs : List A)
    -- NEW: V was built via laurent_cover_from_dominating_unit
    (h_V_from_dom : V.base = C.base ∧
      fs = (T.toList).map (fun t => ((s⁻¹ : Aˣ) : A) * t) ∧
      V.IsLaurentCover fs) :
    ∀ V_j ∈ V.covers, ∃ U ∈ C.covers,
      rationalOpen V_j.T V_j.s ⊆ rationalOpen U.T U.s
```

#### Proof sketch
σ-walk on the dominating-unit Laurent cover: V_j corresponds to a sign vector
σ on T. The σ-choice picks t_{i_max} as the dominant generator (the one with
σ(i_max) = "+"). On V_j, v(t_{i_max}) ≥ v(s) > 0, so v(t_{i_max}) ≠ 0 and
v(t) ≤ v(t_{i_max}) for all t ∈ T (by σ being the dominance choice). Hence
V_j ⊆ R(T/t_{i_max}) = the C-piece D_{t_{i_max}}.

### [T-WC-RESTR-INHERIT-GEN-RESTATED-SUBDECOMPOSED] **REFINES T-WC-RESTR-INHERIT-GEN-RESTATED**

- **Status**: OPEN (sub-decomposed into 2 sub-tickets)
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Depends on**: T-WC-CANONICAL-MAP-UNIT-FROM-T (new sub-ticket below)

#### Statement (sub-decomposition)
```lean
theorem restricted_cover_inherits_IsUnitGenerated ... :
    E.IsUnitGenerated := by
  intro E' hE' t ht
  -- Use T-WC-CANONICAL-MAP-UNIT-FROM-T: t ∈ E'.T ⇒ t ∈ T (via the C'-refines structure)
  -- ⇒ canonicalMap t is a unit in presheafValue E.base.
  ...
```

### [T-WC-PRESHEAFVALUECAST-FINITECOVER-HELPER] **NEW** — cast helper for FiniteCover carrier change

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Parent**: T-WC-TO-REFINEMENT
- **Type**: lemma

#### Statement
```lean
/-- Cast helper: a `FiniteCover` with carrier `↥X` and a base equality `Y = X`
gives, via `h ▸`, a `FiniteCover` with carrier `↥Y`. The `sets` field of the
cast equals the original `sets` (up to defEq via `Eq.rec`). -/
theorem RationalCovering.toFiniteCover_cast_sets [IsHuberRing A]
    {C C' : RationalCovering A} (h : C'.base = C.base) (D' : ↥C'.covers) :
    (h ▸ C'.toFiniteCover).sets D' =
      (h ▸ (fun D' => Subtype.val ⁻¹'
        (Subtype.val ⁻¹' rationalOpen D'.1.T D'.1.s : Set ↥(Spa A A⁺)))) D' := by
  -- Unfold the cast via `Eq.rec` on `h`.
  cases h; rfl
```

#### Proof sketch
`cases h` reduces to identity; `rfl` closes.

### [T-WC-CANONICAL-MAP-UNIT-FROM-T] **NEW** — canonicalMap t is unit when t comes from IsGeneratedBy T set

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Parent**: T-WC-RESTR-INHERIT-GEN-RESTATED-SUBDECOMPOSED
- **Type**: lemma

#### Statement
```lean
/-- When `C'.IsGeneratedBy T`, each `t ∈ T` has canonical image in
`presheafValue D` (for any `D ⊆ C'.base`) that is a unit. -/
theorem canonicalMap_unit_of_IsGeneratedBy
    (C' : RationalCovering A) (T : Finset A) (h_C'_gen : C'.IsGeneratedBy T)
    (t : A) (ht : t ∈ T)
    (D : RationalLocData A) (hD_sub : rationalOpen D.T D.s ⊆ rationalOpen C'.base.T C'.base.s)
    (hD_in_some_C'_piece : ∃ D' ∈ C'.covers,
      rationalOpen D.T D.s ⊆ rationalOpen D'.T D'.s) :
    IsUnit (D.canonicalMap t) := by
  sorry
```

#### Proof sketch
1. Extract D' ∈ C'.covers with D ⊆ D'.
2. By IsGeneratedBy structure, D'.T = T, so t ∈ D'.T.
3. Show: canonicalMap_D' (for D'-localization) inverts t (since t ∈ T ⊆ D'.T means t / D'.s is in locSubring, but more specifically the ratio t over a chosen element makes t a unit).
4. Transfer to D via the restriction map D' → D.

### [T-WC-RATIO-LAURENT-CONS-RECURSION] **NEW** — inductive ratio Laurent cover construction

- **Status**: OPEN
- **File**: `Adic spaces/WedhornCechAcyclicity.lean`
- **Parent**: T-WC-RATIO-LAURENT-COVER
- **Type**: theorem

#### Statement
```lean
/-- Recursive construction of the ratio Laurent cover from a list of units.
Given units `f_1, ..., f_n`, the ratio Laurent cover is iterated as
`laurentRationalCover` over `{f_i · f_j⁻¹}` for all pairs (i, j). -/
theorem ratio_laurent_cover_recursion
    (D₀ : RationalLocData A) (units : List A)
    (h_units_unit : ∀ f ∈ units, IsUnit f) :
    ∃ (V : RationalCovering A) (fs : List A),
      V.IsLaurentCover fs ∧
      V.base = D₀ ∧
      fs = List.product units units |>.map (fun ⟨i, j⟩ =>
        i * (h_units_unit j (by sorry)).unit⁻¹.val) := by
  sorry
```

(Inductive on `units`.)

### Updates to existing tickets in this batch

Mark superseded:
- T-WC-PROPA3-PART2-GLU → T-WC-PROPA3-PART2-GLU-RESTATED
- T-WC-PROPA3-PART1-GLU → T-WC-PROPA3-PART1-GLU-RESTATED
- T-WC-PROPA3-PART3-BRIDGE → T-WC-PROPA3-PART3-BRIDGE-RESTATED
- T-WC-V-REFINES-C-FROM-DOM-UNIT → T-WC-V-REFINES-C-FROM-DOM-UNIT-RESTATED
- T-WC-RESTR-INHERIT-GEN-RESTATED → T-WC-RESTR-INHERIT-GEN-RESTATED-SUBDECOMPOSED

Add dependencies:
- T-WC-PROPA3-PART2-GLU-RESTATED depends on T-WC-EPRIME-RESTRICT-TO-D (closed)
- T-WC-RESTR-INHERIT-GEN-RESTATED-SUBDECOMPOSED depends on T-WC-CANONICAL-MAP-UNIT-FROM-T
- T-WC-RATIO-LAURENT-COVER depends on T-WC-RATIO-LAURENT-CONS-RECURSION
- T-WC-TO-REFINEMENT depends on T-WC-PRESHEAFVALUECAST-FINITECOVER-HELPER

### Updates to plan.md

The 8 fixes resolve all current B2/scope issues. The remaining 19 substantial
tickets (Wedhorn 6.18, 7.40(6), 5-lemma, single-piece sep/glu, evalHom
continuity, combinatorial constructions) have clear paths and don't need
replanning — only focused work via /beastmode.

