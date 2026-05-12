# Ticket Board — `tateAcyclicity` Completion

**Last refreshed**: 2026-05-11 (session 2 reviewer correction — MAJOR REFRAME of
the Wedhorn Prop 8.15 blocker).

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
                    ├── S-IDEAL-JAC: locIdeal ≤ Jacobson(⊥) in locSubring ⏳ ~30-50 lines
                    ├── S-IDEAL-LOC: ideal q ⊆ A_s has q = (q∩𝔇)·A_s    ⏳ ~80-150 lines
                    │     and closedness transfers
                    └── S-IDEAL-ASM: end-to-end assembly                 ⏳ ~30 lines

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
  │     ├── S-GEOM-TAU: τ construction + containment           ⏳ ~30 lines
  │     │     (blocked on minor DecidableEq bridge in LaurentRefinement)
  │     ├── S-GEOM-BASE: hV_glue for |S.elts| = 1              ⏳ ~60 lines
  │     ├── S-GEOM-IND: hV_glue induction on |S.elts|          ⏳ ~200 lines
  │     │     (Wedhorn 8.34 induction, Laurent split at f₀)
  │     └── S-GEOM-ASM: Part 2 assembly (may include hZavyalov
  │                      bypass per Hübner 3.8)                 ⏳ ~50 lines
  │
  └── Local cover-level injectivity per piece E ∈ C.covers
        └── (same coeRingHom_preserves_proper as Part 1)
```

---

## 3. Open tickets — detailed plans

### [T-OV-1] Bivariate Example 6.38 — IN PROGRESS

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

**Target**: `LaurentRefinement.lean:3173`.

**Plan**: instantiate `example638Bivariate_equiv` at
`B := presheafValue D₀, b := D₀.canonicalMap f`; verify both
`LaurentOverlapBridgeCompatible` intertwining identities using the
`_mk`, `_algebraMap`, `_X`, `_Y` action lemmas already landed in
`LaurentOverlap.lean`, plus `presheafValue_iteratedMinus_equiv_apply`
and similar reductions on the plus/minus bridge sides.

**Estimated lines**: ~80. **Blocked on T-OV-1 Step A**.

### [T-IDEAL-2] Closedness of proper ideals — SUBSTANTIAL PROGRESS

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
- **Status**: OPEN, immediately actionable.

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

- **Target**: `RationalCovering.standardCoverVTau` (construct via
  `Classical.choose` on `hS_contain`) + `standardCoverVTau_subset`.
- **Current blocker**: Lean 4 `DecidableEq` instance diamond between
  `Classical.propDecidable` (used implicitly by `noncomputable def
  laurentPlusDatum`) and explicit `[DecidableEq A]`. `rfl` fails on
  `(laurentPlusDatum D₀ f).T = insert f D₀.T` even though values agree.
- **Fix path**: add `@[simp] laurentPlusDatum_T_eq` in
  `LaurentRefinement.lean` proved via `Finset.ext` on membership
  (bypasses diamond; see reviewer note below).
- **Reviewer's alternative**: state τ's subset claim at the
  `rationalOpen` (Set Spv A) level rather than Finset level, since
  valuation membership doesn't depend on `Finset.instInsert`.
- **Estimated lines**: ~30 (once projection helper lands).

#### S-GEOM-BASE: base case `|S.elts| = 1`

- **Target**: when `S.elts = {f}` with `Ideal.span {f} = ⊤` (so
  `f ∈ Aˣ`), build `hV_glue` for the singleton V-cover `{C.plusDatum f}`.
- **Mathematical content**: the unique plus-piece
  `rationalOpen (insert f C.base.T) C.base.s` equals
  `rationalOpen C.base.T C.base.s` as a set (when `f` is a unit + the
  usual normalization `1 ∈ C.base.T` makes `v(s) ≥ 1 ≥ v(f)` tractable).
  Gluing becomes trivial: the compatible family has one element which
  IS the global section.
- **Care needed**: the set equality isn't literally immediate; may need
  a lemma "insert of a unit doesn't restrict rational open" or similar.
- **Estimated lines**: 40-60.

#### S-GEOM-IND: inductive step

- **Target**: given `hV_glue` for standard covers of size `n`, derive
  for size `n+1`.
- **Strategy** (Wedhorn 8.34 / Hübner 3.7):
  1. Given `S.elts` with `n+1` elements, pick `f₀ ∈ S.elts`. The
     remaining `S.elts \ {f₀}` has `n` elements but may not span ⊤ in `A`.
     However, in `A[f₀⁻¹]` (Laurent-minus at f₀) and
     `A[unit·f₀-boundable]` (Laurent-plus at f₀), the remaining
     elements DO span appropriately (since `f₀` inverted).
  2. Laurent-split `rationalOpen C.base.T C.base.s` at `f₀` into
     `rationalOpen_plus(f₀)` and `rationalOpen_minus(f₀)`.
  3. Each half is a rational covering `C_±` of a sub-base, refined by
     `S.elts \ {f₀}` (adjusted).
  4. Apply the induction hypothesis on each half.
  5. Apply `laurentCover_gluing_presheaf` (sorry-free modulo T-OV-1) at
     `f₀` to combine the two half-sections into a global section on
     `C.base`.
- **Complications**:
  - Sub-cover adjustment (step 3) requires the standard-cover span-top
    property to be preserved under restriction — subtle but handleable.
  - Compatibility transfer across the Laurent split — mechanical but
    fiddly.
- **Estimated lines**: 150-250.

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

- **Status**: OPEN (added 2026-05-11 post-reviewer pivot for Lane A)
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

- **Status**: OPEN (added 2026-05-11)
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

- **Status**: OPEN (added 2026-05-11 — major hidden risk newly
  surfaced by reviewer)
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

- **Status**: OPEN (added 2026-05-11)
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

- **Status**: OPEN (added 2026-05-11)
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

- **Status**: OPEN (added 2026-05-11; housekeeping)
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

- **Status**: OPEN (housekeeping)
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

- **Status**: OPEN (HIGH PRIORITY — critical path)
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

- **Status**: OPEN (HIGH PRIORITY — critical path)
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

- **Status**: OPEN (HIGH PRIORITY — critical path; supersedes T-FLAT-PER-E)
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

- **Status**: OPEN (HIGH PRIORITY)
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

- **Status**: PARTLY DONE — `flat_quotient_oneSubfX_general` already
  proves the underlying quotient flatness. Remaining work: expose this
  as a `B → B⟨X⟩/(1-fX)` flatness packaged at the rational-localization
  level, matching the API of T-RATIONAL-FLAT-BASIC-PLUS.
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For any strongly noetherian Tate ring `B`
  and any `f : B`, `B⟨X⟩/(1 - fX)` is flat over `B` along the
  canonical inclusion.
- **Why this is partly done**: the underlying flatness of the quotient
  is established. What's needed is the rational-localization-level
  packaging (an analog of T-RATIONAL-FLAT-BASIC-PLUS).
- **Reference**: Wedhorn Prop 8.30 / Lemma 8.30.

### [T-RATIONAL-LOC-TRANSITIVITY] Transitivity of rational localizations

- **Status**: OPEN (HIGH PRIORITY)
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

- **Status**: OPEN (MEDIUM PRIORITY — needed at intermediate B-levels in T-RATIONAL-LOC-TRANSITIVITY)
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

- **Status**: OPEN (LOW PRIORITY housekeeping; reduces final theorem boundary)
- **Added**: 2026-05-11 round 3
- **Mathematical statement**: For a `PairOfDefinition A` with
  `IsNoetherianRing P.A₀` and a finite `T : Finset A`, `s : A`, the
  subring `locSubring P T s` is noetherian.
- **Strategy**: `locSubring` is generated over `P.A₀` by the finite set
  `T/s`. The ring of definition is noetherian by hypothesis. Finite
  generation over a noetherian ring is noetherian (Hilbert basis).
- **Why it matters**: the current theorems
  (`restrictionMap_flat_via_iteratedMinus`, etc.) expose `IsNoetherianRing
  (locSubring …)` as a final hypothesis. With T-LOC-SUBRING-NOETH, this
  becomes a derived instance, simplifying caller hypotheses.
- **Reviewer guidance**: "any exposed `IsNoetherianRing (locSubring ...)`
  should be discharged locally. Since locSubring is finitely generated
  over a noetherian ring of definition, it should follow from
  noetherianity of P.A₀ and finiteness of T."

### [T-FLAT-PLUS-REWORK] Rework `restrictionMap_flat_via_iteratedPlus` without power-boundedness

- **Status**: OPEN (MEDIUM PRIORITY — fix existing wrong-abstraction theorem)
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

- **Status**: OPEN (HIGH PRIORITY for IsSheafy embedding)
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

- **Status**: OPEN (HIGH PRIORITY for IsSheafy embedding)
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

- **Status**: OPEN (HIGH PRIORITY for IsSheafy embedding)
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

- **Status**: OPEN
- **File**: `Adic spaces/RelativeRationalLocData.lean` (new file)
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
- **Proof sketch**: routine construction except for `hopen`. For `hopen`:
  pull D's `hopen` (∃ N, ∀ b ∈ E.P.I^N, divByS b D.s ∈ locSubring) along
  `E.canonicalMap`, using that the image of E.P.I is contained in
  P_at_E.I (the pair-of-definition at E-level), and divByS commutes with
  the algebraMap-image where applicable.
- **Mathlib lemmas needed**: `Finset.image`, `divByS_mem_locSubring`,
  `algebraMap_mem_locSubring` (all existing).
- **Sources**: Wedhorn Lemma 2.13. Templates: `iteratedMinusDatum_B` (line
  476 of LaurentRefinement.lean), `iteratedPlusDatum_B` (line 460).
- **Generality decision**: `(E D : RationalLocData A)` — D arbitrary
  modulo rationalOpen-inclusion. Uses E.P as the base pair-of-definition.
- **Risks**: subtleties in matching B-level ideal-of-definition images.
  Test with `E.canonicalMap D.s`'s topological behaviour.

### [T-WEDHORN-213-FORWARD] Forward hom presheafValue D → presheafValue (relativeRationalLocData ...)

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN
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

- **Status**: OPEN (HIGH PRIORITY, replaces T-WEDHORN-213-DATUM as primary path)
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

- **Status**: OPEN (HIGH PRIORITY)
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

- **Status**: OPEN (THE structural piece)
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

- **Status**: OPEN (closes T-RATIONAL-FLAT-GENERAL)
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

### [T-MATHLIB-STACKS-00MA] Adic completion of Noetherian ring is Noetherian

- **Status**: OPEN (HIGH PRIORITY — blocks T-STRONG-NOETH-PRESERVATION and the whole chain)
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

- **Status**: PARTIALLY OBVIATED (2026-05-12 architectural finding)
- **2026-05-12 update**: The general flatness route via
  `restrictionMap_flat_of_rational_subset_via_relative` (RestrictionFlatness.lean)
  was REFACTORED to NOT require `HasLocLiftPowerBounded (presheafValue E)` as
  a hypothesis (the `hLocLift_B` parameter has been removed, commit bbbdd28).
  The earlier proof had `letI : HasLocLiftPowerBounded (presheafValue E) :=
  hLocLift_B` bringing the instance into scope, but it was never used —
  flatness comes from `presheafValue_flat_of_canonical` which depends on the
  canonical Tate-quotient identification (Example 6.38 at B-level), not the
  Nullstellensatz.
- **Remaining scope**: Only the BASIC LAURENT depth-1 theorems
  (`restrictionMap_flat_via_iteratedMinus`, `_iteratedPlus`,
  `_fSubX_quotient`, `_oneSubfX_quotient`) still take `hLocLift_B`, and they
  thread it through `laurentPlusBridge` / `laurentMinusBridge` in
  LaurentRefinement.lean which has structural dependencies on the
  Nullstellensatz at B-level. Refactoring those would be a separate cleanup.
- **Original mathematical statement**: For strongly noetherian Tate A and
  D : RationalLocData A, `HasLocLiftPowerBounded (presheafValue D)` holds.
- **Proof sketch (still applicable for any future refactor)**: As before —
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
