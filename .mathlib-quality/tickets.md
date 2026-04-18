# Ticket Board — `tateAcyclicity` Completion

**Last refreshed**: 2026-04-18 (post-worker-integration, grounded in
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
| **Lemma 8.34** / **Hübner 3.8** | geometric reduction to arbitrary rational covers | ⏳ T-GEOM-RED: refinement theorem ✅, induction pending |
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

#### S-GEOM-ASM: Part 2 final assembly

- **Target**: close `LaurentRefinement.lean:3737` via:
  - `RationalCovering.refines_by_standard_cover` to produce standard cover
    refinement.
  - S-GEOM-BASE + S-GEOM-IND to produce hV_glue.
  - S-GEOM-TAU to construct τ.
  - `tateAcyclicity_gluing_via_refinement_cover_level` with cover-level
    hE_sep (from T-IDEAL-2 applied locally).
- **Dependency on T-NULL-7** (adic Nullstellensatz — previously thought
  needed): `refines_by_standard_cover` takes `hZavyalov` as a
  hypothesis. **Bypass options**:
  1. Direct Laurent recursion (no standard-cover reduction — requires a
     different formulation of the induction).
  2. Port a minimal version of Prop 7.14 that gives `hZavyalov`
     unconditionally (this IS T-NULL-7).
  3. Use Hübner Lemma 3.8's packaging (still requires refinement
     geometry, but possibly simpler inputs).
- **Preliminary assessment**: option (1) looks most tractable if we
  directly iterate Laurent splits rather than go through a global
  standard cover. Wedhorn 8.34's proof may in fact be doing option
  (1) implicitly.
- **Estimated lines**: 50 + (possibly 100-200 more for the hZavyalov
  bypass).

**Total T-GEOM-RED remaining**: 270-550 lines (depending on hZavyalov
strategy).

### [T-ACYC-PART2] Final Part 2 assembly

- **Target**: close `LaurentRefinement.lean:3737`.
- **Depends on**: T-OV-1 + T-OVERLAP-COMPAT + T-GEOM-RED + T-IDEAL-2.
- **Estimated lines**: 50 (composition).

---

## 4. Retired tickets

### [T-INJ-1] `restrictionMapHom_injective` — RETIRED (2026-04-18)

Reviewer counterexample proves the unconditional form false. The Route A
NZD scaffolds in `PresheafTateStructure.lean` have been removed (2026-04-18).
Sorry at `:1322` stays. Part 1 routes through cover-level Cor 8.32.

### [T-NULL-7] Full Wedhorn Prop 7.14 — REDUCED TO S-GEOM-ASM bypass

Full adic Nullstellensatz not needed. Minimal input for S-GEOM-ASM is
a direct Laurent-recursion bypass (option 1 above) OR a narrow-scope
`hZavyalov` discharge specific to the induction context.

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
