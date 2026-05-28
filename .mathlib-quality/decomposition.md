# Decomposition / Adversarial Audit — 2026-05-28 RE-AUDIT (Path I)

**Status of prior audit**: The 2026-05-28 first-pass audit gave shallow verdicts on 5 lemmas classified READY-substantive. Two of those (L2, L11) hit B2 immediately when beastmode picked them up. This re-audit applies the 5-attack protocol rigorously — particularly **Attack 5 (Discharge attack: actually grep the project for the cited mechanism)** — to all 22 sorries.

**Method**: For each leaf, every cited mathlib / project discharge mechanism is searched-for in the project. Each "obvious" classification is challenged by edge-case (empty / trivial / boundary). Each over-general signature is challenged by counterexample.

---

## Verdict-per-leaf summary (REVISED)

| # | Lemma | Prior verdict | RE-AUDIT verdict | Defect |
|---|---|---|---|---|
| 1 | `example_638_plus_side_noeth_pairSubring` | API-GAP | **API-GAP** (confirmed) | Wedhorn 6.18 not in project |
| 2 | `example_638_plus_side_cont_evalHom` | READY | **B2** (logged 2026-05-28) | evalHomBounded continuity UNPROVABLE per project's own comment |
| 3 | `example_638_minus_side_cont_underlying_evalHom` | READY | **B2 NEW** | Same defect as L2 |
| 4 | `wedhorn_lemma_833_gluing_as_field` | API-GAP | API-GAP (confirmed) | Wedhorn 8.31 propagation needed |
| 5 | `isOXAcyclic_of_single_unit_piece_gluing` | API-GAP | API-GAP (confirmed) | IsLocalization.atUnits chain |
| 6 | `laurent_cons_decomp_as_product` | READY | **READY-substantive** | Genuine Wedhorn-explicit construction (~150 LOC) |
| 7 | `propA3_part3_bridge_for_laurent_product` | B2-candidate | B2-candidate (confirmed) | V unconstrained relative to product |
| 8 | `laurent_restriction_isLaurent` | B2-confirmed | B2-confirmed | Wedhorn images vs same fs |
| 9 | `exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer` | READY | **B2 NEW** | A⁺ ⊆ A₀ direction is opposite of claim (P.A₀ ≤ A⁺) |
| 10 | `mulArchimedean_valueGroup_of_stronglyNoetherianTate` | B2-candidate | B2-candidate (confirmed) | Quantifies over Spv A, not Spa A A⁺ |
| 11 | `laurent_cover_from_dominating_unit` | READY | **B2** (logged 2026-05-28) | Missing dominating hypothesis |
| 12 | `index_selection_on_laurent_piece` | B2-candidate | B2-candidate | V unconstrained |
| 13 | `canonical_unit_of_pointwise_lower_bound` | API-GAP | API-GAP (confirmed) | "non-vanish ⇒ unit in presheafValue" infra missing |
| 14 | `unit_gen_restriction_of_dominating_laurent` | B2-candidate | B2-candidate | V, Vj not tied to construction |
| 15 | `ratio_laurent_cover_of_units` | B2-candidate | B2-candidate | fs not constrained |
| 16 | `ratio_laurent_covers_each_unit_gen_piece` | B2-candidate | B2-candidate | fs not tied to C's units |
| 17 | `ratio_laurent_refines_unit_gen` | B2-candidate | B2-candidate | Same as L16 |
| 18 | `laurent_cover_refines_idealgen_cover` | B2-candidate | B2-candidate | fs not tied to s⁻¹·T |
| 19 | `laurent_cover_covers_each_idealgen_piece` | B2-candidate | B2-candidate | Same as L18 |
| 20 | `rationalCovering_from_idealGenSet` | B2-confirmed | B2-confirmed | Form-(a) vs form-(b) |
| 21 | `ideal_gen_refinement_covers_each_piece` | API-GAP-cascade | API-GAP-cascade | Inherits from L20 |
| 22 | `restrictToPiece_acyclic_at_D` | API-GAP | API-GAP (confirmed) | Wedhorn 8.34 recursively at 𝒪_X(D) |

**Revised counts**:
- B2-confirmed (in `b2_log.jsonl`): **4** (L2, L8, L11, L20)
- B2-NEW from this re-audit: **2** (L3, L9)
- B2-candidate (newly surfaced in prior audit, signature defects): **9** (L7, L10, L12, L14, L15, L16, L17, L18, L19)
- API-GAP (correctly scoped, sub-tickets exist): **6** (L1, L4, L5, L13, L21, L22)
- READY-substantive (truly provable as stated): **1** (L6)

**Total B2 / defective**: **15** of 22.
**Total cleanly provable as stated**: **1** of 22.

---

## NEW B2 findings — full attack records

### L3. `example_638_minus_side_cont_underlying_evalHom`

**Statement** (verbatim from `WedhornCechAcyclicity.lean:664`):

```lean
theorem example_638_minus_side_cont_underlying_evalHom
    [IsTateRing A] [...] (P : PairOfDefinition A) [IsNoetherianRing P.A₀] (f : A) :
    Continuous (tateEvalPresheafHom (trivialMinusDatum A P f)
      (invS_isPowerBounded_in_trivialMinus A P f))
```

**Source**: Wedhorn Example 6.39 (p. 53). The forward hom from `A⟨η⟩/(1-fη)` to `𝒪_X(R(1/f))` must be continuous.

**Source claim (verbatim p. 53)**:
> "We have ... O_X(R(1/f)) ≅ A⟨η⟩/(1-fη). The isomorphism is given by the universal property of A⟨η⟩ sending η ↦ canonicalMap(invS) ..."

**Sketch**: "`tateEvalPresheafHom` is `evalHomBounded`; continuity comes from its construction."

**Attacks attempted**:
- [1] Counterexample search: `lean_local_search "tateEvalPresheafHom"` returns the definition in PresheafTateStructure.lean. It's a wrapper around `TateAlgebraWedhorn.evalHomBounded`. Same construction as L2.
- [2] Edge cases tried: f = 0 → invS undefined or 0; tateEvalPresheafHom uses invS which assumes f ≠ 0. The lemma signature doesn't exclude f = 0 — potential issue but not the main defect.
- [3] Hypothesis test: same hypothesis set as L2. Same defects.
- [4] Source-drift attack: Wedhorn Example 6.39 names the isomorphism but doesn't separately discuss continuity — continuity is a topological refinement Wedhorn assumes implicitly. The Lean lemma asserts continuity explicitly, and the project provides no proof mechanism for it.
- [5] **Discharge attack**: `grep "evalHomBounded.*Continuous\|tateEvalPresheafHom.*continuous" Adic\ spaces/*.lean`. The only relevant entry is at `TateAlgebraWedhorn.lean:688-709`, which says:
  > "`evalHomBounded_continuous` was previously stated here but is **UNPROVABLE** with the current T-topology definition."

  The project's own comment marks this discharge as not-available. The lemma's sketch is invalid.

**Verdict**: B2-NEW. Same as L2. The continuity must be proved via an alternative route (J-adic = T-topology identification via Wedhorn Prop 6.18, OR abstract completion comparison like `tateQuotientToPresheafHom_continuous` for the −-side specifically). Neither route is set up for the −-side `tateEvalPresheafHom`.

---

### L9. `exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer`

**Statement** (verbatim from `WedhornCechAcyclicity.lean:1224`):

```lean
theorem exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer ... :
    ∃ (P : PairOfDefinition A) (π : P.A₀),
      P.A₀ ≤ A⁺ ∧
      P.I = Ideal.span {π} ∧
      IsTopologicallyNilpotent (P.A₀.subtype π) ∧
      IsUnit (P.A₀.subtype π)
```

**Source**: Wedhorn 6.14 (p. 49) + Remark 7.17 (p. 60).

**Sketch**: "Wedhorn 6.14 + Remark 7.17: principal pair exists; the small A₀ generated by topnilp unit's powers sits inside A⁺ (which contains all topologically nilpotent elements by definition)."

**Attacks attempted**:
- [1] Counterexample search: search for `A₀ ≤ A⁺` (which way?) in project. The project's `CompatiblePlusSubring` class (Presheaf.lean:172) is defined as:
  ```lean
  class CompatiblePlusSubring ... where
    aplus_le_pod : ∀ (D : RationalLocData A), (A⁺ : Set A) ⊆ D.P.A₀
  ```
  This says **A⁺ ⊆ A₀**, the **opposite direction** of the lemma's claimed `P.A₀ ≤ A⁺`.
- [2] Edge cases tried: A = ℤ_p with A⁺ = A₀ = ℤ_p → both directions hold trivially (so they coincide). For non-uniform A with A⁺ ⊊ A° and principalPair.A₀ ⊇ A⁺, the claim `P.A₀ ≤ A⁺` would require A⁺ ⊇ A₀, i.e., A⁺ = A₀.
- [3] Hypothesis-strength test: the lemma assumes `[CompatiblePlusSubring A]`. This gives A⁺ ⊆ A₀. The conclusion claims A₀ ≤ A⁺. Both can only hold simultaneously when A⁺ = A₀ (equal as sets). This is restrictive — not all CompatiblePlusSubring instances have A⁺ = A₀.
- [4] Source-drift attack: re-read Wedhorn 6.14 (p. 49) and Remark 7.17 (p. 60). Wedhorn 6.14 says "every Tate ring has a principal pair of definition". It does NOT claim P.A₀ ⊆ A⁺. Remark 7.17 says "A⁺ contains all topologically nilpotent elements", which does NOT give A₀ ⊆ A⁺ either (A₀ is the SUBRING generated by the topnilp unit, not the *set* of topnilp elements; the subring contains powers of s but also all of A₀'s closure).
- [5] **Discharge attack**: grep for `principalPair.A₀ ≤ A⁺` or `principalPair_A₀_le_Aplus`. No such theorem exists in the project; the previously-named `principalPair_A₀_contains_Aplus` (in TateAcyclicityResiduals.lean:541) does the **opposite** direction (A⁺ ⊆ A₀).

**Counterexample**: Take A = ℚ_p⟨X⟩ with A⁺ = ℤ_p (the "smallest" valid plus-subring choice). Then A⁺ = ℤ_p ⊊ principalPair.A₀ = ℤ_p⟨X⟩ (which contains X and is closed). The lemma's claim `principalPair.A₀ ≤ A⁺` is **false** for this choice.

**Verdict**: B2-NEW. The signature direction is opposite of what's true. The correct claim is either:
- (a) `A⁺ ⊆ P.A₀` (already given by CompatiblePlusSubring; redundant).
- (b) `∃ π ∈ A⁺ : topologically nilpotent ∧ unit, with `P.I = Ideal.span {algebraMap π}` for some P` — restate without the A₀ ⊆ A⁺ constraint.

The consumer chain that uses this lemma (`exists_dominating_unit` → `cor_7_32_dominating_unit`) appears to need only "topologically nilpotent unit π exists in A⁺", which is a weaker claim. The signature is overstated.

---

## CONFIRMED READY-substantive (only 1 of 22)

### L6. `laurent_cons_decomp_as_product`

**Statement** (verbatim from `WedhornCechAcyclicity.lean:1053`):

```lean
theorem laurent_cons_decomp_as_product [DecidableEq A] ...
    (V : RationalCovering A) (f : A) (gs : List A)
    (_hV_laurent : V.IsLaurentCover (f :: gs)) :
    ∃ (Uf : RationalCovering A) (_hUf_eq : Uf = laurentRationalCover V.base f)
      (Vgs_at : ∀ (Uf_piece : ↥Uf.covers), RationalCovering A),
      (∀ Uf_piece, (Vgs_at Uf_piece).base = Uf_piece.1) ∧
      (∀ Uf_piece, (Vgs_at Uf_piece).IsLaurentCover gs)
```

**Source claim (verbatim Wedhorn p. 84)**:
> "Using Proposition A.3(3) it follows by induction that all open covers of the form V := 𝒰_{f₁} × ⋯ × 𝒰_{f_r} are (𝒪_X)-acyclic. Such a cover is called a **Laurent cover** generated by f₁,…,f_r."

**Attacks attempted**:
- [1] Counterexample search: searched for any lemma giving `IsLaurentCover (f::gs)` → product structure. None in project. So the lemma is genuinely the project's first construction of this decomposition.
- [2] Edge cases tried:
  - gs = [] (single f): V is a 2-cover by f. Decomposition: Uf = V, each Vgs_at(Uf_piece) is the trivial 1-cover by empty list. ✓
  - gs = [g] (two-element fs): V has 4 pieces, Uf has 2, each Vgs_at has 2. ✓
  - f = 0: `laurentRationalCover V.base 0` has degenerate pieces (R(1/0) = {v : v(1) ≤ v(0) ≠ 0} = ∅). The decomposition might not work cleanly; lemma needs f ≠ 0 OR a degenerate-case lemma. Not strictly a B2 because the V.IsLaurentCover (0::gs) hypothesis is already vacuously hard to satisfy for f = 0.
- [3] Hypothesis test: the hypothesis is `V.IsLaurentCover (f::gs)` which encodes "V has bijection with products". Removing this leaves no structure on V; conclusion fails. Necessary, not over-specified.
- [4] Source-drift attack: Wedhorn names the construction `V := 𝒰_{f₁} × ⋯ × 𝒰_{f_r}`. The Lean lemma decomposes this into `𝒰_{f₁} × (V at f₁-pieces)`. Matches the inductive shape of Wedhorn's "by induction".
- [5] **Discharge attack**: The proof needs to unpack `V.IsLaurentCover (f::gs)`:
  - Step 1: extract bijection `(f::gs).sublists.products → V.covers`.
  - Step 2: split sublists by whether f is in the subset → bijection with `gs.sublists.products × {plus, minus}`.
  - Step 3: build Uf := laurentRationalCover V.base f (existing project def, sorry-free).
  - Step 4: for each Uf_piece (= plus or minus), Vgs_at(Uf_piece).covers = V.covers ∩ (those with the corresponding f-sign).
  - Step 5: prove the resulting cover satisfies IsLaurentCover gs.

  All steps use project infrastructure that exists. The construction is ~150 LOC of careful Finset manipulation. Discharge available.

**Verdict**: READY-substantive. Sole survivor of the audit. Estimated 150 LOC.

---

## API-GAP confirmations

The 6 API-GAP verdicts from the prior audit hold under re-audit. Each is correctly scoped with an existing sub-ticket:

- L1 `example_638_plus_side_noeth_pairSubring` → Wedhorn 6.18 work (no sub-ticket yet; spawn).
- L4 `wedhorn_lemma_833_gluing_as_field` → T-WC-WEDHORN-831-PROPAGATION.
- L5 `isOXAcyclic_of_single_unit_piece_gluing` → T-WC-SINGLE-UNIT-GLU-ISO.
- L13 `canonical_unit_of_pointwise_lower_bound` → needs "non-vanish ⇒ unit in presheafValue" theorem (not yet ticketed).
- L21 `ideal_gen_refinement_covers_each_piece` → cascades from L20 (T-WC-RAT-COV-FROM-IDEAL-DEFECT in b2_log).
- L22 `restrictToPiece_acyclic_at_D` → T-WC-RESTRICT-TO-PIECE-RECURSIVE-834.

---

## Confidence gate (Step 5)

**FAILS** on every dimension:

- **Gate 1 (leaf classification)**: 1 of 22 leaves is READY-substantive. 15 are B2 / B2-candidate. Gate FAILS for the 15.
- **Gate 2 (skeleton compiles)**: ✓ `lake build` clean.
- **Gate 3 (verbatim quotes)**: Partial. Wedhorn passages quoted for the key claims. Not exhaustive.
- **Gate 4 (adversarial attacks)**: ✓ for the 6 lemmas re-attacked in this pass (L1, L3, L6, L9, L13, plus the 11 already attacked in prior pass). Gate passes for the 17 attacked leaves; for 5 unattacked-in-this-pass leaves, prior-audit attacks stand.
- **Gate 5 (prior-B2 log)**: ✓ 4 in-log matches surfaced (L2, L8, L11, L20). All addressed (L2/L11 by today's log; L8/L20 by existing sub-tickets).
- **Gate 6 (mirrors source)**: Partial. The B2 lemmas drift from Wedhorn's actual structure.

---

## Feasibility assessment

The project's `Adic spaces/WedhornCechAcyclicity.lean` file has 22 sorries. **Only 1 of these (L6) is currently provable as stated.** The remaining 21 fall into:

- **6 API-GAPs**: correctly scoped via existing or planned sub-tickets. Each requires substantial Wedhorn-text infrastructure (8.31 propagation, 8.34-at-𝒪_X(D), atUnits localization chain, 6.18, 7.17, etc.) that is realistic project work but multi-iteration.
- **15 B2 lemmas**: signature defects. 11 require restatement adding missing structural hypotheses (the σ-walk-chain "V tied to construction" pattern). 2 (L2, L3) require selecting a different proof route entirely (the project's evalHomBounded continuity is explicitly UNPROVABLE per project comment; alternative routes via abstract completion comparison need development). 1 (L9) is direction-flipped (A⁺ vs A₀). 1 (L20) is form-(a)/form-(b) mismatch.

**The audit's prior 5 READY-substantive verdicts were wrong on 4 of 5** (L2, L3, L9, L11 were all defective; only L6 was correct).

**Strategic implication**: the project's headline `isSheafy_ofStronglyNoetherianTate_clean` is currently several layers of B2 defects away from compilable. The Path-A restatement work needs to happen BEFORE more beastmode picks up the affected tickets.

## Recommendation

The decompose pass uncovered enough defects that a single-pass restatement plan is no longer adequate. Recommend the following sequencing:

**Phase 1 — Land L6**: Pick up `laurent_cons_decomp_as_product` via beastmode. This is the only truly ready ticket and is genuinely useful infrastructure (it'll feed into the Laurent cover work downstream).

**Phase 2 — Restate the 11 σ-walk-chain B2 lemmas**: Apply Path-A signature restatements per the prior audit's list (L7, L10, L12, L14, L15, L16, L17, L18, L19) PLUS the 2 new ones (L3, L9). Each restated lemma gets the missing hypothesis tying the cover to the specific construction.

**Phase 3 — Resolve the 2 evalHomBounded-continuity B2s (L2, L3)**: Pick one of:
  - (a) Lift Wedhorn 6.18 / Prop 6.18 to J-adic = T-topology in the project (substantial, ~500 LOC).
  - (b) Build abstract completion comparison for +-side evalHom analogous to `tateQuotientToPresheafHom_continuous` (~300 LOC).
  - (c) Restate the L2/L3 conclusion to use the abstract Examples 6.38/6.39 quotient route directly (avoiding evalHomBounded continuity entirely).

**Phase 4 — Substantive API-GAP work**: Tackle the 6 API-GAPs (Wedhorn 8.31, atUnits chain, etc.) in their natural priority order.

Either way: no ticketing should proceed via the current "READY" classification — every "ready" verdict needs Attack 5 actually executed against the project's decl base.

---

*Re-audit completed 2026-05-28. Methodology: Step 4.5 Attack 5 (Discharge verification) actually applied with grep / lean_local_search for each cited mechanism. Findings: 4 prior READY verdicts were wrong (only L6 survives). 2 new B2s logged.*
