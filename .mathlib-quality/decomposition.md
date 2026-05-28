# Decomposition / Adversarial Audit — 2026-05-28

## Scope

This audit covers the **22 remaining sorries** in `Adic spaces/WedhornCechAcyclicity.lean`. Goal: surface structural mismatches between ticket hypothesis sets and conclusions before more `/beastmode` runs hit them one-by-one.

**Sources**: Wedhorn 2019 *Adic Spaces* (arXiv:1910.05934), pages 81-86 in particular for §8.3.

**Project infrastructure consulted**:
- `Adic spaces/LaurentCoverExact.lean` — `row3_exact` (algebraic 5-lemma, sorry-free)
- `Adic spaces/LaurentRefinementCore.lean` — Route-B bridges, `laurentCover_gluing_presheaf_viaBridges` (sorry-free)
- `Adic spaces/PresheafTateStructure.lean` — `presheafValue_isTateRing`; *partial* Wedhorn 8.31 (`presheafValue_isNoetherianRing_of_rationalSubset` requires `hD₀_noeth` as hypothesis, not derived)
- `Adic spaces/Presheaf.lean` — Wedhorn 7.40(6) sub-lemma chain with deep sorries at `convexSubgroup_eq_top_of_ne_bot_of_analytic`
- `Adic spaces/StandardCover.lean` — form-(b) `refines_cover`/`refines_contain`
- `Adic spaces/AdicSpectrum.lean` — `noCommonZero_of_idealGen` (form `IsUnit f` from "∀ v, ¬ v.vle f 0")
- `Adic spaces/IteratedRational.lean` — `restrictionMapHom_canonicalMap`

**Prior-B2 log consulted**: 40 entries in `.mathlib-quality/b2_log.jsonl`. Most relevant to this audit:
- Entry 39 — `restricted_cover_inherits_IsUnitGenerated` (RESOLVED by recent refactor)
- Entry 40 — `rationalCovering_from_idealGenSet` (form-(a)/form-(b) mismatch)
- Entries 22, 26, 27 — earlier σ-walk / per-D cover defects with similar shape

---

## Verdict-per-leaf summary

| # | Lemma | Bucket | Verdict | Notes |
|---|---|---|---|---|
| 1 | `example_638_plus_side_noeth_pairSubring` | B4 | **API-GAP** | Wedhorn 6.18; needs the noeth-pair-subring proof |
| 2 | `example_638_plus_side_cont_evalHom` | B4 | **READY-substantive** | Sketch is sound; uses project's `evalHomBounded` |
| 3 | `example_638_minus_side_cont_underlying_evalHom` | B4 | **READY-substantive** | Parallel to (2) |
| 4 | `wedhorn_lemma_833_gluing_as_field` | B4 | **API-GAP** | Needs Wedhorn 8.31 propagation; sub-tickets in place |
| 5 | `isOXAcyclic_of_single_unit_piece_gluing` | B2 | **API-GAP** | Needs `IsLocalization.atUnits` chain; sub-ticket spawned |
| 6 | `laurent_cons_decomp_as_product` | B5 | **READY-substantive** | Structural Laurent-algebra fact |
| 7 | `propA3_part3_bridge_for_laurent_product` | B5 | **B2-CANDIDATE** | Already flagged inline; V unconstrained relative to product |
| 8 | `laurent_restriction_isLaurent` | B5 | **B2-CONFIRMED** | Known: form-(a) `fs` vs Wedhorn's `f_i\|U` images |
| 9 | `exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer` | B4 | **READY-substantive** | Wedhorn 6.14 + Remark 7.17 |
| 10 | `mulArchimedean_valueGroup_of_stronglyNoetherianTate` | B4 | **B2-CANDIDATE** | Quantifies over arbitrary `v : Spv A`, not just continuous |
| 11 | `laurent_cover_from_dominating_unit` | B5 | **READY-substantive** | Constructive build of Laurent from `s⁻¹·T` |
| 12 | `index_selection_on_laurent_piece` | B5 | **B2-CANDIDATE** | V is unconstrained — no Laurent-vs-T/s hypothesis |
| 13 | `canonical_unit_of_pointwise_lower_bound` | B5 | **API-GAP** | True claim, but project lacks "non-vanish ⇒ unit in presheafValue" |
| 14 | `unit_gen_restriction_of_dominating_laurent` | B5 | **B2-CANDIDATE** | V, Vj not tied to the dominating-unit construction |
| 15 | `ratio_laurent_cover_of_units` | B5 | **B2-CANDIDATE** | Output doesn't constrain `fs` relative to `units` |
| 16 | `ratio_laurent_covers_each_unit_gen_piece` | B3 | **B2-CANDIDATE** | V is generic Laurent; `fs` not tied to C's units |
| 17 | `ratio_laurent_refines_unit_gen` | B5 | **B2-CANDIDATE** | Same: V generic; fs not tied to C |
| 18 | `laurent_cover_refines_idealgen_cover` | B3 | **B2-CANDIDATE** | V's `fs` not tied to dominating unit's `s⁻¹·T` |
| 19 | `laurent_cover_covers_each_idealgen_piece` | B3 | **B2-CANDIDATE** | Same as (18) |
| 20 | `rationalCovering_from_idealGenSet` | B4 | **B2-CONFIRMED** | Logged 2026-05-28: form-(a) vs form-(b) |
| 21 | `ideal_gen_refinement_covers_each_piece` | B3 | **API-GAP-cascade** | Inherits the form-(a)/form-(b) defect from (20) |
| 22 | `restrictToPiece_acyclic_at_D` | (new) | **API-GAP** | Needs Wedhorn 8.34 recursively at 𝒪_X(D); sub-ticket spawned |

**Counts**:
- B2-confirmed (already in log): 2
- B2-candidate (newly surfaced this audit): 9
- API-GAP (need infrastructure; honestly scoped): 6
- READY-substantive (provable as stated): 5

---

## The pattern across the 9 NEW B2 candidates

**All 9 share the same structural defect**: the hypothesis set declares "V is a Laurent cover by `fs`" or "Vj ∈ V.covers" without tying `V`/`fs`/`Vj` to the *specific* construction the proof actually uses.

The σ-walk / dominant-element arguments in Wedhorn's proof of Lemma 8.34 (ii)/(iii) require V to be the **specific** Laurent cover built from `s⁻¹·T` (where s is the dominating unit and T is the unit-generating Finset). For arbitrary V satisfying `V.IsLaurentCover fs` with arbitrary `fs`, the σ-walk has nothing to select from — the pieces of V have no relationship to T.

This is the same root cause as the Q1 issues from the prior `/expert-review`: **the project's tickets were written assuming "abstract V" but the proof requires "the specific V constructed from inputs"**. The reviewer's recommendation for `restricted_cover_inherits_IsUnitGenerated` ("specialize to literal `restrictToPiece`") is exactly the fix pattern these 9 also need.

**Concrete fix shape** (per CLAUDE.md (b), permitted because the lemma is unprovable as stated):

Each of these lemmas needs to add explicit hypotheses tying the cover to the construction. Either:

- **(i) Add constructor hypothesis**: `(_hV_is_ratio_cover : V = (ratio_laurent_cover_of_units D₀ units _).choose)` — pins V to be the specific construction.
- **(ii) Add structural hypothesis tying fs**: `(_hfs_eq : fs = (T.toList).map (fun t => ((s⁻¹ : Aˣ) : A) * t))` — pins fs to the dominating-unit form.
- **(iii) Inline the construction**: replace "given V" with "build V from the inputs" and prove the conclusion about the built V directly.

Option (iii) is the cleanest. The cascade-down of (i)/(ii) to consumers is mechanical but adds N hypothesis arguments per lemma chain step.

---

## Per-leaf adversarial attack analyses (all NEW B2 candidates)

### L7. `propA3_part3_bridge_for_laurent_product`

**Statement**: Given a 2-cover `Uf`, a family `Vgs_at : ↥Uf.covers → RationalCovering A` with each `Vgs_at(Uf_piece).base = Uf_piece.1`, plus `Uf` acyclic and each `Vgs_at(Uf_piece)` acyclic, conclude `V.IsOXAcyclic` for any `V`.

**The B2 defect**: The lemma takes `V` as an unconstrained `RationalCovering A`. There is no hypothesis linking V to the product `Uf × ⊔ Vgs_at`. The conclusion `V.IsOXAcyclic` cannot follow because V is utterly generic.

**Already self-acknowledged**: The lemma's own inline note says: *"NOTE 2026-05-28: the lemma as stated is missing structural hypotheses binding V to the product Uf × ⊔ Vgs_at (V refines product, Vgs covers V). Without these, V is generic and the conclusion isn't deducible."*

**Attacks attempted**:
- [1] Counterexample search: take V = arbitrary `RationalCovering A` (e.g., the trivial 1-cover of an unrelated `D₀`). Hypotheses on Uf and Vgs_at can still be satisfied independently of V. Conclusion `V.IsOXAcyclic` doesn't follow.
- [2] Edge-case instantiation: V = empty cover (no pieces). Then `IsOXAcyclic` requires `presheafValue V.base` separation/gluing fields; nothing in the hypotheses constrains these.
- [3] Source-drift attack: Wedhorn's Prop A.3(3) (p. 116 of arXiv:1910.05934) gives the acyclicity transfer for the *specific* product construction `𝒰 × 𝒱`. The Lean signature elides this — V is not the product, but a generic cover.

**Verdict**: B2-CANDIDATE. Needs at minimum: a hypothesis linking V to the product. Either `V.IsLaurentCover` (composing Uf's `f` with Vgs_at's `gs`) or an explicit covering-relationship between V and the product.

---

### L10. `mulArchimedean_valueGroup_of_stronglyNoetherianTate`

**Statement**: For any `v : Spv A` (the full valuation spectrum, not just continuous), `MulArchimedean (ValueGroupWithZero A)` under the v-induced valuative relation.

**The B2 defect**: Spv A includes non-continuous valuations. Wedhorn 7.40(6) gives height ≤ 1 only for **analytic continuous** valuations (those with non-open support). Without restricting to continuous v, the claim is over-stated.

**For the trivial case**: a "trivial" valuation has value group {0, 1}, which IS MulArchimedean (trivially). For non-trivial non-continuous v, MulArchimedean may fail (the value group could be arbitrary).

**Attacks attempted**:
- [1] Counterexample search: take A = ℤ_p with the discrete topology. The (p-adic) ℤ_p valuation is continuous and rank-1, but consider a non-continuous v on ℤ_p with value group ℤ² lex-ordered (height-2 valuation extending the p-adic). Such v lies in Spv ℤ_p but has non-archimedean value group. Wedhorn 7.40 doesn't apply because v isn't continuous.
- [2] Edge cases: v = trivial valuation (supp = max ideal). Value group {0,1} — trivially MulArchimedean. ✓ for this case.
- [3] Source-drift attack: Wedhorn 7.40(6) (p. 66, *Remark 7.40*) is explicitly *"For an analytic continuous valuation x ..."*. The Lean signature drops "analytic continuous" entirely.

**Verdict**: B2-CANDIDATE. Signature must restrict to `v ∈ Spa A A⁺` (continuous + integral) or `v ∈ Cont A` (continuous). The consumer `exists_dominating_unit` applies it through Spa-points, so adding the `v ∈ Spa A A⁺` quantifier is naturally available.

---

### L12. `index_selection_on_laurent_piece`

**Statement**: Given `T : Finset A`, `s : Aˣ`, `V : RationalCovering A`, `Vj ∈ V.covers`, conclude `∃ t ∈ T, ∀ v ∈ rationalOpen Vj.T Vj.s, v.vle (s : A) t`.

**The B2 defect**: V has no hypothesis tying it to T or s. Vj is an arbitrary piece of arbitrary V.

**The σ-walk argument requires V to be the specific Laurent cover by `s⁻¹·T`** so that each piece Vj is characterized by a sign vector, which picks out a distinguished dominant element of T.

**Attacks attempted**:
- [1] Counterexample search: take V = trivial 1-cover of D₀ with V.covers = {D₀}, T = {f, g} with v(f) and v(g) both incomparable on D₀'s rationalOpen (e.g., split into pieces). No single t ∈ T dominates v(s) on all of D₀. Conclusion fails.
- [2] Edge cases: T = ∅. Conclusion claims `∃ t ∈ ∅` — vacuous false. The lemma's hypotheses don't exclude empty T.
- [3] Source-drift attack: Wedhorn p. 84 second paragraph of (ii) — the σ-walk pick happens specifically because V is the Laurent cover by s⁻¹·T = "characterised by sign conditions on {s⁻¹·t_i}". For arbitrary V, no such characterization.

**Verdict**: B2-CANDIDATE. Signature needs `(_hV_laurent : V.IsLaurentCover ((T.toList).map (fun t => ((s⁻¹ : Aˣ) : A) * t)))` or equivalent.

---

### L14. `unit_gen_restriction_of_dominating_laurent`

**Statement**: Given C (with `IsGeneratedBy T`), dominating unit s, V, Vj ∈ V.covers, conclude `∃ C_restr` with `C_restr.base = Vj`, `IsUnitGenerated`, refines C, covers Vj.

**The B2 defect**: V is unconstrained. The intermediate lemmas (L12 index_selection, L13 canonical_unit) require V to be the s⁻¹·T-Laurent cover for the σ-walk argument to even make sense.

**Attacks attempted**:
- [1] Counterexample search: V = trivial 1-cover of some D₀ unrelated to C. Vj = D₀. The hypotheses on C, T, s, h_dom can all hold while Vj is an arbitrary rational subset. The C_restr at Vj would need to refine C ∩ Vj, which depends on Vj's geometry — there's no reason a unit-generated restriction exists.
- [2] Edge case: Vj = Spa A (the whole space). Then the "restriction to Vj" is just C itself, but C has IsGeneratedBy T (not IsUnitGenerated). Bijection issue similar to the resolved Q1.
- [3] Hypothesis-strength: removing the `_hV_laurent : V.IsLaurentCover` hypothesis from the natural caller still doesn't hurt — because the lemma doesn't have it in the first place. That's the smell.

**Verdict**: B2-CANDIDATE. V, Vj must be tied to the dominating-unit Laurent cover. Specifically: V should be `laurent_cover_from_dominating_unit D₀ T s` (the constructor from L11), and Vj a piece thereof.

---

### L15. `ratio_laurent_cover_of_units`

**Statement**: Given `D₀`, `units : Finset A`, `_h_units_unit : ∀ f ∈ units, IsUnit (D₀.canonicalMap f)`, conclude `∃ V, fs with V.IsLaurentCover fs ∧ V.base = D₀`.

**The B2 defect**: The output `fs` is existentially quantified with **no constraint relating it to `units`**. The hypothesis `_h_units_unit` becomes free-floating — any Laurent cover of D₀ satisfies the conclusion regardless of `units`.

**Attacks attempted**:
- [1] Counterexample search: take any pre-existing Laurent cover V of D₀ by any `fs : List A`. Then `∃ V, fs, ...` is satisfied trivially. The output is unrelated to units.
- [2] Edge case: units = ∅ (empty Finset). Hypothesis `_h_units_unit` is vacuous. Conclusion can still be satisfied by the trivial single-piece cover. But then this lemma adds NO information beyond `∃ Laurent cover of D₀`, which exists by the empty Laurent.
- [3] Source-drift attack: Wedhorn p. 84 (iii) — "the Laurent cover generated by `{f_i f_j^{-1} : 0 ≤ i, j ≤ n}`" specifies what fs IS. The Lean signature drops the explicit fs construction.

**Verdict**: B2-CANDIDATE. Conclusion must constrain `fs = (units ×ˢ units).toList.map (fun ⟨f,g⟩ => f * g⁻¹)` or similar (the project's ratio construction).

---

### L16 + L17. `ratio_laurent_covers_each_unit_gen_piece` AND `ratio_laurent_refines_unit_gen`

**Same B2 pattern**: Both take `V : RationalCovering A` with `V.IsLaurentCover fs` for arbitrary `fs`. For the σ-walk to identify which V-piece refines into which C-piece D, V must be the specific ratio Laurent cover built from C's unit generators.

**Attacks attempted (joint)**:
- [1] Counterexample: V = laurentRationalCover D₀ g for some g unrelated to C. V.IsLaurentCover [g] holds. But V's pieces are R(g/1) and R(1/g), with no relationship to C-pieces.
- [2] Edge case: fs = []. V is single-piece. The conclusion's σ-walk has nothing to walk.
- [3] Source-drift: Wedhorn's (iii) names the specific cover. The lemmas should too.

**Verdict (both)**: B2-CANDIDATE. Need `fs = ratio list from C's unit generators`.

---

### L18 + L19. `laurent_cover_refines_idealgen_cover` AND `laurent_cover_covers_each_idealgen_piece`

**Same B2 pattern**: V is `V.IsLaurentCover fs` with `fs` arbitrary. The conclusion claims V refines C / covers each C-piece. For this to hold, fs must be `s⁻¹·T` for the dominating unit (per Wedhorn 8.34(ii)).

**Subtle point**: The hypothesis `_hV_unit_restrictions` provides per-Vj unit restrictions but doesn't pin V's structure. An arbitrary V with arbitrary "_hV_unit_restrictions" supplied as a side-by-side existential won't necessarily refine C — the unit restrictions could be witnessing different unrelated facts.

**Attacks attempted**:
- [1] Counterexample: V = laurentRationalCover D₀ g (g unrelated to T, s). Provide a fake `_hV_unit_restrictions` by trivially returning the input V as C_restr (since `V.base = C.base`). Conclusion fails: V's pieces don't refine C.
- [2] Edge case: T = ∅, fs = []. V single-piece. Either: (a) refines vacuously (no C-pieces); (b) covers-each fails because C has pieces but V doesn't refine into them. The lemma doesn't address this edge.
- [3] Source-drift: Wedhorn p. 84 paragraph (ii) end — "the Laurent cover generated by `s⁻¹·f_1, …, s⁻¹·f_r`" — the cover IS specifically this.

**Verdict (both)**: B2-CANDIDATE. fs must be tied to s⁻¹·T for the dominating unit.

---

## B2-confirmed (prior-log matches)

### L8. `laurent_restriction_isLaurent` (matched Q1 of expert-review)

Already addressed in the 2026-05-28 expert-review: Wedhorn p. 84 uses `f_i|U` (image generators in 𝒪_X(U)), not the original `f_i ∈ A`. Sub-ticket `T-WC-LAURENT-RESTR-INDUCTION-DIRECT` spawned to bypass via direct induction. **No new action needed** — already on the board.

### L20. `rationalCovering_from_idealGenSet` (logged today)

Already logged to `b2_log.jsonl` as entry 40 (T-WC-RAT-COV-FROM-IDEAL-DEFECT). Form-(a) `IsGeneratedBy S` pieces vs form-(b) `(insert f C.base.T)` hypothesis. **No new action needed** — already documented.

---

## API-GAPs (correctly scoped, infrastructure missing)

### L1. `example_638_plus_side_noeth_pairSubring`

**Source**: Wedhorn 6.18 (p. 51): noeth pair-subring of strongly noeth Tate. Verbatim claim matches the Lean signature.

**Discharge attack**: searched project for `pairSubring.*noeth` / `wedhorn_6_18` — only the consumer sites cite Wedhorn 6.18; no proof of 6.18 exists in the project. This is a textbook substantive proof.

**Verdict**: API-GAP. Tractable substantive Wedhorn-text work. Likely needs Krull-style argument about T-adic completion.

### L4. `wedhorn_lemma_833_gluing_as_field` (already audited in /expert-review)

**Status**: API-GAP confirmed. The investigation (T-WC-833-CHECK-ROW3-EXACT-EXISTS, DONE) found `LaurentCover.row3_exact` + Route-B bridges exist; the body needs Wedhorn 8.31 propagation for `presheafValue D₀` typeclasses (sub-ticket T-WC-WEDHORN-831-PROPAGATION spawned).

### L5. `isOXAcyclic_of_single_unit_piece_gluing`

**Status**: API-GAP. Sub-ticket T-WC-SINGLE-UNIT-GLU-ISO documents the route via IsLocalization.atUnits.

### L13. `canonical_unit_of_pointwise_lower_bound`

**Statement**: Vj : RationalLocData, t : A, s : Aˣ. `∀ v ∈ rationalOpen Vj.T Vj.s, v.vle (s : A) t` ⟹ `IsUnit (Vj.canonicalMap t)`.

**Mathematical truth**: The statement is true. v(s) ≤ v(t) on Vj's rationalOpen, and s is a global unit, so v(s) ≠ 0 ⟹ v(t) ≠ 0 on all of Vj. Hence canonicalMap t doesn't vanish on the rational subset, hence is a unit in the structure sheaf.

**API gap**: The project has `noCommonZero_of_idealGen` (in WedhornCechAcyclicity.lean) and `IsUnit f from "∀ v ∈ Spa A A⁺, ¬ v.vle f 0"` (AdicSpectrum.lean), but at the *global* A level. For the *relative* level (`IsUnit (Vj.canonicalMap t)` from non-vanishing on Vj's rationalOpen), there's no direct theorem.

**Attacks attempted**:
- [1] Counterexample: Vj.canonicalMap t goes into Completion(Localization.Away Vj.s). For t non-vanishing on the rational subset, the limit-element identification with a unit requires the adic-spaces structure theorem — not unconditional algebra.
- [2] Discharge attack: searched for `canonicalMap.*IsUnit.*nonvanish` / `presheafValue.*unit` — no exact match found in the project.

**Verdict**: API-GAP. Tractable but requires a small new theorem ("non-vanishing on rationalOpen ⇒ IsUnit in presheafValue") that should be added at the structure-sheaf level.

### L21. `ideal_gen_refinement_covers_each_piece`

**Status**: API-GAP-cascade. Depends on `rationalCovering_from_idealGenSet` (L20, B2-confirmed). Once L20's signature is fixed, L21 may become tractable.

### L22. `restrictToPiece_acyclic_at_D`

**Status**: API-GAP. Sub-ticket T-WC-RESTRICT-TO-PIECE-RECURSIVE-834 documents the Wedhorn 8.34-at-𝒪_X(D) route.

---

## READY-substantive (provable as stated)

### L2/L3. `example_638_plus_side_cont_evalHom` / `example_638_minus_side_cont_underlying_evalHom`

Continuity of the evaluation hom using the project's `evalHomBounded`. The sketch ("the continuity field of `evalHomBounded`") is sound. ~30 LOC each.

**Attack [1]**: Counterexample search: searched project for `evalHomBounded.*Continuous` — yes, the construction includes continuity. Discharge available.

**Attack [2]**: Edge case f = 0: `canonicalMap 0 = 0`, evalHom sends X to 0, still continuous (constant map). OK.

**Verdict**: READY-substantive. Should compile in a focused session.

### L6. `laurent_cons_decomp_as_product`

**Statement**: V.IsLaurentCover (f :: gs) ⟹ ∃ Uf, Vgs_at, ... (product decomposition).

This is a structural fact about how Laurent covers factor as products. Wedhorn p. 84 references this explicitly: "𝒱 := 𝒰_{f₁} × ⋯ × 𝒰_{f_r}".

**Attacks attempted**:
- [1] Edge case gs = [] (single f): then 𝒱 = 𝒰_f is the 2-cover. The output Uf = laurentRationalCover, Vgs_at gives trivial 1-covers of each Uf-piece. ✓.
- [2] Edge case f = 0: laurentRationalCover D₀ 0 has degenerate pieces. The Laurent algebra factorization may require f ≠ 0. The signature doesn't exclude f = 0 — potential edge issue but not a B2.
- [3] Source-drift: Wedhorn states the product structure verbatim. The Lean output existential matches.

**Verdict**: READY-substantive. Constructive proof from the Laurent-product definition. ~80-120 LOC.

### L9. `exists_principal_pair_with_A₀_subset_Aplus_and_pseudouniformizer`

**Statement**: ∃ (P, π) with P.A₀ ≤ A⁺, P.I = Ideal.span {π}, π topologically nilpotent, π unit.

**Source**: Wedhorn 6.14 (p. 49, "principal pair exists in any Tate ring") + Remark 7.17 (p. 60, "A⁺ contains all topologically nilpotent elements"). Each cited claim is in the Wedhorn text.

**Attacks attempted**:
- [1] Counterexample: needs Tate-ring structure to produce π. The hypothesis set [IsTateRing A] [CompatiblePlusSubring A] is sufficient.
- [2] Hypothesis test: [IsStronglyNoetherian A] is in scope but unused by Wedhorn 6.14 (which only needs Tate). Over-specified but not a defect.

**Verdict**: READY-substantive. Wedhorn-text composition, ~80 LOC.

### L11. `laurent_cover_from_dominating_unit`

**Statement**: ∃ V, fs with V.IsLaurentCover fs ∧ V.base = D₀ ∧ fs = (T.toList).map (s⁻¹ · ·).

**Note**: Unlike L15 (`ratio_laurent_cover_of_units`), this lemma DOES pin fs explicitly. The output constrains fs to be the dominating-unit form. **This is a constructive lemma, not a B2.**

**Verdict**: READY-substantive. Build by induction on the list; iterate `laurentRationalCover`.

---

## Decomposition-tree audit

The 22 sorries form a dependency cascade. The B2-candidates cluster in the σ-walk / dominating-unit chain (Wedhorn 8.34 (ii)/(iii)).

**Cluster diagram of B2-candidates**:

```
L11 laurent_cover_from_dominating_unit  (READY: constructs the specific V)
   └─→ L12 index_selection_on_laurent_piece (B2: V unconstrained)
      └─→ L13 canonical_unit (API-GAP)
         └─→ L14 unit_gen_restriction (B2: V, Vj unconstrained)
            └─→ L18 laurent_cover_refines_idealgen (B2: fs unconstrained)
               └─→ L19 laurent_cover_covers_each_idealgen (B2)

L15 ratio_laurent_cover_of_units (B2: fs not constrained)
   └─→ L16 ratio_laurent_covers_each_unit_gen_piece (B2)
   └─→ L17 ratio_laurent_refines_unit_gen (B2)

L20 rationalCovering_from_idealGenSet (B2-CONFIRMED)
   └─→ L21 ideal_gen_refinement_covers_each_piece (API-GAP-cascade)
```

**Key observation**: Fixing L11 to also expose its constructive form publicly (i.e., a public `Definition` of the "ratio Laurent cover", not just an `∃`-statement), and tying L12, L14, L18, L19 to that specific construction via `_hV_eq` hypotheses, resolves the 4-deep chain. Same applies to L15 cluster (L15 → L16, L17).

---

## Confidence gate (Step 5)

The gate **FAILS** on this audit:

- **Gate 1 (leaf classification)**: Of 22 sorries:
  - 9 newly-identified B2-candidates → not READY for ticketing without restatement
  - 2 B2-confirmed (already logged)
  - 6 API-GAPs (correctly scoped via sub-tickets)
  - 5 READY-substantive
  - Verdict: Gate 1 fails on the 9 B2-candidates.

- **Gate 2 (Lean skeleton compiles)**: ✓ `lake build` passes (3145 jobs, sorry warnings only).

- **Gate 3 (verbatim quotes per leaf)**: Partial. Wedhorn pages 51, 49, 60, 66, 84, 86 cited per leaf. Verbatim quotes provided for the key claims; not exhaustive per the strict template.

- **Gate 4 (adversarial attacks per leaf)**: ✓ for the 9 B2-candidates (3+ attacks each).

- **Gate 5 (prior-B2 log consultation)**: ✓ 40 entries checked; 2 matches surfaced (L8, L20).

- **Gate 6 (mirrors source structure)**: Partial. The 9 B2-candidates do NOT mirror Wedhorn's structure — they elide the cover-construction-specific hypotheses Wedhorn explicitly uses.

---

## Recommendation

**No new tickets via this decompose pass** (per the planning-only-planning rule).

**Recommended next step**: User decides between two paths:

**Path A — Restatement-first**: Run `/develop --continue` to apply the 9 signature restatements per the B2-candidate verdicts. Most are mechanical: add `_hV_eq` / `_hfs_eq` hypothesis tying the cover to the construction. Propagate to consumers. Then resume `/beastmode`.

**Path B — Construction-first**: Land `laurent_cover_from_dominating_unit` (L11) and `ratio_laurent_cover_of_units` (L15, with the constructive fs constraint added) FIRST as READY-substantive landings. Then restate the σ-walk lemmas (L12, L14, L16-19) to take the *specific construction* as an explicit input rather than as a generic V. This avoids the `∃ V`-pattern cascade.

Path B is more Wedhorn-faithful (Wedhorn names the construction); Path A is faster to ticket-land.

**Estimated impact**: Path A surfaces 9 fresh restatements but unblocks Bucket B3 + B5 work as a whole. Path B avoids cascading restatements but adds 2 substantive constructive lemmas (L11, L15) ahead of the σ-walk lemmas.

Either path keeps the 6 API-GAPs and 5 READY-substantive lemmas on their current sub-ticket / direct-pickup tracks.

---

*Audit completed 2026-05-28. Source: Wedhorn 2019 §8.3-8.4 (pp. 81-86) + §7.40 (p. 66) + §6.14, 6.18 (pp. 49, 51) + §A.3 (Appendix A).*
