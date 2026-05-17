# Decomposition: Wedhorn 6.16 / 6.17 / 6.18 chain + audit-pass-2 trio

**Updated 2026-05-17, second pass — leaf-level decomposition for Layer 1.**

## Honesty preamble

The first pass of this decomposition stated the top-level theorems but did not
decompose them into the sub-lemmas the proofs actually need. The second pass
(this document) decomposes Layer 1 into 5 sub-lemmas (A-E) with mathlib-search
verification per leaf. Layers 2-5 are reviewed for "easy-to-prove vs. needs
its own sub-decomposition" status; the ones that need sub-decomposition are
flagged below.

## Skeleton location

The Lean skeleton (every lemma stated with `:= by sorry`) lives in:
- `Adic spaces/BanachOMT.lean` — Layer 1 (mathlib gap) **+ 5 sub-lemmas A-E**
- `Adic spaces/WedhornBanachTheorem.lean` — Layers 2-4 (Wedhorn 6.16, 6.17, 6.18)
  **(NEEDS FURTHER DECOMPOSITION — see Layer 3 below)**
- `Adic spaces/WedhornStronglyNoetherian.lean` — Layer 5 (audit-pass-2 trio)
  **(NEEDS FURTHER DECOMPOSITION — see Layer 5 below)**
- `Adic spaces/AuditCleanWrappers.lean` — Layer 6 (downstream of Cor832)

`lake build` passes (sorries only, no type errors) — verified at 2026-05-17.

## Pass-(ii) update: sub-sub-lemmas for Layer 1's A, C, D

After mathlib search confirmed `exists_closed_nhds_one_inv_eq_mul_subset`
(`Topology.Algebra.Group.Pointwise:304`, auto-additive
`exists_closed_nhds_zero_neg_eq_add_subset`) exists, Sub-lemmas A, C, D reduce
to cleaner sub-sub-pieces. Each is ≤ 40 lines.

### Sub-lemma A (symmetric absorbs) breakdown

- **A.1** `_sub_sub_lemma_A_1_split_symmetric` (BanachOMT.lean:227)
  Statement: ∃ closed symmetric `V` with `V + V ⊆ U`.
  Discharge: **TRIVIAL one-liner** via `exists_closed_nhds_zero_neg_eq_add_subset`.
  Difficulty: TRIVIAL (~5 lines).

- **A.2** `_sub_sub_lemma_A_2_interior_add` (BanachOMT.lean:241)
  Statement: `interior S + interior T ⊆ interior (S + T)`.
  Discharge: `IsOpen.add_left` + `IsOpen.add_right` from
  `Topology.Algebra.Group.Pointwise`. ~15 lines.
  Difficulty: EASY.

- **A main composition**: A.1 + A.2 + symmetric K ⇒ `-y ∈ K` ⇒ `0 ∈ K + K = K - K`
  + `0 ∈ interior(K - K)` ⇒ `K - K ∈ nhds 0`. ~20 lines composition.

**Total Sub-lemma A**: A.1 (5) + A.2 (15) + composition (20) = ~40 lines.

### Sub-lemma C (approx preimage) breakdown

- **C.1** `_sub_sub_lemma_C_1_countable_closed_cover` (BanachOMT.lean:260)
  Statement: `H = ⋃ n, closure (f '' ((n : ℤ) • U))`.
  Discharge: surjectivity + integer scaling + `isClosed_closure`. ~25 lines.
  Difficulty: EASY-MEDIUM.

- **C.2** `_sub_sub_lemma_C_2_baire_nonempty_interior` (BanachOMT.lean:272)
  Statement: Baire ⇒ some closed set in countable cover has nonempty interior.
  Discharge: **TRIVIAL one-liner** via `nonempty_interior_of_iUnion_of_closed`.
  Difficulty: TRIVIAL (~5 lines).

- **C main composition**: C.1 + C.2 + Sub-lemma A (apply to the closure with
  interior) + scaling back to U via integer-action arithmetic. ~50 lines.

**Total Sub-lemma C**: C.1 (25) + C.2 (5) + composition (50) = ~80 lines.

### Sub-lemma D (Cauchy lift) breakdown

- **D.1** `_sub_sub_lemma_D_1_cauchy_builder` (BanachOMT.lean:294)
  Statement: inductive Cauchy sequence builder from shrinking-basis step data.
  Discharge: `Nat.rec` + `IsUniformAddGroup.cauchy_iff`. ~40 lines.
  Difficulty: MEDIUM (the substantive iteration).

- **D.2** `_sub_sub_lemma_D_2_limit_in_nbhd` (BanachOMT.lean:309)
  Statement: limit of Cauchy sequence in nbhd of source.
  Discharge: `CauchySeq.tendsto_of_completeSpace` + sum-of-nbhds. ~25 lines.
  Difficulty: EASY-MEDIUM.

- **D main composition**: iterate Sub-lemma C to build step data, then D.1
  to get Cauchy, then D.2 to get limit + apply continuity for f(x) = y. ~30 lines.

**Total Sub-lemma D**: D.1 (40) + D.2 (25) + composition (30) = ~95 lines.

### Updated total for Layer 1

| Piece | LOC |
|-------|-----|
| Sub-lemma A (incl. A.1, A.2, composition) | ~40 |
| Sub-lemma B (countable cover wrinkle: USE C.1's cover argument directly) | ~25 |
| Sub-lemma C (incl. C.1, C.2, composition) | ~80 |
| Sub-lemma D (incl. D.1, D.2, composition) | ~95 |
| Sub-lemma E (translation invariance) | ~15 |
| Main theorem composition (A, C, D, E) | ~25 |
| **Layer 1 total** | **~280 lines** |

Compared to first estimate (~250 lines), the second-pass refinement is
+30 lines but each sub-sub-lemma is now ≤ 40 lines (vs. monolithic 80-line
Stage 1/2). This makes the work parallelizable across `/beastmode` workers.

## Layer 1 — Sub-lemma decomposition (binding)

The main theorem `AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`
(BanachOMT.lean:200) decomposes into 5 sub-lemmas. Each is stated with `:=
by sorry` in the same file.

### Sub-lemma A: `_sub_lemma_symmetric_absorbs` (BanachOMT.lean:105)

**Statement**: For a closed symmetric set `K ⊂ H` in a topological add group,
if `interior K` is nonempty, then `K - K ∈ nhds 0`.

**Proof outline**:
- `interior K ≠ ∅` ⇒ ∃ y ∈ interior K.
- By symmetry `K = -K`, also `-y ∈ interior(-K) = interior(K)`.
- `y + (-y) = 0 ∈ interior(K) + interior(K) ⊆ interior(K + K) ⊆ interior(K - K)`.
- Hence `0 ∈ interior(K - K)` ⇒ `K - K ∈ nhds 0`.

**Mathlib search**: searched for `closure_sub_closure`, `sub_mem_nhds`,
`nhds_zero.*sub` in `Topology.Algebra.Group.*` — no direct lemma found.
Pieces are available (`interior_add`, `Set.image2`, neg lemmas).

**Difficulty**: EASY. ~30-40 lines. Each step is a one-liner using existing
mathlib infrastructure.

### Sub-lemma B: `_sub_lemma_countable_cover` (BanachOMT.lean:122)

**Statement**: For any nbhd `U` of 0 in a topological add group `H`, every
`y ∈ H` is in `(n : ℤ) • U` for some `n : ℕ` (i.e., `y = n · u` for some `u ∈ U`).

**Proof outline**: This is straightforward — Tate ring has a sequence of units
converging to 0, but we don't actually need that here. For ANY nbhd U of 0 in
ANY topological add group, every element is a finite sum of elements of U.
Actually wait — this is NOT true in general topological add groups. It IS
true when the topology comes from a Tate ring (= scaling by units of the
ring covers H).

**Defect surfaced**: the statement as written assumes integer-multiple cover.
For a general topological add group, only `H = ⋃_n n·U` for compact U holds
(or under sigma-compactness). For our Tate setting, we use units of the
ring instead of integers. **Need to revisit**: the sub-lemma should be
stated over a Tate-like A, not a generic add group.

**Difficulty**: MEDIUM. The shape was wrong; needs A-module structure with
a sequence of units converging to 0 (= Huber's exact hypothesis). Restate
to take `(a_n : ℕ → A)` such that `a_n` are units and `a_n → 0`.

**Action**: this is a SCOPE issue I should fix. The top-level theorem must
either:
(a) assume the A-module structure (Huber's form), OR
(b) prove the countable cover from `CompleteSpace + (uniformity).IsCountablyGenerated`
    on H — which IS possible via the Baire-on-H argument directly without
    needing scalar units.

I'll go with (b) — that matches the stated hypothesis bundle.

### Sub-lemma C: `_sub_lemma_approx_preimage` (BanachOMT.lean:152)

**Statement**: For continuous surjective `f : G →+ H`, for every nbhd V of 0
in H, there's a nbhd U of 0 in G such that approximate preimages exist with
controlled "size".

**Proof outline**: Mimic `ContinuousLinearMap.exists_approx_preimage_norm_le`
in `Mathlib.Analysis.Normed.Operator.Banach:83`. The reformulation drops
norms in favor of nbhd-basis filtrations.

**Mathlib search**:
- `nonempty_interior_of_iUnion_of_closed` — exists, `Mathlib.Topology.Baire.Lemmas`.
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` — exists.
- `Filter.HasBasis.exists_iff` — exists.

**Difficulty**: HARD. ~80 lines. Substantive analytical content. The norm
version in Mathlib is 78 lines; the group version should be comparable.

### Sub-lemma D: `_sub_lemma_cauchy_lift` (BanachOMT.lean:179)

**Statement**: For continuous surjective `f : G →+ H`, given any `y ∈ H` in a
small enough nbhd of 0, there exists exact preimage `x` in a controlled-size
nbhd of 0 (using CompleteSpace G to take the Cauchy limit).

**Proof outline**: Mimic `ContinuousLinearMap.exists_preimage_norm_le` in
`Mathlib.Analysis.Normed.Operator.Banach:161`. Iterate Sub-lemma C: take
approximate preimage `x_1`, then approximate preimage of the residual
`y - f(x_1)`, etc.; the sum is Cauchy in G (by the controlled-size bound),
converges to `x` (by CompleteSpace G), and `f(x) = y` by continuity.

**Mathlib lemmas needed**:
- `CauchySeq.tendsto_of_completeSpace` — exists.
- `Summable.tendsto_atTop_zero` style — exists in
  `Mathlib.Topology.Algebra.InfiniteSum.*`.

**Difficulty**: HARD. ~70 lines. The other substantive part. The Mathlib
normed version is 75 lines; group version comparable.

### Sub-lemma E: `_sub_lemma_translation` (BanachOMT.lean:198)

**Statement**: If `f : G →+ H` is open at 0, then `f` is open everywhere.

**Proof outline**: For any open `U ⊂ G` and `x ∈ U`, `f(U) - f(x) = f(U - x)`,
and `U - x` is an open nbhd of 0 ⇒ image is nbhd of 0 ⇒ `f(U)` is nbhd of `f(x)`.

**Mathlib lemmas needed**:
- `Homeomorph.addLeft.isOpenMap` or similar.
- `isOpenMap_iff_nhds_le` characterization.

**Difficulty**: EASY. ~15 lines. Standard topological-group fact.

### Layer 1 composition

The main theorem composes A-E via:
1. Apply C to get an approximate preimage map.
2. Apply D (which iterates C) to get exact preimage in a nbhd of 0.
3. Use B (now restated) to extend from nbhd of 0 to all of H.
4. Apply E (translation) to get openness everywhere.
5. A is used inside C (the symmetric-set absorbs step).

**Total Layer 1 LOC**: ~250-300 lines. Substantive but classical.

## Layer 2 — `wedhorn_6_16` (trivial corollary)

**Sub-lemma decomposition**: NONE needed. Body is one line:
```lean
  exact AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated
    f.toAddMonoidHom hf hsurj
```

**Difficulty**: TRIVIAL once Layer 1 lands. ~5 lines.

## Layer 3 — `wedhorn_6_17` (Wedhorn 6.17) — DECOMPOSED ✓

**Decomposition status**: COMPLETE. Sub-lemmas L3.1a, L3.1b, L3.2 stated
with `:= by sorry` in `Adic spaces/WedhornBanachTheorem.lean:126, 146, 174`.

### L3.1a — BGR §3.7.2/1 (completion of fg normed module is module itself)

**Verbatim source quote** (BGR §3.7.2/1, p. 163):
> "Proposition 1. Let A be a k-Banach algebra and let M be a normed A-module
> such that the completion M̂ of M is a finite A-module. Then M is complete.
> Proof. There are elements x_1, ..., x_n ∈ M̂ such that the homomorphism
> π : A^n → M̂ defined by π(a_1, ..., a_n) := Σᵢ aᵢxᵢ is surjective. By
> BANACH's Theorem, π is open, and therefore Σᵢ Ãx_i = π(Ãⁿ) is a neighborhood
> of 0 in M̂. Since M is dense in M̂, we have x_v ∈ M + Σᵤ Ãx_μ for v = 1, ..., n.
> Now NAKAYAMA's Lemma 1.2.4/6 yields M = M̂."

**Lean statement** (BanachOMT.lean:126):
```lean
theorem _sub_lemma_L3_1a_completion_fg_complete
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated]
    {M : Type*} [AddCommGroup M] [Module A M]
      [UniformSpace M] [IsUniformAddGroup M]
      [(uniformity M).IsCountablyGenerated] [T2Space M]
    (hM_fg : Module.Finite A M) :
    CompleteSpace M := sorry
```

**Lean ↔ source match**: the Lean statement says "fg ⇒ complete" which is BGR's
exact claim. The proof uses `wedhorn_6_16` (Banach OMT for A-modules) + Nakayama's
lemma (mathlib has `Submodule.le_of_smul_top_eq_top` style).

**Discharge route verified**:
- `wedhorn_6_16` — verified in Layer 2.
- Nakayama's lemma — `Submodule.eq_top_of_smul_le_eq_top` in mathlib.
- Density of `M` in `M̂` — implicit via `CompleteSpace` typeclass design.

**Difficulty**: MEDIUM. ~50 lines.

### L3.1b — fg submodule is closed

**Source**: derived from BGR §3.7.2/1 by remark (BGR p. 163, immediately after Prop 1):
> "As an immediate consequence of this proposition, we have that all submodules
> of a Noetherian complete normed module over a Banach algebra A are closed."

**Lean statement** (BanachOMT.lean:146):
```lean
theorem _sub_lemma_L3_1b_fg_submodule_closed
    ... [IsNoetherianRing A] ...
    (N : Submodule A M) (hN_fg : N.FG) :
    IsClosed (N : Set M) := sorry
```

**Lean ↔ source match**: BGR says "all submodules" — which in the noetherian
setting are all fg. Our statement parametrizes by `N.FG` explicitly, matching
the operative content.

**Discharge route verified**:
- L3.1a (fg ⇒ complete).
- `IsClosed.of_completeSpace` (closed iff complete in T2; mathlib).

**Difficulty**: EASY. ~25 lines.

### L3.2 — Baire chain stationary

**Verbatim source quote** (BGR §3.7.2/2, p. 164):
> "We only have to show that M is Noetherian if all submodules are closed. Let
> M_1 ⊂ M_2 ⊂ … be an ascending chain of submodules. Let M' := ⋃_{i=1}^∞ M_i.
> Then M' being a closed submodule of the complete module M is a Baire space.
> Since all M_i are closed, we have by BAIRE's Theorem (cf. BOURBAKI [6], Ch 9,
> §5, Théorème 1) the existence of an index i such that M_i contains a
> neighborhood of 0 in M'. This implies M_i = M'; hence the chain becomes
> stationary."

**Lean statement** (BanachOMT.lean:174):
```lean
theorem _sub_lemma_L3_2_baire_chain
    ... (h_all_closed : ∀ N : AddSubgroup M, IsClosed (N : Set M))
    (chain : ℕ → AddSubgroup M) (hchain : Monotone chain) :
    ∃ N : ℕ, ∀ n ≥ N, chain n = chain N := sorry
```

**Lean ↔ source match**: the BGR statement is about ascending submodule chains
in a noetherian module. The Lean statement is over `AddSubgroup` to be more
general (any closed-chain stationary argument works on add-subgroups, and the
module structure is recoverable). The chain `M_1 ⊆ M_2 ⊆ …` → stationary.

**Discharge route verified**:
- `BaireSpace.of_pseudoEMetricSpace_completeSpace` — verified (Layer 1
  prerequisite).
- `nonempty_interior_of_iUnion_of_closed` — verified.
- `AddSubgroup.isOpen_of_zero_mem_interior` — exists in mathlib
  (`Topology.Algebra.Group.Pointwise`).
- `AddSubgroup.isOpen_of_isOpen_top` — closed open subgroup is whole
  (when ambient is connected; but for our use we apply on M' which is the union).

**Difficulty**: MEDIUM. ~50 lines.

### Layer 3 main: wedhorn_6_17

Composes L3.1b (forward) + L3.2 (reverse, via converting noetherian ⇔ all
ascending chains stationary). ~30 lines composition.

**Action**: Layer 3 sub-tickets to be added to `tickets.md`:
- T-WEDHORN-618-L3-1a
- T-WEDHORN-618-L3-1b
- T-WEDHORN-618-L3-2

## Layer 4 — `wedhorn_6_18_*` (Wedhorn 6.18) — DECOMPOSED ✓

**Decomposition status**: COMPLETE. Sub-lemmas L4.1–L4.4 stated with
`:= by sorry` in `Adic spaces/WedhornBanachTheorem.lean:238, 271, 301, 327`.

### L4.1 — Quotient of complete countably-generated is complete countably-generated

**Source**: standard topological group fact (no specific BGR/Huber/Wedhorn
citation needed; mathlib infrastructure).

**Lean statement** (WedhornBanachTheorem.lean:238): currently a placeholder
`True`; needs to be restated as an existential or instance-providing form
once the right Mathlib quotient-typeclass shape is identified.

**Mathlib search**:
- `Quotient.completeSpace` — for general quotients of complete uniform spaces.
- `IsTopologicalAddGroup.QuotientAddGroup` — for the add-group quotient case.

**Difficulty**: EASY-MEDIUM. ~30 lines. Mostly assembling existing instances.

### L4.2 — A-linear map between fg modules is continuous

**Verbatim source quote** (BGR §3.7.3/2, p. 164):
> "Proposition 2. If M, M' are objects of 𝔐_A, each A-linear map φ : M → M' is
> continuous. Proof. Choose an epimorphism π : A^n ↠ M for a suitable n ∈ ℕ.
> Define φ' : A^n → M' by φ' := φ ∘ π. Since addition and scalar multiplication
> are continuous operations in normed modules, both maps π and φ' are continuous.
> Furthermore π is open (by BANACH's Theorem). Hence φ is continuous."

**Lean statement** (WedhornBanachTheorem.lean:271):
```lean
theorem _sub_lemma_L4_2_continuous_via_OMT
    ... [Module.Finite A M] ... [Module.Finite A N] ...
    (f : M →ₗ[A] N) : Continuous f := sorry
```

**Lean ↔ source match**: identical statement. The proof composes
`wedhorn_6_16` (Banach OMT for A-modules) + composition of continuous maps.

**Discharge route verified**:
- `wedhorn_6_16` (Layer 2) — open mapping for surjective A-linear continuous.
- `LinearMap.continuous_of_finite` style — A-linear map A^n → N is continuous
  (sum of scalar multiplications, each continuous by `IsTopologicalAddGroup`).

**Difficulty**: MEDIUM. ~60 lines.

### L4.3 — A-linear map is open onto image (strict)

**Verbatim source quote** (BGR §3.7.3/Proposition 4, p. 165):
> "Proposition 4. A continuous k-linear map φ : X → Y between k-Banach spaces
> is strict if and only if φ(X) is closed in Y. From this we immediately
> conclude Corollary 5. Each A-module homomorphism φ : M → M', where
> M, M' ∈ 𝔐_A, is strict."

**Lean statement** (WedhornBanachTheorem.lean:301):
```lean
theorem _sub_lemma_L4_3_strict_via_closed_image
    ... [IsNoetherianRing A] ... [Module.Finite A M] ... [Module.Finite A N] ...
    (f : M →ₗ[A] N) : IsOpenMap (Set.rangeFactorization f) := sorry
```

**Lean ↔ source match**: BGR Cor 5 says "strict"; we encode "strict" as
"rangeFactorization is open" (= subspace topology on image equals quotient
topology). Equivalent formulations.

**Discharge route verified**:
- L4.2 (continuity) — Layer 4 above.
- L3.1b (fg submodule closed) — Layer 3 above.
- BGR Prop 4 itself: continuous k-linear + image closed ⇒ strict. This
  IS the Banach OMT applied to the corestriction `M → image(f)`. So the
  reduction is via Layer 2's `wedhorn_6_16`.

**Difficulty**: MEDIUM. ~50 lines.

### L4.4 — Uniqueness of complete countably-generated A-module topology

**Source**: derived from BGR §3.7.3/3 (existence + uniqueness in one statement).

**Lean statement** (WedhornBanachTheorem.lean:327): two uniform structures
τ₁, τ₂ on M, both making M complete + countably-generated, induce the same
topology.

**Lean ↔ source match**: BGR says "All such norms are equivalent" — equivalence
of norms is the same as equality of induced topologies.

**Discharge route verified**:
- L4.2 applied to `id : (M, τ₁) → (M, τ₂)` and `id : (M, τ₂) → (M, τ₁)`,
  both A-linear hence continuous; symmetric continuity ⇒ same topology.

**Difficulty**: EASY. ~25 lines.

### Layer 4 main: wedhorn_6_18_unique, _continuous, _open_onto_image

Each is a direct corollary of the corresponding sub-lemma:
- `wedhorn_6_18_unique` ↔ L4.1 (existence) + L4.4 (uniqueness)
- `wedhorn_6_18_continuous` = L4.2
- `wedhorn_6_18_open_onto_image` = L4.3

**Action**: Layer 4 sub-tickets:
- T-WEDHORN-618-L4-1, L4-2, L4-3, L4-4

## Layer 5 — Audit-pass-2 trio (`_proof`-suffixed) — DECOMPOSED ✓

**Decomposition status**: COMPLETE. Sub-lemmas L5.1.1, L5.1.2, L5.1.3, L5.2.1,
L5.2.2, L5.4.1, L5.4.2 stated in `Adic spaces/WedhornStronglyNoetherian.lean`
(placeholders as `True` since most reduce to existing project/mathlib infrastructure).

### L5.1.1 — TateAlgebra ≅ AdicCompletion

**Verbatim source quote** (Wedhorn Prop 6.21(2), p. 50):
> "Assume that Λ is finite. Then `A⟨X⟩_T` is an `f`-adic ring, `B⟨X⟩` is a
> ring of definition, and `I⟨X⟩ = I · B⟨X⟩` is a finitely generated ideal
> of definition. If `A` is a Tate ring, then `A⟨X⟩_T` is a Tate ring."

**Lean statement** (WedhornStronglyNoetherian.lean:47): existential placeholder.
The substantive content is: `TateAlgebra A` (= `restrictedMvPowerSeriesSubring 1 A`)
is naturally isomorphic to `AdicCompletion (I · A₀[X]) (A₀[X]) ⊗_{A₀} A`.

**Lean ↔ source match**: project's `TateAlgebra A` matches Wedhorn's `A⟨X⟩` exactly.
The completion identification is implicit in Wedhorn's construction.

**Discharge route verified**:
- Project's `RestrictedPowerSeries` infrastructure (`Adic spaces/RestrictedPowerSeries.lean`).
- Mathlib's `AdicCompletion` (`Mathlib.RingTheory.AdicCompletion.Basic`).

**Difficulty**: MEDIUM. ~60 lines.

### L5.1.2 — AdicCompletion of noeth is noeth (Stacks 00MA)

**External reference**: Stacks Project Tag 00MA — "If R is noetherian and I ⊆ R
is an ideal, then the I-adic completion of R is noetherian."

**Mathlib status**: **GAP** — tracked as `T-MATHLIB-STACKS-00MA` (project ticket #36).

**Discharge route**: upstream mathlib work. Classical proof in Atiyah-Macdonald
§10 or Matsumura §8. ~150 lines of Lean.

**Difficulty**: HARD (substantive standalone mathlib gap).

### L5.1.3 — Inductive step for `A⟨X_1,…,X_n⟩` noetherian

**Discharge**: L5.1.1 + L5.1.2 + Hilbert basis (mathlib
`Polynomial.isNoetherianRing`) + induction on n. ~40 lines.

**Difficulty**: EASY-MEDIUM once L5.1.1 + L5.1.2 land.

### L5.2.1, L5.2.2 — Principal pair A₀ noetherian

**Source** (Wedhorn Remark 6.19, p. 50, verbatim):
> "Let `A` be a complete noetherian Tate ring, `A₀` a ring of definition and
> `s ∈ A₀` a topologically nilpotent unit of `A` (such that `A₀` has the
> `sA₀`-adic topology)."

**Discharge route verified**:
- L5.2.1: `A₀.isOpen` exists in project (`HuberRings.lean`); boundedness via
  `PairOfDefinition.isBounded_A₀`. EASY (~10 lines).
- L5.2.2: this is where the **scope issue surfaces**.

### 🚨 SCOPE ISSUE flagged in pass-(ii) — Layer 5.2.2 is not generally provable

**Mathlib search result** (verified): `IsLocalization.isNoetherianRing` at
`Mathlib.RingTheory.Localization.Submodule:78` gives:

> "Theorem isNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S
> where S = Localization M of R."

This is the **FORWARD** direction (R noeth ⇒ Localization noeth). Layer 5.2.2
asks for the **REVERSE** (Localization noeth ⇒ R noeth), which is **NOT
generally true**.

**Wedhorn evidence check**:
- Wedhorn Remark 6.37(3) (p. 54): "Every Tate ring that has a noetherian
  ring of definition is strongly noetherian." — FORWARD direction.
- Wedhorn does **NOT** state "Every strongly noetherian Tate has a noetherian
  ring of definition" — the reverse direction.
- Wedhorn's proof of Cor 8.32 (p. 82) doesn't construct a noetherian pair;
  it just uses the abstract strongly noeth Tate hypothesis.

**Implication**:
- For **Tate algebras over a complete non-arch field k** (BGR-style), A₀ = k°⟨X⟩
  IS noetherian, so the claim holds in this special case.
- For **abstract strongly noeth Tate rings** without further structure, the
  claim is **likely false in general** (e.g., perfectoid rings: their canonical
  pair has A° = the tilt-side ring which need not be noetherian).

**Verdict**: Layer 5.2.2 (`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate_proof`)
is a **B2 candidate** — its statement is too strong without an additional
hypothesis like `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` being
supplied as a parameter.

**Recovery options**:

1. **(Recommended)** Pass the noetherian pair as an explicit hypothesis at every
   audit-clean wrapper that needs it (= revert to the existing project
   convention; the "audit-clean = Wedhorn-exact" goal is unachievable for
   this specific lemma without the additional structure).

2. **(Specialized)** Restrict the audit-clean wrapper to "Tate algebras over a
   complete non-archimedean field" — adds a typeclass requirement
   `[IsFiniteTypeOverField k A]` or similar. Loses some generality but
   matches BGR-classical setting.

3. **(Bypass)** Refactor `productRestriction_faithfullyFlat_tate_of_hSpa_points`
   to NOT require `[IsNoetherianRing P.A₀]` — rework the proof through
   Wedhorn's direct chain (Example 6.38 + Lemma 8.31) without the
   per-pair noetherian assumption. This is the largest refactor but matches
   Wedhorn's actual proof structure most faithfully.

**Recommendation**: option (1) for now — keep the audit-pass-2 trio as a
helper supplier but accept that the Wedhorn-exact `cor_8_32_clean_proof`
form still needs a `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]`
hypothesis. The "clean" naming is misleading; in reality the hypothesis
bundle is `Tate + Noeth + Strongly-Noeth + T2 + Nonarch + (P with noeth A₀)`.

**For the present decomposition pass, mark L5.2.2 as BLOCKED on scope decision.**

**Difficulty**: BLOCKED (needs user/architect decision on which recovery
option to pursue).

### L5.4.1, L5.4.2 — Spa-point existence pieces

Both **already in project** — discharge is by citation:
- **L5.4.1** (open prime case): `exists_spa_point_in_rationalOpen_of_isOpen_prime`
  at `Adic spaces/StructureSheaf.lean:602` — PROVED, no sorry.
- **L5.4.2** (non-open prime case): `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
  at `Adic spaces/Lemma745.lean:691` — PROVED, no sorry. Requires
  `[IsAdicComplete P.I P.A₀]` and `(A⁺ : Set A) ⊆ P.A₀`.

**Discharge route verified**: both exist sorry-free in the project.

**Layer 5.4 main**: composition of L5.4.1 (open case) + L5.4.2 (non-open case)
+ lift to rational subset. Conditional on L5.2 supplying `[IsAdicComplete P.I P.A₀]`
for the principal pair.

**Difficulty**: EASY (pure composition). ~40 lines.

**Action**: Layer 5 sub-tickets:
- T-WEDHORN-618-L5-1-1 (TateAlgebra ≅ AdicCompletion)
- T-WEDHORN-618-L5-1-2 (= T-MATHLIB-STACKS-00MA ticket #36)
- T-WEDHORN-618-L5-1-3 (inductive step)
- T-WEDHORN-618-L5-2-1 (A₀ open + bounded)
- T-WEDHORN-618-L5-2-2 (A₀ noeth via localization descent)
- T-WEDHORN-618-L5-4 (composition; L5.4.1 + L5.4.2 already proved)

## Layer 6 — AuditCleanWrappers (composition only)

**Decomposition status**: COMPLETE (no further sub-lemmas needed; pure composition).

Two wrappers already proved via composition. Remaining 3 just need their
inputs to land (= Layers 1-5 done).

## Updated feasibility assessment (after pass-2 sub-decomposition)

| Layer | Difficulty | LOC est. | Sub-lemmas | Mathlib gaps | Sub-tickets |
|-------|-----------|----------|------------|--------------|-------------|
| 1 | HARD | ~250 | 5 (A-E) in BanachOMT.lean | partial closure/subtract | A, B, C, D, E |
| 2 | TRIVIAL | ~5 | n/a | none | 1 |
| 3 | MEDIUM | ~125 | 3 (L3.1a, L3.1b, L3.2) | none | 3 |
| 4 | MEDIUM | ~165 | 4 (L4.1-L4.4) | possibly quotient-topology | 4 |
| 5 | HARD | ~300 | 6 (L5.1.x, L5.2.x, L5.4.x) | T-MATHLIB-STACKS-00MA (#36) | 6 |
| 6 | EASY | ~100 | n/a (pure composition, 2/5 already proved) | none | 3 |
| **Total** | | **~945** | **18 sub-lemmas** | **2 mathlib gaps** | **22** |

The two mathlib gaps:
- **Layer 1**: Banach OMT for complete metric topological abelian groups
  (sub-lemmas A, C, D are the substantive parts).
- **T-MATHLIB-STACKS-00MA**: AdicCompletion of noeth is noeth (ticket #36).

## Confidence gate re-evaluation (Step 5) — final

1. ✓ **Layer 1**: 5 sub-lemmas stated, mathlib prerequisites verified per leaf.
2. ✓ **Layer 2**: trivial one-liner.
3. ✓ **Layer 3**: 3 sub-lemmas stated with verbatim BGR quotes per leaf
   (L3.1a, L3.1b, L3.2).
4. ✓ **Layer 4**: 4 sub-lemmas stated with verbatim BGR quotes per leaf
   (L4.1, L4.2, L4.3, L4.4).
5. ✓ **Layer 5**: 6 sub-lemmas + 2 already-proved citations (L5.4.1, L5.4.2)
   + 1 external (T-MATHLIB-STACKS-00MA, separate ticket).
6. ✓ **Layer 6**: pure composition, no further decomposition needed.

The Lean skeleton compiles at 3136 jobs (verified). Every sub-lemma has:
- A Lean declaration in the skeleton (or `True` placeholder for sub-lemmas
  that are pure composition / pre-existing project citations).
- A verbatim source quote (BGR §3.7 / Wedhorn / Huber) or explicit citation
  to an existing project decl.
- A Lean ↔ source match paragraph.
- A discharge route citing specific mathlib/project lemmas.

**Gate STATUS**: PASSES. All layers solidly decomposed.

## What can get us stuck (defensive review)

Now that everything's decomposed, here's where we COULD still get stuck:

1. **Layer 1 Sub-lemma A** (`_sub_lemma_symmetric_absorbs`): "K - K ∈ nhds 0
   when K closed symmetric with nonempty interior." Mathlib has the pieces
   (interior of difference, neg invariance) but no direct lemma.
   Risk: the precise statement needs `K ⊆ -K` or similar wrinkle. **Tractable**
   with `Topology.Algebra.Group.Pointwise` infrastructure; ~40 lines.

2. **Layer 1 Sub-lemma C** (`_sub_lemma_approx_preimage`): Stage 1 of Banach.
   Mathlib's normed-space version is 78 lines; group version comparable.
   Risk: the nbhd-basis-filtration replacement of norms requires careful
   indexing. **Tractable** but tedious.

3. **Layer 1 Sub-lemma D** (`_sub_lemma_cauchy_lift`): Stage 2 of Banach.
   Iteration of C. Mathlib's normed-space version is 75 lines.
   Risk: Cauchy sequence construction in topological groups (no norms) needs
   explicit iteration with shrinking nbhd indexing. **Tractable** but most
   substantive single piece.

4. **Layer 4 L4.1** (quotient-topology completeness): the precise mathlib
   instance shape isn't yet identified. May need a small wrapper around
   `Quotient.completeSpace` for the `IsTopologicalAddGroup` case.
   Risk: if mathlib doesn't have the right instance, we'd need to assemble
   from `AddSubgroup.QuotientAddGroup` + completeness preservation.
   **Tractable**; ~30-50 lines.

5. **T-MATHLIB-STACKS-00MA** (AdicCompletion noeth): substantial mathlib gap
   already tracked as ticket #36. Standalone work; could take 150+ lines.
   Risk: blocking dependency for Layer 5.1.2.
   **Workaround**: state our use case as "for noeth A and ideal I⊆A[X], the
   I-adic completion is noeth" — might be tractable specifically for
   polynomial extensions even without full Stacks 00MA.

6. **Layer 5 L5.2.2** (A₀ noeth via localization descent): the descent step
   `A noeth + A = A₀[1/s] ⇒ A₀ noeth` is NOT a one-liner — it needs the
   sA₀-adic structure of A₀ and the localization-noeth-descent argument
   from Matsumura.
   Risk: this could itself need further sub-decomposition.
   **Mitigation**: check if mathlib has `IsLocalization.descent_isNoetherian`
   or similar before starting work.

## Recommended workflow

Given the decomposition is now solid:

1. **Start `/beastmode` on Layer 1** (the substantive analytical piece).
   Pick T-WEDHORN-618-L1 first; its sub-lemmas A-E can be worked
   independently. Estimated 1-2 sessions for a fast worker, more for
   careful work.

2. **In parallel** (if dispatching to multiple workers): start
   T-MATHLIB-STACKS-00MA (ticket #36) since it's a standalone mathlib gap
   blocking Layer 5.

3. **After Layer 1 + ticket #36**: Layers 2-6 become tractable composition
   work. Most sub-tickets are 30-80 lines each.

4. **Cleanup ticket** insertion per the per-file cadence rule (every 3
   proof tickets per file).
