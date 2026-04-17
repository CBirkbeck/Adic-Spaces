# Development Plan: Close `restrictionMapHom_injective` (and thence tateAcyclicity Part 1)

**Target sorry**: `Adic spaces/PresheafTateStructure.lean:1238`
**Goal**: Close injectivity of `restrictionMapHom D₀ D h` (or equivalently, close tateAcyclicity Part 1 via another route).

**MUST PRESERVE**: signature of `tateAcyclicity` and `restrictionMapHom_injective` — only `[IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]`.

## Investigation findings (from prior sessions)

1. **`restrictionMapHom_injective_via_iso` is tautological** — ring equivs preserve injectivity both ways. The Example 6.38 iso doesn't reduce the problem.

2. **`mk_D₀s_isUnit` (target-side) is proved** (commit `5f4dd86`) but alone doesn't give injectivity — we need SOURCE-side non-zero-divisor of `D.s` in `presheafValue D₀`.

3. **Cor 8.32 gives PRODUCT injectivity, not single-map** (commit `dc87cce`). Via Cor832.lean's `tateAcyclicity_zero_kernel_of_flat_and_lifting`, product injectivity is conditional on `flat_over_base` and `hSpa_surj`.

## Following Wedhorn

### Wedhorn chain for tateAcyclicity Part 1:

- **Prop 8.2** (continuity): ✅ done.
- **Example 6.38** (ring iso): ✅ packaged (`presheafValue_tateAlgebra_quotient_iso`, conditional).
- **Lemma 8.31** (flatness of A⟨X⟩ quotients): ✅ done.
- **Prop 8.15** (restriction = rational localization): ⚠ partially scaffolded, blocked on source NZD.
- **Prop 8.30** (restriction flat as ring hom): ⚠ partially done.
- **Cor 8.32** (product faithful flat): ✅ abstract done.
- **Prop 8.30 → injectivity**: Wedhorn's actual argument requires A⟨T/s⟩ to be a specific completed localization where D.s is provably NZD.

### The critical insight

**Wedhorn does NOT separately prove single-map injectivity** — it follows from product injectivity (Cor 8.32) when the given cover is a singleton cover of the base (i.e., V = U₁), which happens iff `rationalOpen D = rationalOpen D₀`. For general `D ⊊ D₀`, single-map injectivity is EQUIVALENT to the specific localization structure at `D.s`.

**Key observation**: for tateAcyclicity Part 1, we don't need single-map injectivity — we need PRODUCT injectivity from ONE vanishing:
```
Hypothesis: ∀ D ∈ C.covers, restriction x = 0  (all vanishings)
Goal: x = 0
```
The hypothesis gives x in the kernel of the product restriction. By Cor 8.32, x = 0.

**So we can REROUTE tateAcyclicity Part 1 to use product injectivity**, sidestepping the single-map problem entirely!

## Strategy: 3-phase plan

### Phase A (PRIORITY): Reroute tateAcyclicity Part 1 via Cor 8.32

Instead of:
```lean
obtain ⟨D, hD⟩ := hne
exact ValuationSpectrum.restrictionMapHom_injective C.base D (C.hsubset D hD)
  ((hx D hD).trans (map_zero _).symm)
```

Use:
```lean
exact Cor832.tateAcyclicity_zero_kernel_of_flat_and_lifting
  flat_over_base hSpa_surj x hx
```

**Obligations**:
- `flat_over_base`: each `restrictionMap C.base D` is flat as `presheafValue C.base`-module. This is the Prop 8.15 content — CURRENTLY AN OPEN BLOCKER.
- `hSpa_surj`: `Spec(∏ presheafValue D) → Spec(presheafValue C.base)` surjective. Follows from `exists_spa_point_with_supp_ge_of_prime` (done, commit `fa74a49`) + valuation lifting through cover.

### Phase B: Discharge Phase A obligations from Tate hypotheses only

For `flat_over_base`: flatness of `presheafValue C.base → presheafValue D` as ring hom. 

**Via Example 6.38**: under the ring iso, this reduces to flatness of a map between Tate-algebra quotients. Since both are quotients of `A⟨X⟩` by principal ideals `(1-s·X)` (Lemma 8.31 gives flatness over A), the map between them is induced by the inclusion of ideals, which is flat.

But this needs the Example 6.38 iso's 4 hypotheses discharged. **Some are NOT automatic**:
- `hb_D : IsPowerBounded (invS D)` — needs `1 ∈ D.T`.
- `hA_complete : CompleteSpace A` — Tate rings aren't complete by default.
- `hnoeth`, `hT_pb` — require strong noetherian + T ⊆ A°.

### Phase C: Add missing completeness/normalization to tateAcyclicity's context

If Phase B can't discharge all hypotheses cleanly, we may need to:
- Add `[CompleteSpace A]` to tateAcyclicity (minor pollution — acceptable? User to decide).
- Work with a normalized cover where all D have `1 ∈ D.T`.

Alternatively:
- Use a DIFFERENT characterization of flatness that avoids the Example 6.38 iso.

### Phase D (alternative route): direct localization injectivity

`restrictionMapAlg D₀ D h : Localization.Away D₀.s → presheafValue D` is a LOCALIZATION (Prop 8.15). Localizations over flat bases are flat. Flat + faithfully-flat-cover gives injectivity on the whole.

## Tickets

### [T-WEDHORN-1] Verify Cor 8.32 hypothesis discharge under tateAcyclicity's instance bundle

**File**: `Adic spaces/Cor832.lean` + new proofs.
**Task**: Write
```lean
theorem productRestriction_injective_tate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (x : presheafValue C.base)
    (hx : ∀ D ∈ C.covers, restrictionMap C.base D (C.hsubset D hD) x = 0) :
  x = 0
```
Discharge the 2 abstract hypotheses (`flat_over_base`, `hSpa_surj`) internally.

**Obligation (a): flat_over_base**. For each D ∈ C.covers, `presheafValue D` is flat over `presheafValue C.base`. Use Prop 8.30 / Example 6.38 + some flat-composition. Check which extra hypotheses this needs.

**Obligation (b): hSpa_surj**. Use `exists_spa_point_with_supp_ge_of_prime` applied to every prime of `presheafValue C.base`, then use the COVERAGE property of C to map to some cover piece.

**Estimate**: 150-250 lines. This is the CRITICAL ticket — if this works, tateAcyclicity Part 1 closes.

### [T-WEDHORN-2] Reroute tateAcyclicity Part 1

**File**: `Adic spaces/LaurentRefinement.lean:3688-3696`.
**Task**: Replace the `restrictionMapHom_injective` call with `productRestriction_injective_tate` from T-WEDHORN-1.
**Estimate**: 20 lines.

### [T-WEDHORN-3] (optional) Close `restrictionMapHom_injective` proper

**File**: `Adic spaces/PresheafTateStructure.lean:1238`.
**Task**: Using the same infrastructure, derive single-map injectivity. May need additional argument (e.g., completing the cover `{D}` to `{D, D^c}`).
**Estimate**: 100-200 lines.

**Not required** for tateAcyclicity progress (T-WEDHORN-2 bypasses it).

## Execution order

1. **T-WEDHORN-1** — the critical piece, 150-250 lines.
2. **T-WEDHORN-2** — quick reroute, 20 lines, unlocks tateAcyclicity Part 1.
3. **T-WEDHORN-3** — nice-to-have cleanup, optional.

## Dependency graph

```
Cor832 abstract (done) ──────┐
                             │
Prop 6.18 (done) ─────┐      │
                      │      │
Example 6.38 iso ─────┴──────┼──> T-WEDHORN-1 (flat_over_base discharge)
                             │
Lemma 7.45 + spa_point ──────┼──> T-WEDHORN-1 (hSpa_surj discharge)
                             │
                             ▼
                       T-WEDHORN-1
                             │
                             ▼
                       T-WEDHORN-2
                             │
                             ▼
                  tateAcyclicity Part 1 CLOSED
```

## Expected outcome of this session

- T-WEDHORN-1 closed or blocker precisely identified.
- T-WEDHORN-2 closed (if T-WEDHORN-1 lands).
- **tateAcyclicity Part 1 CLOSED** — major milestone.
- `restrictionMapHom_injective` still sorry'd but DECOUPLED from tateAcyclicity path.

## Risk

- `flat_over_base` may still require non-trivial Prop 8.15 content.
- If unable to discharge `flat_over_base` cleanly, the reroute doesn't work and we're back to the original blocker.

## What NOT to do

- Do NOT add `[DiscreteTopology A]` — defeats purpose.
- Do NOT add `[IsDomain A]` — restrictive.
- Do NOT add `hZavyalov` — pollutes.
- Do NOT assume `MulArchimedean` globally — it's per-valuation in our Cor 7.32 port.
- Do NOT break existing signatures.
