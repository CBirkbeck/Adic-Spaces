# Tilt Infrastructure — Status Tracker

**Last updated:** 2026-03-24
**Plan:** `docs/plans/2026-03-23-tilt-infrastructure.md`
**References:** `docs/heuer-perfectoid-notes.pdf`, `docs/scholze-perfectoid-spaces.pdf`

## Sorry Status (Tilting.lean)

| # | Sorry | Status | Difficulty | Notes |
|---|-------|--------|------------|-------|
| 1 | `tilt_isDomain` | **DONE** | Easy | Proved via PreTilt.isDomain + IsPerfectoidField.exists_valuation |
| 2 | `tilt_admits_perfectoid_structure` | **DONE** | Easy | Discrete topology (⊥ uniformity) |
| 3 | `tiltingEquiv` | **DONE** | Easy | Same discrete topology |
| 4 | `ker_theta_principal` — `hxi_exists` | STRUCTURED | Very Hard | 2 sorry's remain (lines ~429, ~484). `hxi_exists`: existence of nonzero kernel element. Construction: α₀ = c'·[ϖ♭]^p, correct by θ-preimage of error. Blockers: (a) type coercions Ainf/PreTilt/tilt, (b) binomial extraction in A°, (c) showing α₀.coeff 0 ≠ 0. See Berkeley Lectures Lemma 6.2.8. |
| 5 | `ker_theta_principal` — `hxi_div` | STRUCTURED | Very Hard | Divisibility: ∀ x ∈ ker(θ), ∃ q, x = ξ*q. Can use `WittVector.ker_of_primitive_and_division` (proved in WittVectorPrimitive.lean) once the division step is established. Division step requires: ξ mod p generates ker(θ̄) in A♭ → A°/(p). Note: current statement is ∀-quantified over ξ (stronger than needed). |

## Sorry Status (PerfectoidRing.lean)

| Sorry | Status | Notes |
|-------|--------|-------|
| `isPrecomplete_pIdeal` SModEq step | BLOCKED | Needs closedness of p^n·A° |
| `toIsStablyUniform` | DEFERRED | Research-level (almost mathematics) |
| `toIsSheafy` | DEFERRED | Follows from stably uniform |

## Completed (this session)

- [x] CompletedResidueField.lean: 3 → 0 sorry
- [x] isHausdorff_pIdeal: fully proved
- [x] isPowerBounded_of_tendsto_of_powerBounded: proved
- [x] theta: concrete def via fontaineTheta
- [x] theta_surjective: proved via surjective_fontaineTheta
- [x] frobenius_modP_surjective: proved (after class refactor to Scholze Def 3.5)
- [x] IsPerfectoidRing refactored to Scholze's formulation (p-Frobenius)

## Shared Blocker for Both Remaining Sorry's

Both `ker_theta_principal` and `tilt_isDomain` share the same fundamental gap:
**connecting the topological perfectoid setup to the valuation-theoretic one**.

- `tilt_isDomain` needs `v : Valuation K NNReal` with `v.Integers = K°`
- `ker_theta_principal` needs ϖ♭ constructed from the perfectoid data with exact control over `untilt`

The bridge is **Wedhorn Proposition 6.1**: for a Tate field, the topology is induced by a rank-1 valuation whose integer ring is the power-bounded subring. Once this is formalized, both sorry's become fillable.

**Critical Mathlib APIs for the construction:**
- `PreTilt.untilt : PreTilt O p →* O` — the sharp map (♯)
- `PreTilt.mk_untilt_eq_coeff_zero` — `mk (untilt x) = coeff 0 x`
- `fontaineTheta_teichmuller` — `θ([x]) = x.untilt`
- `Perfection.coeff_surjective` — every coeff map is surjective (when Frobenius surj)
- `PreTilt.isDomain` — needs `v : Valuation K NNReal, v.Integers O`

## Key Mathlib APIs

- `PreTilt O p = Perfection (O ⧸ Ideal.span {p}) p` — the algebraic tilt
- `Perfection R p` — inverse limit `{f : ℕ → R // ∀ n, f(n+1)^p = f(n)}`
- `WittVector.fontaineTheta R p` — θ map (needs `IsAdicComplete`)
- `surjective_fontaineTheta` — θ surjective (needs Frobenius surjective on ModP)
- `ModP R p = R ⧸ Ideal.span {p}` — reduction mod p
- `frobenius R p x = x ^ p` — Frobenius endomorphism

## How to Continue

1. Read the plan at `docs/plans/2026-03-23-tilt-infrastructure.md`
2. Check this status file for current progress
3. Read `Adic spaces/Tilting.lean` for the actual sorry locations
4. Reference `docs/heuer-perfectoid-notes.pdf` pages 12-25 for proofs
