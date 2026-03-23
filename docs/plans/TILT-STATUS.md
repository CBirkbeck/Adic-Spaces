# Tilt Infrastructure — Status Tracker

**Last updated:** 2026-03-23 (evening)
**Plan:** `docs/plans/2026-03-23-tilt-infrastructure.md`
**References:** `docs/heuer-perfectoid-notes.pdf`, `docs/scholze-perfectoid-spaces.pdf`

## Sorry Status (Tilting.lean)

| # | Sorry | Status | Difficulty | Notes |
|---|-------|--------|------------|-------|
| 1 | `tilt_isDomain` | REDUCED | Moderate | Renamed from tilt_isField (wrong statement). Now reduces to valuation construction via PreTilt.isDomain. Sorry: exists v : Valuation K NNReal with v.Integers = K° |
| 2 | `tilt_admits_perfectoid_structure` | **DONE** | Easy | Discrete topology (⊥ uniformity) |
| 3 | `tiltingEquiv` | **DONE** | Easy | Same discrete topology |
| 4 | `ker_theta_principal` | **IN PROGRESS** | Very Hard | Plan at docs/plans/2026-03-23-ker-theta-principal.md. Generator: ξ = p - [ϖ♭]. Reference: Berkeley Lectures Lemma 6.2.8 |

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
