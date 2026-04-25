/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

/-!
# Lifting algebraic Laurent separation to the presheafValue level (R2)

The companion to `laurentCover_gluing_presheaf_viaRow3`
(`LaurentRefinement.lean:3527`) for the **separation** direction of the
Laurent row.

## What this gives

`LaurentCoverExact.lean:380` proves the algebraic Laurent diagonal
`ε : A → B₁_gen f × B₂_gen f` is injective whenever
`⨅ n, span {f}^n = ⊥` in `A` (Krull intersection at `f`). This file
applies that result at `A := presheafValue D₀, f := D₀.canonicalMap f`,
threading the same `(τ_plus, τ_minus, htau_plus, htau_minus)` bridge
data the gluing companion uses, to derive presheafValue-level Laurent
separation:

  Two `presheafValue D₀` sections agreeing on both `presheafValue
  (laurentPlusDatum D₀ f)` and `presheafValue (laurentMinusDatum D₀ f)`
  via restriction must be equal.

The single new caller residual versus the gluing companion is the
**Krull intersection hypothesis** `hInf` at the presheafValue base —
discharged downstream from completion / topological-nilpotence inputs.

## Why this is the R2 direction

Wedhorn's Lemma 8.33 row `0 → A →ε B₁ × B₂ →δ B₁₂ → 0` decomposes into:
- δ-surjectivity + ker-δ ⊆ im-ε → **gluing** (Lane A's existing
  `laurentCover_gluing_presheaf_via*` chain via `row3_exact`).
- ε-injectivity → **separation** (this file).

Both halves use the same `(τ_plus, τ_minus)` bridges, so the cost of
this file is just the Krull-intersection hypothesis. No new
faithful-flatness / Cor 8.32 / Jacobson content; ε-injectivity is the
purely algebraic Krull route.

## References

* `Adic spaces/LaurentCoverExact.lean:380` —
  `LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot`
  (the algebraic separation core consumed here).
* `Adic spaces/LaurentRefinement.lean:3527` —
  `laurentCover_gluing_presheaf_viaRow3`
  (gluing companion, mirror structure).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- **R2 / presheafValue Laurent separation companion** to
`laurentCover_gluing_presheaf_viaRow3`.

Given the same `(τ_plus, τ_minus, htau_plus, htau_minus)` bridge data
plus a Krull-intersection hypothesis `hInf` on `D₀.canonicalMap f` in
`presheafValue D₀`, two `presheafValue D₀` sections that agree after
restriction to both Laurent halves must be equal.

The proof composes:

1. `htau_plus` / `htau_minus` — translate the restriction equalities
   into equalities of the first / second components of
   `LaurentCover.epsilonHom_gen (D₀.canonicalMap f)` at `a, b`.
2. `LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot` — the
   algebraic ε-injectivity, applied at `A := presheafValue D₀`,
   `f := D₀.canonicalMap f`.

No new sorries, no faithful-flatness, no Cor 8.32. The Krull
hypothesis `hInf` is the single explicit residual; it is the analytic
content already isolated as the "R2" content in
`LaurentCoverExact.lean:1890-1908`. -/
theorem laurentCover_separation_presheaf_viaRow3
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) (f : A)
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (hInf : (⨅ n : ℕ,
        Ideal.span ({D₀.canonicalMap f} : Set (presheafValue D₀)) ^ n) = ⊥)
    {a b : presheafValue D₀}
    (h_plus : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus a =
      restrictionMap D₀ (laurentPlusDatum D₀ f) hplus b)
    (h_minus : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus a =
      restrictionMap D₀ (laurentMinusDatum D₀ f) hminus b) :
    a = b := by
  -- Apply ε-injectivity at the bridged base.
  apply LaurentCover.epsilonHom_gen_injective_of_iInf_pow_eq_bot
    (A := presheafValue D₀) (D₀.canonicalMap f) hInf
  -- Reduce to component-wise equality.
  apply Prod.ext
  · -- First component: via τ_plus and h_plus.
    have ha := htau_plus a
    have hb := htau_plus b
    rw [← ha, ← hb, h_plus]
  · -- Second component: via τ_minus and h_minus.
    have ha := htau_minus a
    have hb := htau_minus b
    rw [← ha, ← hb, h_minus]

end ValuationSpectrum
