/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

/-!
# Rational chain decomposition (Wedhorn Lemma 2.13 via iteration)

For any pair of rational locales `E, D : RationalLocData A` with
`rationalOpen D.T D.s ⊆ rationalOpen E.T E.s`, construct a finite chain of
basic Laurent plus/minus steps that starts at E and ends at a locale whose
rationalOpen equals D's:

```
E = L₀ → L₁ → L₂ → ⋯ → L_n = chainEnd
```

with `L₁ = laurentMinusDatum E D.s` (basic minus step inverting D.s) and
`L_{k+2} = laurentPlusDatum L_{k+1} t_k` for `t_k` enumerating `D.T` (basic
plus steps adding power-bounded T elements).

This decomposition realises the reviewer-recommended (session 3, ChatGPT Pro
2026-05-11) proof of general rational-restriction flatness:
1. Each basic Laurent step is flat (depth-1 theorems
   `restrictionMap_flat_via_fSubX_quotient`,
   `restrictionMap_flat_via_oneSubfX_quotient`).
2. Composition of flat maps along the chain (`Module.Flat.comp`) gives
   `presheafValue E → presheafValue chainEnd` flat.
3. `chainEnd`'s rationalOpen equals D's, so `presheafValue chainEnd ≃+*
   presheafValue D` (transfer flatness).

## Main definitions

* `rationalChain E D hsub` — the finite list of intermediate rational locales.
* `rationalChainEnd E D hsub` — the last locale in the chain.

## Main theorems (deferred to sibling tickets)

* `rationalChainEnd_rationalOpen_eq` — chainEnd's rationalOpen equals D's.
* `rationalChainStep_flat` — each chain step is flat.
* `rationalChainComposite_flat` — the composition is flat.

## References

* [Wedhorn 2019] Lemma 2.13 (transitivity of rational localizations).
* Reviewer (ChatGPT Pro, 2026-05-11 session 3): "Build [the general flatness
  theorem] from the two basic flatness steps plus transitivity/decomposition
  of rational localizations."
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Chain construction

The chain is built in two phases:
* Phase 1 (single minus step): `L₁ := laurentMinusDatum E D.s`. This inverts
  `D.s` over E's topology — the resulting locale has `s = E.s * D.s`.
* Phase 2 (plus steps, one per `t ∈ D.T`): iteratively add each `t ∈ D.T`
  as a plus generator.

`D.T` is a `Finset A`; we use `Finset.toList` to fix an enumeration. -/

/-- The list of `D.T` elements, in some fixed enumeration. Used as the
sequence of plus steps in the chain. -/
noncomputable def chainPlusElements (D : RationalLocData A) : List A :=
  D.T.toList

/-- Iteratively apply `laurentPlusDatum` for each element of a list. Used to
add the plus steps for `D.T` to an intermediate locale. -/
noncomputable def applyPlusList (L : RationalLocData A) :
    List A → RationalLocData A
  | [] => L
  | t :: ts => applyPlusList (laurentPlusDatum L t) ts

/-- The chain end: starting from `E`, take a minus step at `D.s`, then apply
plus steps for each element of `D.T`. -/
noncomputable def rationalChainEnd (E D : RationalLocData A) :
    RationalLocData A :=
  applyPlusList (laurentMinusDatum E D.s) (chainPlusElements D)

end ValuationSpectrum
