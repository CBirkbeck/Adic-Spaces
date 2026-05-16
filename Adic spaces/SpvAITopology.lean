/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpvAI
import «Adic spaces».RationalSubsets

/-!
# Spectral structure on `Spv(A, I)` (Wedhorn 7.5) — T-SPV-AI-WEDHORN-710

Per Wedhorn 7.5 (p. 57–58): `Spv(A, I)` is a spectral space, and the
"rational subsets" `Spv(A,I)(T/s)` for `T ⊆ A` finite with `I ⊆ √(T·A)`
form a basis of quasi-compact open subsets stable under finite
intersection.

This is the topological infrastructure that bridges `Spv.IsInSpvAI`
(the algebraic disjunct from `SpvAI.lean`) to the Wedhorn 7.35 Spa
compactness statement.

## Main definitions

* `ValuationSpectrum.SpvAI A I` : the set `Spv(A, I)` as a subset of
  `Spv A`, equipped with the disjunctive condition `Spv.IsInSpvAI`.
* `ValuationSpectrum.SpvAI.rationalSubset T s` : the rational subset
  `Spv(A,I)(T/s)` per Wedhorn 7.5.

## Status

This file currently contains **only the definitional framework**. The
spectrality proof (Wedhorn 7.5 (1)) and the retraction continuity
(Wedhorn 7.5 (2)) are TODO; each is substantive (multi-step proof
using Proposition 3.31 / spectral-space machinery). See the per-
declaration docstrings for the proof plans.

## References

* [Wedhorn 2019] Section 7.1, Lemma 7.5 (p. 57–58), arXiv:1910.05934.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`Spv(A, I)` as a subset of `Spv A`.** -/
def SpvAI (A : Type*) [CommRing A] (I : Ideal A) : Set (Spv A) :=
  { v : Spv A | Spv.IsInSpvAI v I }

/-- **Rational subset `Spv(A, I)(T/s)` (Wedhorn 7.5).** For `T ⊆ A`
finite, `s ∈ A`, this is `{v ∈ Spv(A, I) : v(t) ≤ v(s) ≠ 0 ∀ t ∈ T}`. -/
def SpvAI.rationalSubset (I : Ideal A) (T : Finset A) (s : A) :
    Set (Spv A) :=
  SpvAI A I ∩ { v : Spv A | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 }

end ValuationSpectrum
