/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentCoverTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Pseudo-metrizability and BaireSpace support for the Laurent cover (T137 / T138)

Continuation of the T136 BaireSupport section in
`«Adic spaces».LaurentCoverTopology`. The Mathlib metrizability and
Baire APIs (`Mathlib.Topology.Metrizable.CompletelyMetrizable`,
`Mathlib.Topology.Baire.CompleteMetrizable`) significantly expand the
typeclass-instance database; importing them directly into
`LaurentCoverTopology.lean` would slow down `infer_instance`-based
proofs there (notably the T135 `laurentTateAlgebra_t2Space` proof
times out under the default `synthInstance.maxHeartbeats=20000`).

This module isolates the metrizability/Baire imports plus the
follow-up lemmas, keeping `LaurentCoverTopology.lean` lean enough
to compile under default heartbeat budgets.

## Lemmas delivered

T137 (B₂-side):

* `B₂_gen_completeSpace` — `CompleteSpace (B₂_gen f)` under the
  canonical right uniform structure, delegating to the existing
  `TateAlgebra.quotient_oneSubfXIdeal_completeSpace` (`B₂_gen f`'s
  ideal is definitionally `oneSubfXIdeal f`).
* `B₂_gen_isCompletelyPseudoMetrizableSpace` — completely
  pseudo-metrizable, via Mathlib's auto-instance
  `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
  fed by T136 `B₂_gen_uniformity_isCountablyGenerated` and
  `B₂_gen_completeSpace`.

T138 (B₁-side, consuming the upstream
`TateAlgebra.quotient_plusFSubXIdeal_completeSpace`):

* `B₁_gen_completeSpace` — analogous `CompleteSpace (B₁_gen f)`,
  delegating to the new
  `TateAlgebra.quotient_plusFSubXIdeal_completeSpace` declared
  upstream in `TateAlgebraTopology.lean`.
* `B₁_gen_isCompletelyPseudoMetrizableSpace` — completely
  pseudo-metrizable.

## Remaining steps (next-ticket scope)

* Product `B₁_gen f × B₂_gen f` is completely pseudo-metrizable
  (auto via Mathlib's `IsCompletelyPseudoMetrizableSpace.prod`).
* Closed kernel `↥(deltaMap_gen f).ker` is completely
  pseudo-metrizable via `IsClosed.isCompletelyPseudoMetrizableSpace`,
  using T134 `ker_deltaMap_gen_isClosed` and T135 `B₁₂_gen_t2Space`.
* `BaireSpace ↥(deltaMap_gen f).ker` via Mathlib's auto-instance
  `BaireSpace.of_completelyPseudoMetrizable`.
-/

namespace LaurentCover

open TateAlgebra LaurentTateAlgebra Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

open scoped Uniformity

section BaireSupport

variable [IsTateRing A] [T2Space A] [IsNoetherianRing A] [IsDomain A] (f : A)

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₂_gen f` is `CompleteSpace` under the canonical right uniform structure.

Delegates to the existing `TateAlgebra.quotient_oneSubfXIdeal_completeSpace`
(`B₂_gen f`'s ideal is definitionally `oneSubfXIdeal f`). -/
theorem B₂_gen_completeSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @CompleteSpace (B₂_gen f) (B₂_gen_uniformSpace f) :=
  quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth f

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₂_gen f` is completely pseudo-metrizable.
The Mathlib instance
`IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
fires from `[UniformSpace] [CompleteSpace] [IsCountablyGenerated 𝓤]`. -/
theorem B₂_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₂_gen f) := by
  haveI : Filter.IsCountablyGenerated (𝓤 (B₂_gen f)) :=
    B₂_gen_uniformity_isCountablyGenerated f
  haveI : CompleteSpace (B₂_gen f) := B₂_gen_completeSpace f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₁_gen f` is `CompleteSpace` under the canonical right uniform structure.

Delegates to the upstream `TateAlgebra.quotient_plusFSubXIdeal_completeSpace`
(`B₁_gen f`'s ideal is definitionally `plusFSubXIdeal f`). -/
theorem B₁_gen_completeSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @CompleteSpace (B₁_gen f) (B₁_gen_uniformSpace f) :=
  quotient_plusFSubXIdeal_completeSpace hA_complete hnoeth f

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₁_gen f` is completely pseudo-metrizable. -/
theorem B₁_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₁_gen f) := by
  haveI : Filter.IsCountablyGenerated (𝓤 (B₁_gen f)) :=
    B₁_gen_uniformity_isCountablyGenerated f
  haveI : CompleteSpace (B₁_gen f) := B₁_gen_completeSpace f hA_complete hnoeth
  infer_instance

end BaireSupport

end LaurentCover
