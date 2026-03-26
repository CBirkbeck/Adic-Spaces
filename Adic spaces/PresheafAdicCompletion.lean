/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicCompletionTransfer
import «Adic spaces».Presheaf

/-!
# Presheaf Value via Adic Completion of the Subring

For a rational localization datum `D`, the ring of definition `locSubring`
with ideal of definition `locIdeal` carries the `locIdeal`-adic topology.
By the bridge (`AdicCompletionBridge`), the completion of `locSubring`
is isomorphic to `AdicCompletion locIdeal locSubring`, and by the transfer
(`AdicCompletionTransfer`), this completion is flat over `locSubring`.

The full presheaf value `presheafValue D = Completion(Localization.Away D.s)`
is obtained from `Completion(locSubring)` by inverting the Tate unit.

## Main definitions

* `locSubringTopology` : The `locIdeal`-adic topology on `locSubring`.
* `locSubringIsAdic` : `IsAdic locIdeal` (by definition).
* `locSubring_completion_flat` : The completion of `locSubring` is flat.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

section LocSubringCompletion

variable (D : RationalLocData A)

/-- The `locIdeal`-adic topology on `locSubring`. -/
@[reducible]
noncomputable def locSubringTopology :
    TopologicalSpace (locSubring D.P D.T D.s) :=
  (locIdeal D.P D.T D.s).adicTopology

/-- The `locIdeal`-adic topology is a ring topology. -/
@[reducible]
noncomputable def locSubringIsTopologicalRing :
    @IsTopologicalRing (locSubring D.P D.T D.s) (locSubringTopology D) _ := by
  infer_instance

/-- `IsAdic locIdeal` on `locSubring` with the adic topology. By definition. -/
theorem locSubringIsAdic :
    @IsAdic (locSubring D.P D.T D.s) _ (locSubringTopology D) (locIdeal D.P D.T D.s) :=
  rfl

/-- The completion of `locSubring` (with `locIdeal`-adic topology) is flat
over `locSubring`, when `locSubring` is noetherian. -/
theorem locSubring_completion_flat [IsNoetherianRing (locSubring D.P D.T D.s)] :
    let J := locIdeal D.P D.T D.s
    letI : TopologicalSpace (locSubring D.P D.T D.s) := J.adicTopology
    letI : IsTopologicalRing (locSubring D.P D.T D.s) := inferInstance
    letI : UniformSpace (locSubring D.P D.T D.s) :=
      IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup (locSubring D.P D.T D.s) :=
      isUniformAddGroup_of_addCommGroup
    Module.Flat (locSubring D.P D.T D.s)
      (UniformSpace.Completion (locSubring D.P D.T D.s)) := by
  letI : TopologicalSpace (locSubring D.P D.T D.s) :=
    (locIdeal D.P D.T D.s).adicTopology
  letI : IsTopologicalRing (locSubring D.P D.T D.s) := inferInstance
  letI : UniformSpace (locSubring D.P D.T D.s) :=
    IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (locSubring D.P D.T D.s) :=
    isUniformAddGroup_of_addCommGroup
  exact AdicCompletionBridge.completion_flat (locIdeal D.P D.T D.s) rfl

end LocSubringCompletion

end ValuationSpectrum
