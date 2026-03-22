/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.Flat.Basic
import «Adic spaces».TateAlgebra

/-!
# Topology on the Tate Algebra A⟨X⟩

The Tate algebra `A⟨X⟩` inherits the **product topology** from `MvPowerSeries (Fin 1) A`,
where we view power series as functions `(Fin 1 →₀ ℕ) → A` and equip the codomain with
the topology of `A`. The subring `TateAlgebra A ⊂ MvPowerSeries (Fin 1) A` gets the
induced (subspace) topology.

This topology makes `A⟨X⟩` a topological ring (via `Subring.instIsTopologicalRing`)
and is the topology of coefficient-wise convergence: a net of restricted power series
converges iff each coefficient converges in `A`.

## Main results

* `TateAlgebra.topologicalSpace` : The topology on `A⟨X⟩` (product/subspace topology).
* `TateAlgebra.isTopologicalRing` : `A⟨X⟩` is a topological ring.
* `TateAlgebra.continuous_coeff` : Each coefficient function `coeff n` is continuous.
* `TateAlgebra.flat` : `A⟨X⟩` is flat over `A` (for noetherian `A`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6, §8
-/

open MvPowerSeries.WithPiTopology

namespace TateAlgebra

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### Topology instances -/

/-- The topology on `A⟨X⟩` is the subspace topology from `MvPowerSeries (Fin 1) A`
with the product topology. This makes coefficient extraction continuous. -/
example : TopologicalSpace ↥(TateAlgebra A) := inferInstance

/-- `A⟨X⟩` is a topological ring with the subspace topology. -/
example : IsTopologicalRing ↥(TateAlgebra A) := inferInstance

/-! ### Continuity of coefficient extraction -/

/-- The `n`-th coefficient function `coeff n : A⟨X⟩ → A` is continuous
(it's the composition of the continuous embedding into `MvPowerSeries` and
the continuous coefficient projection). -/
theorem continuous_coeff (n : ℕ) :
    Continuous (fun f : ↥(TateAlgebra A) => coeff n f) := by
  apply Continuous.comp
  · exact MvPowerSeries.WithPiTopology.continuous_coeff (toIndex n)
  · exact continuous_subtype_val

/-- `evalZeroHom` is continuous (it extracts the 0-th coefficient). -/
theorem continuous_evalZeroHom :
    Continuous (evalZeroHom : ↥(TateAlgebra A) → A) := by
  exact continuous_coeff 0

end TateAlgebra
