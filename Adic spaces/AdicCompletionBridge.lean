/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a commutative ring `R` with an ideal `I` such that the topology on `R`
is the `I`-adic topology (`IsAdic I`), we construct a ring isomorphism:

  `UniformSpace.Completion R ≃+* AdicCompletion I R`

## Strategy

Since the topology is `I`-adic, the uniform structure on `R` is the `I`-adic
one. We equip `AdicCompletion I R` with the projective limit uniformity
(coarsest making each `eval n : AdicCompletion I R → R/(I^n)` uniformly
continuous with discrete target). Then:

1. Show `AdicCompletion.of I R : R → AdicCompletion I R` is a uniform
   inducing with dense range (AbstractCompletion axioms).
2. Use `AbstractCompletion.compareEquiv` for the uniform equivalence.
3. Prove multiplicativity by density + T₂.

## Key lemma

For `R` as a module over itself: `I^n • ⊤ = I^n`, so the quotients
`R/(I^n • ⊤)` used by `AdicCompletion` are exactly `R/I^n`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, §8.1
-/

universe u

namespace AdicCompletionBridge

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n • ⊤ = I^n`. This is the
identity that makes `AdicCompletion I R` use the correct filtration. -/
theorem ideal_smul_top_eq_self (n : ℕ) :
    (I ^ n • (⊤ : Submodule R R) : Submodule R R) = ↑(I ^ n) := by
  ext x; constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha r _ => ?_) (fun _ _ h1 h2 => ?_)
    · change a * r ∈ (I ^ n : Ideal R)
      exact Ideal.mul_mem_right r _ ha
    · exact (I ^ n).add_mem h1 h2
  · intro hx
    have : x = x • (1 : R) := (mul_one x).symm
    rw [this]
    exact Submodule.smul_mem_smul hx Submodule.mem_top

/-! ### Uniform structure on AdicCompletion -/

section UniformStructure

variable [IsTopologicalRing R] (hadic : IsAdic I)

/-- The uniform structure on `AdicCompletion I R` induced by the projective
limit: the coarsest uniformity making each evaluation map
`eval n : AdicCompletion I R → R/(I^n • ⊤)` uniformly continuous,
where each quotient carries the discrete uniformity. -/
noncomputable def adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  ⨅ n : ℕ, UniformSpace.comap (AdicCompletion.eval I R n) ⊥

/-- The topology on `AdicCompletion I R` from the projective limit uniformity. -/
noncomputable def adicCompletionTopology :
    TopologicalSpace (AdicCompletion I R) :=
  (adicCompletionUniformSpace I).toTopologicalSpace

-- TODO: instances (IsTopologicalAddGroup, T0Space, CompleteSpace)
-- TODO: IsUniformInducing, DenseRange for AdicCompletion.of
-- TODO: AbstractCompletion instance
-- TODO: compareEquiv → adicCompletionRingEquiv

end UniformStructure

end AdicCompletionBridge
