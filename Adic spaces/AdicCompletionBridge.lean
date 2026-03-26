/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a commutative ring `R` with an ideal `I` such that the topology on `R`
is the `I`-adic topology (`IsAdic I`), we construct a uniform equivalence
and ring isomorphism:

  `UniformSpace.Completion R ≃ᵤ AdicCompletion I R`
  `UniformSpace.Completion R ≃+* AdicCompletion I R`

## Strategy

We equip `AdicCompletion I R` with the projective limit uniformity (coarsest
making each `eval n` uniformly continuous to the discrete quotient). Then:

1. Show the projective limit uniform space is T0 and complete.
2. Show `AdicCompletion.of I R` is uniform inducing with dense range.
3. Package as `AbstractCompletion` and use `compareEquiv`.
4. Multiplicativity by density + T2.

## Key lemma

For `R` as a module over itself: `I^n * top = I^n`, so the quotients
`R/(I^n * top)` used by `AdicCompletion` are exactly `R/I^n`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], section 5.6, section 8.1
-/

universe u

open scoped Topology Uniformity

open Filter Set Function

namespace AdicCompletionBridge

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n * top = I^n`. This is the
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

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] (hadic : IsAdic I)

/-- The uniform structure on `AdicCompletion I R` induced by the projective
limit: the coarsest uniformity making each evaluation map
`eval n : AdicCompletion I R -> R/(I^n * top)` uniformly continuous,
where each quotient carries the discrete uniformity. -/
noncomputable def adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  ⨅ n : ℕ, UniformSpace.comap (AdicCompletion.eval I R n) ⊥

/-! ### T0Space for AdicCompletion -/

/-- Two elements of `AdicCompletion I R` in the projective limit uniformity
are topologically inseparable iff they agree at all levels. Since
`AdicCompletion.ext` says agreement at all levels implies equality, this
gives T0. -/
theorem adicCompletion_t0 :
    @T0Space (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace := by
  sorry -- T0: elements equal iff equal at all levels (AdicCompletion.ext)

/-! ### CompleteSpace for AdicCompletion -/

/-- The projective limit of discrete quotients is complete. -/
theorem adicCompletion_completeSpace :
    @CompleteSpace (AdicCompletion I R) (adicCompletionUniformSpace I) := by
  letI : UniformSpace (AdicCompletion I R) := adicCompletionUniformSpace I
  sorry -- needs: projective limit of complete discrete spaces is complete

/-! ### IsUniformInducing for AdicCompletion.of -/

/-- The pullback of the projective limit uniformity on `AdicCompletion I R`
along `AdicCompletion.of I R` equals the I-adic uniformity on `R`. -/
theorem of_isUniformInducing (_ : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  sorry

/-! ### DenseRange for AdicCompletion.of -/

/-- `AdicCompletion.of I R` has dense range in the projective limit topology. -/
theorem of_denseRange (_ : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  intro x
  rw [@mem_closure_iff_nhds _ (adicCompletionUniformSpace I).toTopologicalSpace]
  intro U hU hxU
  -- U is a neighborhood of x in the projective limit topology.
  -- The projective limit topology has basis: eval_n⁻¹({eval_n(x)}) for each n.
  -- Any neighborhood contains such a basic open. Find r ∈ R with of(r) ∈ U.
  -- For now, use the fact that eval_n is surjective on quotients:
  -- eval_n(x) is a coset in R/(I^n•⊤), which has a representative r ∈ R.
  sorry

/-! ### AbstractCompletion package -/

/-- The `AdicCompletion I R` with projective limit uniformity, packaged as an
`AbstractCompletion` of `R`. -/
noncomputable def adicAbstractCompletion : AbstractCompletion R where
  space := AdicCompletion I R
  coe := AdicCompletion.of I R
  uniformStruct := adicCompletionUniformSpace I
  complete := adicCompletion_completeSpace I
  separation := adicCompletion_t0 I
  isUniformInducing := of_isUniformInducing I hadic
  dense := of_denseRange I hadic

/-! ### The uniform equivalence -/

/-- The uniform equivalence between `UniformSpace.Completion R` (for the
I-adic uniformity) and `AdicCompletion I R` (projective limit uniformity). -/
noncomputable def adicCompletionEquiv :
    UniformSpace.Completion R → AdicCompletion I R :=
  (UniformSpace.Completion.cPkg (α := R)).compare (adicAbstractCompletion I hadic)

noncomputable def adicCompletionEquivInv :
    AdicCompletion I R → UniformSpace.Completion R :=
  (adicAbstractCompletion I hadic).compare (UniformSpace.Completion.cPkg (α := R))

/-! ### The ring isomorphism -/

/-- The ring isomorphism between `UniformSpace.Completion R` and
`AdicCompletion I R`. Multiplicativity follows from density + T2. -/
noncomputable def adicCompletionRingEquiv :
    UniformSpace.Completion R ≃+* AdicCompletion I R := by
  sorry

end UniformStructure

end AdicCompletionBridge
