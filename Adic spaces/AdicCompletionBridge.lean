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
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a commutative ring `R` with an ideal `I` such that the topology on `R`
is the `I`-adic topology (`IsAdic I`), we construct a ring isomorphism:

  `UniformSpace.Completion R ≃+* AdicCompletion I R`

## Strategy

`AdicCompletion I R` is a subtype of `∀ n, R ⧸ (I^n • ⊤)`. We put the
discrete uniformity on each quotient and the product uniformity on the Pi
type. `AdicCompletion` inherits the subtype uniformity. Then:

1. The product of discrete spaces is T₂ and complete.
2. `AdicCompletion` is a closed subtype → T₂ and complete.
3. `AdicCompletion.of I R` is uniform inducing with dense range.
4. Package as `AbstractCompletion`, use `compareEquiv`.
5. Multiplicativity by density + T₂.
-/

universe u

open scoped Topology Uniformity

open Filter Set Function

namespace AdicCompletionBridge

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n • ⊤ = I^n`. -/
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

/-! ### Discrete topology on quotients -/

/-- Discrete topology on `R ⧸ (I^n • ⊤)`. -/
noncomputable instance quotientDiscreteTopology (n : ℕ) :
    TopologicalSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

noncomputable instance quotientDiscreteUniformSpace (n : ℕ) :
    UniformSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

instance quotientDiscreteUnif (n : ℕ) :
    DiscreteUniformity (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-! ### Topology and uniformity on AdicCompletion via subtype of product -/

section Instances

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The uniform structure on `AdicCompletion I R`: the subtype uniformity
from the product `∀ n, R ⧸ (I^n • ⊤)` with discrete factors. -/
noncomputable instance adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  instUniformSpaceSubtype

/-- `AdicCompletion I R` is T₀ because elements agreeing at all levels are equal. -/
instance adicCompletionT0 : @T0Space (AdicCompletion I R)
    (adicCompletionUniformSpace I).toTopologicalSpace := by
  constructor
  intro ⟨f, hf⟩ ⟨g, hg⟩ hinsep
  ext n
  -- Inseparable in subtype → inseparable in Pi → pointwise inseparable → equal (discrete)
  have hpi : @Inseparable _ Pi.topologicalSpace
      (⟨f, hf⟩ : AdicCompletion I R).val (⟨g, hg⟩ : AdicCompletion I R).val :=
    Inseparable.map hinsep continuous_subtype_val
  rw [@inseparable_pi] at hpi
  exact (hpi n).eq

/-- The set underlying `AdicCompletion I R` inside the product type. -/
private def adicCompletionSet :
    Set (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) :=
  {f | ∀ {m n : ℕ} (hmn : m ≤ n),
    (AdicCompletion.transitionMap I R hmn) (f n) = f m}

private theorem adicCompletionSet_isClosed : IsClosed (adicCompletionSet I) := by
  unfold adicCompletionSet
  have : {g : ∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R)) |
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (AdicCompletion.transitionMap I R hmn) (g n) = g m} =
    ⋂ (p : ℕ × ℕ) (_ : p.1 ≤ p.2),
      {g | (AdicCompletion.transitionMap I R ‹p.1 ≤ p.2›) (g p.2) = g p.1} := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h p hp => h hp, fun h m n hmn => h ⟨m, n⟩ hmn⟩
  rw [this]
  exact isClosed_iInter fun ⟨m, n⟩ => isClosed_iInter fun hmn =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n))
      (continuous_apply m)

/-- `AdicCompletion I R` is complete: it's a closed subtype of the complete
product `∀ n, R ⧸ (I^n • ⊤)` (product of discrete = complete). -/
instance adicCompletionComplete : @CompleteSpace (AdicCompletion I R)
    (adicCompletionUniformSpace I) :=
  (adicCompletionSet_isClosed I).completeSpace_coe

end Instances

section Bridge

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- `AdicCompletion.of I R` is uniform inducing for the I-adic uniformity
on `R` and the subtype uniformity on `AdicCompletion I R`. -/
theorem of_isUniformInducing (hadic : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  sorry

/-- `AdicCompletion.of I R` has dense range in the subtype topology. -/
theorem of_denseRange (hadic : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  sorry

/-- `AdicCompletion I R` with subtype uniformity as an `AbstractCompletion`. -/
noncomputable def adicAbstractCompletion (hadic : IsAdic I) : AbstractCompletion R where
  space := AdicCompletion I R
  coe := AdicCompletion.of I R
  uniformStruct := adicCompletionUniformSpace I
  complete := adicCompletionComplete I
  separation := adicCompletionT0 I
  isUniformInducing := of_isUniformInducing I hadic
  dense := of_denseRange I hadic

/-- Forward comparison: `Completion R → AdicCompletion I R`. -/
noncomputable def adicCompletionEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R → AdicCompletion I R :=
  (UniformSpace.Completion.cPkg (α := R)).compare (adicAbstractCompletion I hadic)

/-- Backward comparison: `AdicCompletion I R → Completion R`. -/
noncomputable def adicCompletionEquivInv (hadic : IsAdic I) :
    AdicCompletion I R → UniformSpace.Completion R :=
  (adicAbstractCompletion I hadic).compare (UniformSpace.Completion.cPkg (α := R))

/-- The ring isomorphism `Completion R ≃+* AdicCompletion I R`. -/
noncomputable def adicCompletionRingEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R ≃+* AdicCompletion I R := by
  sorry

end Bridge

end AdicCompletionBridge
