/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import «Adic spaces».HuberRings

/-!
# Noetherian Tate Module Topology (Wedhorn Prop 6.18)

We formalize the canonical topology on finitely generated modules over topological rings,
following §6.18 of [Wedhorn, *Adic Spaces*].

The key insight is that mathlib's `moduleTopology` (the finest topology making `M` a
topological `A`-module) coincides with the I-adic lattice topology from Wedhorn, and
already provides automatic continuity of linear maps and the open mapping theorem.

## Main definitions

* `IsStrictMap` : A continuous map between topological spaces is *strict* if it is open
  onto its image (i.e., it is an open map to `Set.range f` with the subspace topology).
* `IsStrictLinearMap` : Specialization for linear maps.

## Main results

* `IsModuleTopology.isOpenMap_of_surjective_of_finite` : Every surjective `A`-linear map
  between modules with module topology is open (the open mapping theorem, Prop 6.18(2)).
* `IsModuleTopology.isStrictLinearMap_surjective` : Every surjective `A`-linear map between
  modules with module topology is strict.
* `IsModuleTopology.strictExact` : In a short exact sequence of modules with module
  topology, the surjection is open and the injection is continuous (strict exactness).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 6.18, Remark 6.19
-/

open Filter Topology Pointwise

/-! ### Strict maps -/

/-- A continuous map `f : X → Y` is **strict** if it is open onto its image, i.e.,
the induced map `X → Set.range f` (with the subspace topology) is an open map. -/
def IsStrictMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  IsOpenMap (Set.rangeFactorization f)

/-- A linear map `f : M →ₗ[R] N` is **strict** if the underlying continuous map is
open onto its image. This is the notion of "strict morphism" in the theory of
topological modules. -/
def IsStrictLinearMap {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [TopologicalSpace M] [TopologicalSpace N] (f : M →ₗ[R] N) : Prop :=
  IsStrictMap f

/-- An open map is strict. -/
theorem isStrictMap_of_isOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenMap f) : IsStrictMap f := by
  intro U hU
  rw [isOpen_induced_iff]
  exact ⟨f '' U, hf U hU, by
    ext ⟨y, x, rfl⟩
    simp only [Set.rangeFactorization, Set.mem_preimage, Set.mem_image, Subtype.mk.injEq]⟩

/-- A strict surjective map is open. -/
theorem IsStrictMap.isOpenMap_of_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsStrictMap f) (hfs : Function.Surjective f) :
    IsOpenMap f := by
  intro U hU
  have h := hf U hU
  rw [isOpen_induced_iff] at h
  obtain ⟨V, hV, hVeq⟩ := h
  convert hV using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    have hmem : Set.rangeFactorization f x ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact ⟨x, hxU, rfl⟩
    exact hmem
  · intro hy
    obtain ⟨x, rfl⟩ := hfs y
    have hmem : (⟨f x, Set.mem_range_self x⟩ : Set.range f) ∈ Subtype.val ⁻¹' V :=
      hy
    rw [hVeq] at hmem
    obtain ⟨x', hx'U, hx'eq⟩ := hmem
    exact ⟨x', hx'U, congr_arg Subtype.val hx'eq⟩

/-- An open surjective linear map is strict. -/
theorem isStrictLinearMap_of_isOpenMap {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [TopologicalSpace M] [TopologicalSpace N] {f : M →ₗ[R] N}
    (hf : IsOpenMap f) : IsStrictLinearMap f :=
  isStrictMap_of_isOpenMap hf

/-! ### Module topology on finitely generated modules -/

section ModuleTopologyFG

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
variable {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]

omit [IsTopologicalRing A] in
/-- Every `A`-linear map from a module with module topology is continuous
(Prop 6.18(2) of Wedhorn, easy direction). -/
theorem IsModuleTopology.continuous_linearMap_of_finite [IsModuleTopology A M]
    [ContinuousAdd N] [ContinuousSMul A N] (f : M →ₗ[A] N) :
    Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
/-- Every surjective `A`-linear map between modules with module topology is open.
This is the **open mapping theorem** for module topologies (Prop 6.18(2) of Wedhorn). -/
theorem IsModuleTopology.isOpenMap_of_surjective_of_finite
    [IsModuleTopology A M] [IsModuleTopology A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) : IsOpenMap f :=
  (IsModuleTopology.isOpenQuotientMap_of_surjective (φ := f) hf).isOpenMap

omit [IsTopologicalRing A] in
/-- Every surjective `A`-linear map between modules with module topology is strict.
This follows immediately from the open mapping theorem. -/
theorem IsModuleTopology.isStrictLinearMap_surjective
    [IsModuleTopology A M] [IsModuleTopology A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) : IsStrictLinearMap f :=
  isStrictLinearMap_of_isOpenMap (IsModuleTopology.isOpenMap_of_surjective_of_finite f hf)

end ModuleTopologyFG

/-! ### I-adic lattice topology characterization (Prop 6.18) -/

section AdicLattice

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- An **`A₀`-lattice** in a module `M` is a finitely generated `A₀`-submodule that
generates `M` as an `A`-module. -/
structure IsLattice (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) : Prop where
  /-- The lattice is finitely generated over `A₀`. -/
  fg : M₀.FG
  /-- The lattice generates `M` over `A`. -/
  span_eq_top : Submodule.span A (M₀ : Set M) = ⊤

/-- The n-th lattice neighborhood: `I^n • M₀` as a submodule of `M`. -/
def latticeNhd (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) (n : ℕ) : Submodule P.A₀ M :=
  P.I ^ n • M₀

omit [IsTopologicalRing A] in
/-- The lattice neighborhoods `I^n • M₀` are antitone in `n`. -/
theorem latticeNhd_antitone (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) : Antitone (latticeNhd P M₀) := by
  intro m n hmn
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)

omit [IsTopologicalRing A] in
/-- `I^(n+m) • M₀ ≤ I^n • M₀` -/
theorem latticeNhd_add_le (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) (n m : ℕ) : latticeNhd P M₀ (n + m) ≤ latticeNhd P M₀ n :=
  latticeNhd_antitone P M₀ le_self_add

end AdicLattice

/-! ### Module topology on the ring itself -/

section RingModuleTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A topological ring `A` has `IsModuleTopology A A`. This is
`IsTopologicalSemiring.toIsModuleTopology` from mathlib. -/
example : IsModuleTopology A A := inferInstance

/-- For a finite type `ι`, the product `ι → A` has `IsModuleTopology A (ι → A)`.
This is `IsModuleTopology.instPi` from mathlib. -/
example (ι : Type*) [Finite ι] : IsModuleTopology A (ι → A) := inferInstance

end RingModuleTopology

/-! ### Neighborhood basis characterization -/

section NhdBasis

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The standard `A₀`-lattice in `Fin k → A` is `(A₀)^k`, the product of copies of `A₀`. -/
def stdLattice (P : PairOfDefinition A) (k : ℕ) : Submodule P.A₀ (Fin k → A) where
  carrier := Set.pi Set.univ (fun _ ↦ (P.A₀ : Set A))
  add_mem' ha hb := fun i _ ↦ P.A₀.add_mem (ha i trivial) (hb i trivial)
  zero_mem' := fun _ _ ↦ P.A₀.zero_mem
  smul_mem' r _ hx := fun i _ ↦ P.A₀.mul_mem r.2 (hx i trivial)

omit [IsTopologicalRing A] in
/-- Elements of the standard lattice are exactly tuples in `(A₀)^k`. -/
theorem mem_stdLattice_iff (P : PairOfDefinition A) {k : ℕ} {x : Fin k → A} :
    x ∈ stdLattice P k ↔ ∀ i, x i ∈ P.A₀ :=
  ⟨fun h i ↦ h i trivial, fun h i _ ↦ h i⟩

end NhdBasis

/-! ### Strict exact sequences -/

section StrictExact

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [Module A M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [TopologicalSpace M₂]
  [AddCommGroup M₃] [Module A M₃] [TopologicalSpace M₃]

omit [IsTopologicalRing A] in
/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules with module topology
is **strict exact**: `g` is an open map and `f` is continuous.
This is a consequence of Prop 6.18(2) (open mapping theorem). -/
theorem IsModuleTopology.strictExact
    [IsModuleTopology A M₁] [IsModuleTopology A M₂] [IsModuleTopology A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hg_surj : Function.Surjective g) :
    IsOpenMap g ∧ Continuous f := by
  have := IsModuleTopology.toContinuousAdd (R := A) (A := M₂)
  have := IsModuleTopology.toContinuousSMul (R := A) (A := M₂)
  exact ⟨IsModuleTopology.isOpenMap_of_surjective_of_finite g hg_surj,
         IsModuleTopology.continuous_of_linearMap f⟩

end StrictExact
