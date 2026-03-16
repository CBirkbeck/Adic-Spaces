/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization project
-/
import «Adic spaces».HuberRings
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Order.Basic

/-!
# Restricted Power Series

This file defines restricted power series `A⟨T₁, …, Tₖ⟩` and the notion of a strongly
noetherian ring, following Wedhorn's *Adic Spaces*, §6.9.

## Main definitions

* `MvPowerSeries.IsRestricted`: A power series is **restricted** if its coefficients
  converge to `0` along the cofinite filter on multi-indices.
* `restrictedMvPowerSeriesSubring k A`: The subring of restricted power series in `k`
  variables over `A`, denoted `A⟨T₁, …, Tₖ⟩`.
* `IsStronglyNoetherian A`: A topological ring `A` is **strongly noetherian** if
  `restrictedMvPowerSeriesSubring k A` is noetherian for all `k ≥ 0`
  (Definition 6.9 of Wedhorn).

## Implementation notes

The restricted power series ring is defined as a subring of `MvPowerSeries (Fin k) A`
(the formal power series ring), cut out by the condition that coefficients tend to `0`.
This is the canonical concrete definition; the opaque/axiom-based placeholders in the
Scottish Book problem files are replaced by imports from this module.

The closure of the restricted power series under multiplication (convolution) requires
that `A` is a topological ring. The proof that the convolution of two sequences tending
to `0` also tends to `0` is currently left as `sorry`.
-/

open Filter

universe u

/-! ### Restricted power series -/

/-- An element `f` of the multivariate power series ring `A⦃X₁, …, Xₖ⦄` is **restricted**
if its coefficients converge to `0` along the cofinite filter on multi-indices. That is,
for every open neighborhood `U` of `0` in `A`, all but finitely many coefficients of `f`
lie in `U`. This is the defining property of elements of `A⟨T₁, …, Tₖ⟩`.

See Wedhorn, §6.9. -/
def MvPowerSeries.IsRestricted {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    (f : MvPowerSeries (Fin k) A) : Prop :=
  Tendsto (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) cofinite (nhds 0)

/-- The set of restricted power series forms a subring of `MvPowerSeries (Fin k) A`.

The closure under multiplication (convolution of tendsto-0 coefficient sequences)
requires that `A` is a topological ring. This is the canonical definition of
`A⟨T₁, …, Tₖ⟩` (Wedhorn, §6.9). -/
def restrictedMvPowerSeriesSubring (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Subring (MvPowerSeries (Fin k) A) where
  carrier := {f | MvPowerSeries.IsRestricted f}
  zero_mem' := by
    change Tendsto _ cofinite (nhds 0)
    simp only [map_zero]
    exact tendsto_const_nhds
  one_mem' := by
    change Tendsto _ cofinite (nhds 0)
    apply tendsto_nhds.mpr
    intro U hU h0U
    rw [Filter.mem_cofinite]
    apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hs (by rw [MvPowerSeries.coeff_one, if_neg h]; exact h0U)
  add_mem' {f g} hf hg := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s => MvPowerSeries.coeff s f + MvPowerSeries.coeff s g)
        cofinite (nhds 0) := by
      rw [show (0 : A) = 0 + 0 from (add_zero 0).symm]
      exact hf.add hg
    exact this.congr (fun s => by simp [map_add])
  neg_mem' {f} hf := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s => -(MvPowerSeries.coeff s f)) cofinite (nhds 0) := by
      rw [show (0 : A) = -0 from neg_zero.symm]
      exact hf.neg
    exact this.congr (fun s => by simp [map_neg])
  mul_mem' {f g} hf hg := by
    change Tendsto _ cofinite (nhds 0)
    -- The convolution of two coefficient sequences tending to 0 also tends to 0.
    -- This uses: for topological rings, multiplication is continuous, so products of
    -- terms tending to 0 tend to 0, and finite sums preserve this.
    sorry

/-! ### Algebra instance -/

/-- Constant power series are restricted: the `algebraMap` image of any `a : A` has
coefficient `a` at multi-index `0` and `0` elsewhere, so it trivially tends to `0`. -/
theorem MvPowerSeries.IsRestricted_algebraMap {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] (a : A) :
    MvPowerSeries.IsRestricted (algebraMap A (MvPowerSeries (Fin k) A) a) := by
  change Tendsto _ cofinite (nhds 0)
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg h]; exact h0U)

/-- The restricted power series subring inherits an `A`-algebra structure from the
`MvPowerSeries` algebra instance, since constant power series are restricted. -/
noncomputable instance restrictedMvPowerSeriesSubring.instAlgebra (k : ℕ) (A : Type*)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Algebra A (restrictedMvPowerSeriesSubring k A) :=
  RingHom.toAlgebra
    { toFun := fun a => ⟨algebraMap A (MvPowerSeries (Fin k) A) a,
        MvPowerSeries.IsRestricted_algebraMap a⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }

/-! ### Strongly noetherian rings -/

/-- A topological ring `A` is **strongly noetherian** if the ring of restricted power series
`A⟨T₁, …, Tₖ⟩` is noetherian for all `k ≥ 0` (Definition 6.9 of Wedhorn).

This is a fundamental finiteness condition in nonarchimedean geometry, introduced by
Huber. For a noetherian Tate ring, being strongly noetherian is equivalent to saying
that the theory of formal models is well-behaved. -/
class IsStronglyNoetherian (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Prop where
  /-- The restricted power series ring in `k` variables is noetherian for all `k`. -/
  isNoetherianRing_restricted : ∀ k : ℕ,
    IsNoetherianRing (restrictedMvPowerSeriesSubring k A)
