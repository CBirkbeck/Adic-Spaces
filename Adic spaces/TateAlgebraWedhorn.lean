/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».TateAlgebraTopology
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# T-topology on the Tate Algebra (Wedhorn, Definition 5.48)

For an element `f` in a nonarchimedean topological ring `A`, the **T-topology** on
the restricted power series ring `A⟨X⟩` (with `T = {f}`) has neighborhoods of `0`
of the form `{g ∈ A⟨X⟩ : f^n · coeff_n(g) ∈ U for all n}` where `U` ranges over
neighborhoods of `0` in `A`.

## Implementation

The T-topology is defined as the **induced topology** via the ring endomorphism
`scaleHom f : A[[X]] → A[[X]]` that sends `g(X)` to `g(fX)`, i.e., multiplies the
`n`-th coefficient by `f^n`. Since this is a ring homomorphism and the target carries
the product topology (which is a ring topology), the induced topology is automatically
a ring topology.

## Main definitions

* `TateAlgebraWedhorn.scaleHom f` : The ring endomorphism `g(X) ↦ g(fX)` on
  `MvPowerSeries (Fin 1) A`.
* `TateAlgebraWedhorn.scaleIncl f` : The composition of `scaleHom f` with the
  subtype inclusion `TateAlgebra A ↪ MvPowerSeries (Fin 1) A`.
* `TateAlgebraWedhorn.tateTopologyT f` : The T-topology on `TateAlgebra A`.

## Main results

* `tateTopologyT_isTopologicalRing` : The T-topology is a ring topology
  (Proposition 5.49(2) of Wedhorn).
* `tateTopologyT_nonarchimedean` : The T-topology is nonarchimedean.
* `tateTopologyT_continuous_scaledCoeff` : Each scaled coefficient
  `g ↦ f^n · coeff_n(g)` is continuous for the T-topology.
* `tateTopologyT_continuous_algebraMap` : The constant series embedding is continuous.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 5.48, Proposition 5.49
-/

open MvPowerSeries Filter Topology

universe u

namespace TateAlgebraWedhorn

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! ### The scaling ring endomorphism -/

/-- The scaling ring endomorphism on `MvPowerSeries (Fin 1) A`: sends `g(X)` to
`g(fX)`, i.e., multiplies the coefficient at multi-index `s` by `f^(s 0)`. This
is the substitution `X ↦ fX` (Wedhorn, §5.48). -/
noncomputable def scaleHom (f : A) :
    MvPowerSeries (Fin 1) A →+* MvPowerSeries (Fin 1) A where
  toFun g s := f ^ (s 0) * g s
  map_zero' := funext fun _ => mul_zero _
  map_one' := funext fun s => by
    change f ^ (s 0) * (1 : MvPowerSeries (Fin 1) A) s =
      (1 : MvPowerSeries (Fin 1) A) s
    rw [show (1 : MvPowerSeries (Fin 1) A) s =
      MvPowerSeries.coeff s 1 from rfl, MvPowerSeries.coeff_one]
    split
    · rename_i h; subst h; simp
    · ring
  map_add' _ _ := funext fun _ => mul_add _ _ _
  map_mul' g h := funext fun s => by
    classical
    let φ : MvPowerSeries (Fin 1) A := fun s => f ^ (s 0) * g s
    let ψ : MvPowerSeries (Fin 1) A := fun s => f ^ (s 0) * h s
    change f ^ (s 0) * MvPowerSeries.coeff s (g * h) =
      MvPowerSeries.coeff s (φ * ψ)
    rw [MvPowerSeries.coeff_mul (φ := g) (ψ := h),
        MvPowerSeries.coeff_mul (φ := φ) (ψ := ψ), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    change f ^ (s 0) * (g p.1 * h p.2) =
      (f ^ (p.1 0) * g p.1) * (f ^ (p.2 0) * h p.2)
    have : p.1 0 + p.2 0 = s 0 := by
      rw [← Finsupp.add_apply, Finset.mem_antidiagonal.mp hp]
    calc f ^ (s 0) * (g p.1 * h p.2)
        = f ^ (p.1 0 + p.2 0) * (g p.1 * h p.2) := by rw [this]
      _ = _ := by rw [pow_add]; ring

omit [TopologicalSpace A] [NonarchimedeanRing A] in
@[simp]
theorem scaleHom_apply (f : A) (g : MvPowerSeries (Fin 1) A)
    (s : Fin 1 →₀ ℕ) :
    scaleHom f g s = f ^ (s 0) * g s := rfl

/-- The composition of `scaleHom f` with the subtype inclusion
`TateAlgebra A ↪ A[[X]]`. This is the ring homomorphism used to define the
T-topology via the induced topology. -/
noncomputable def scaleIncl (f : A) :
    ↥(TateAlgebra A) →+* MvPowerSeries (Fin 1) A :=
  (scaleHom f).comp (TateAlgebra A).subtype

theorem scaleIncl_apply (f : A) (g : ↥(TateAlgebra A))
    (s : Fin 1 →₀ ℕ) :
    scaleIncl f g s = f ^ (s 0) * g.val s := rfl

/-! ### The T-topology -/

/-- The T-topology on `TateAlgebra A` for `T = {f}`, where neighborhoods of `0`
are `{g ∈ A⟨X⟩ : f^n · coeff_n(g) ∈ U for all n}` for open sets `U` of `A`.
Defined as the topology induced by `scaleIncl f` from the product topology on
`MvPowerSeries (Fin 1) A` (Definition 5.48 of Wedhorn). -/
@[reducible]
noncomputable def tateTopologyT (f : A) :
    TopologicalSpace ↥(TateAlgebra A) :=
  TopologicalSpace.induced (scaleIncl f)
    (WithPiTopology.instTopologicalSpace A)

/-! ### Ring topology -/

section RingTopology

variable (f : A)

private theorem scaleIncl_neg_comm :
    ((scaleIncl f) ∘ (- · : ↥(TateAlgebra A) → ↥(TateAlgebra A))) =
    ((- ·) ∘ (scaleIncl f)) := by
  ext x s
  change f ^ (s 0) * ((-x : ↥(TateAlgebra A)).val) s =
    -(f ^ (s 0) * x.val s)
  rw [NegMemClass.coe_neg,
      show (-x.val) s = -(x.val s) from rfl, mul_neg]

/-- The T-topology is a ring topology (Proposition 5.49(2) of Wedhorn).
This follows from the fact that it is the induced topology via the ring
homomorphism `scaleIncl f` from the product topology, which is already
a ring topology. -/
theorem tateTopologyT_isTopologicalRing :
    @IsTopologicalRing ↥(TateAlgebra A) (tateTopologyT f) _ := by
  letI τ_prod : TopologicalSpace (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instTopologicalSpace A
  haveI : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  letI : TopologicalSpace ↥(TateAlgebra A) := tateTopologyT f
  haveI hind : Topology.IsInducing (scaleIncl f) := ⟨rfl⟩
  haveI : ContinuousMul ↥(TateAlgebra A) :=
    continuousMul_induced (scaleIncl f)
  haveI : ContinuousAdd ↥(TateAlgebra A) :=
    continuousAdd_induced (scaleIncl f)
  haveI : ContinuousNeg ↥(TateAlgebra A) := by
    constructor; rw [hind.continuous_iff]
    change Continuous ((scaleIncl f) ∘ (- ·))
    rw [scaleIncl_neg_comm]
    exact continuous_neg.comp continuous_induced_dom
  exact
    { continuous_add := continuous_add
      continuous_mul := continuous_mul
      continuous_neg := continuous_neg }

end RingTopology

/-! ### Nonarchimedean property -/

/-- The T-topology is nonarchimedean (Proposition 5.49(2) of Wedhorn).
For any neighborhood of `0`, there exists an open additive subgroup inside it.
This follows because the T-topology is induced from the product topology on
`MvPowerSeries`, which has a nonarchimedean structure inherited from `A`. -/
theorem tateTopologyT_nonarchimedean (f : A) :
    @NonarchimedeanRing ↥(TateAlgebra A) _ (tateTopologyT f) := by
  letI : TopologicalSpace (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instTopologicalSpace A
  haveI : IsTopologicalRing (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instIsTopologicalRing (Fin 1) A
  letI : TopologicalSpace ↥(TateAlgebra A) := tateTopologyT f
  haveI := tateTopologyT_isTopologicalRing f
  constructor
  intro U hU
  -- Unfold the induced topology nhds of 0.
  rw [@nhds_induced _ _ (WithPiTopology.instTopologicalSpace A)
      (scaleIncl f) 0, mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  rw [map_zero] at hW
  -- W is a nhd of 0 in the Pi topology. Decompose via mem_pi.
  change W ∈ @nhds _
    (@Pi.topologicalSpace (Fin 1 →₀ ℕ) (fun _ => A) (fun _ => ‹_›)) 0
    at hW
  rw [nhds_pi] at hW
  simp only [show ∀ i : Fin 1 →₀ ℕ,
    (0 : (Fin 1 →₀ ℕ) → A) i = (0 : A) from fun _ => rfl] at hW
  obtain ⟨I, hI_fin, t, ht, hIt⟩ := mem_pi.mp hW
  -- For each i ∈ I, find an open additive subgroup of A inside t i.
  -- Use a single V that works for all i ∈ I by taking a finite infimum.
  -- First, for each i, pick a subgroup inside t i.
  have hVi : ∀ i : Fin 1 →₀ ℕ,
      ∃ Vi : OpenAddSubgroup A, (Vi : Set A) ⊆ t i := fun i =>
    NonarchimedeanRing.is_nonarchimedean (t i) (ht i)
  choose Vi hVi using hVi
  -- The preimage scaleIncl⁻¹(I.pi Vi) is an open additive subgroup.
  refine ⟨{
    toAddSubgroup :=
      { carrier := (scaleIncl f) ⁻¹' (I.pi (fun i => (Vi i : Set A)))
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_preimage] at ha hb ⊢
          intro i hi
          change (scaleIncl f (a + b)) i ∈ _
          rw [map_add]
          change (scaleIncl f a) i + (scaleIncl f b) i ∈ _
          exact (Vi i).toAddSubgroup.add_mem (ha i hi) (hb i hi)
        zero_mem' := by
          simp only [Set.mem_preimage, map_zero]
          intro i _; exact (Vi i).toAddSubgroup.zero_mem
        neg_mem' := fun {a} ha => by
          simp only [Set.mem_preimage] at ha ⊢
          intro i hi
          change scaleIncl f (-a) i ∈ _
          rw [map_neg]
          exact (Vi i).toAddSubgroup.neg_mem (ha i hi) }
    isOpen' :=
      (isOpen_set_pi hI_fin fun i _ => (Vi i).isOpen).preimage
        continuous_induced_dom
  }, ?_⟩
  -- Show this open additive subgroup is contained in U.
  intro g hg
  apply hWU
  apply hIt
  intro i hi
  exact hVi i (hg i hi)

/-! ### Continuous coefficient extraction -/

/-- Each scaled coefficient `g ↦ f^n · coeff_n(g)` is continuous for the
T-topology. This is because it is the composition of `scaleIncl f` (which is
continuous by definition of the induced topology) with the continuous
projection `π_{toIndex n}` from the product topology. -/
theorem tateTopologyT_continuous_scaledCoeff (f : A) (n : ℕ) :
    @Continuous _ _ (tateTopologyT f) _
      (fun g : ↥(TateAlgebra A) =>
        f ^ n * TateAlgebra.coeff n g) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := tateTopologyT f
  letI : TopologicalSpace (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instTopologicalSpace A
  -- The map equals π_{toIndex n} ∘ scaleIncl f.
  have h : (fun g : ↥(TateAlgebra A) =>
      f ^ n * TateAlgebra.coeff n g) =
    (fun φ : MvPowerSeries (Fin 1) A =>
      φ (TateAlgebra.toIndex n)) ∘ (scaleIncl f) := by
    ext g
    simp only [Function.comp, scaleIncl_apply]
    congr 1
    simp [TateAlgebra.toIndex, Finsupp.single_eq_same]
  rw [h]
  exact (WithPiTopology.continuous_coeff A
    (TateAlgebra.toIndex n)).comp continuous_induced_dom

/-- The constant series embedding `algebraMap A (TateAlgebra A)` is continuous
when `A⟨X⟩` carries the T-topology and `A` carries its own topology. -/
theorem tateTopologyT_continuous_algebraMap (f : A) :
    @Continuous _ _ _ (tateTopologyT f)
      (algebraMap A ↥(TateAlgebra A)) := by
  letI : TopologicalSpace ↥(TateAlgebra A) := tateTopologyT f
  letI : TopologicalSpace (MvPowerSeries (Fin 1) A) :=
    WithPiTopology.instTopologicalSpace A
  rw [continuous_induced_rng]
  change Continuous ((scaleIncl f) ∘ algebraMap A ↥(TateAlgebra A))
  -- The target topology is Pi.topologicalSpace (= WithPiTopology).
  -- Use continuous_pi: suffices that each coordinate is continuous.
  apply continuous_pi
  intro s
  -- The s-th component is a ↦ f^(s 0) * (C a)(s).
  -- Since (C a)(s) = if s = 0 then a else 0 (by MvPowerSeries.coeff_C),
  -- this is either a ↦ f^0 * a = a or a ↦ f^k * 0 = 0.
  -- Both are continuous.
  change Continuous fun a =>
    f ^ (s 0) * (algebraMap A ↥(TateAlgebra A) a).val s
  by_cases hs : s = 0
  · subst hs
    simp only [Finsupp.zero_apply, pow_zero, one_mul]
    -- Need: a ↦ (algebraMap a).val 0 is continuous.
    -- (algebraMap a).val 0 = (C a) 0 = a (constant coefficient).
    change Continuous fun a =>
      (algebraMap A (MvPowerSeries (Fin 1) A) a) 0
    exact (WithPiTopology.continuous_coeff A 0).comp
      WithPiTopology.continuous_C
  · -- s ≠ 0: (C a)(s) = 0, so the map is a ↦ f^(s 0) * 0 = 0.
    have : (fun a : A =>
        f ^ (s 0) * (algebraMap A ↥(TateAlgebra A) a).val s) =
      fun _ => 0 := by
      ext a
      change f ^ (s 0) * (algebraMap A (MvPowerSeries (Fin 1) A) a) s = 0
      classical
      rw [show (algebraMap A (MvPowerSeries (Fin 1) A) a) s =
        MvPowerSeries.coeff s (MvPowerSeries.C (σ := Fin 1) a) from rfl,
        MvPowerSeries.coeff_C, if_neg hs, mul_zero]
    rw [this]; exact continuous_const

end TateAlgebraWedhorn
