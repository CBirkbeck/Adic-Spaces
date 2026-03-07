/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationSpectrum
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuous Valuations and Cont(A)

We define continuous valuations on a topological ring and the subspace `Cont(A)` of the
valuation spectrum `Spv(A)`, following Definition 7.7 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `Valuation.IsContinuous v` : A valuation `v` on a topological ring `A` is continuous if
  `{ a ∈ A | v(a) < γ }` is open for all `γ` in the value group.
* `Spv.IsContinuous v` : A point `v` of `Spv A` is continuous.
* `Cont A` : The set of continuous valuations in `Spv A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.7, Remark 7.8, Remark 7.9
-/

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation `v` on a topological ring `A` is *continuous* if for every `γ` in the value
group, the sublevel set `{ a ∈ A | v(a) < γ }` is open (Definition 7.7 of Wedhorn). -/
def IsContinuous [TopologicalSpace A] (v : Valuation A Γ₀) : Prop :=
  ∀ (γ : Γ₀), IsOpen { a : A | v a < γ }

variable (v : Valuation A Γ₀) [TopologicalSpace A]

/-- A valuation is continuous iff the sublevel sets `{ a | v(a) < γ }` are open for all
units `γ` in the value group. -/
lemma isContinuous_iff_units :
    v.IsContinuous ↔ ∀ (γ : Γ₀ˣ), IsOpen { a : A | v a < γ } := by
  constructor
  · intro h γ
    exact h γ
  · intro h γ
    by_cases hγ : γ = 0
    · subst hγ
      convert isOpen_empty
      ext a
      exact iff_of_false not_lt_zero' (Set.notMem_empty a)
    · exact h (Units.mk0 γ hγ)

/-- If `v` is continuous, then the additive subgroup `v.ltAddSubgroup γ = { a | v(a) < γ }`
is open for every unit `γ`. -/
lemma IsContinuous.isOpen_ltAddSubgroup (hv : v.IsContinuous) (γ : Γ₀ˣ) :
    IsOpen (v.ltAddSubgroup γ : Set A) := by
  rw [Valuation.coe_ltAddSubgroup]
  exact hv γ

end Valuation

namespace Spv

variable {A : Type*} [CommRing A]

/-- A point `v` of `Spv A` is *continuous* if the associated canonical valuation is continuous
(Definition 7.7 of Wedhorn). This is well-defined since equivalent valuations give the same
`ValuativeRel` and hence the same canonical valuation. -/
def IsContinuous [TopologicalSpace A] (v : Spv A) : Prop :=
  letI : ValuativeRel A := v.toValuativeRel
  (ValuativeRel.valuation A).IsContinuous

/-- The set `Cont(A)` of continuous valuations in `Spv(A)` (Definition 7.7 of Wedhorn). -/
def Cont (A : Type*) [CommRing A] [TopologicalSpace A] : Set (Spv A) :=
  { v : Spv A | v.IsContinuous }

variable [TopologicalSpace A]

@[simp]
lemma mem_cont_iff (v : Spv A) : v ∈ Cont A ↔ v.IsContinuous := Iff.rfl

omit [TopologicalSpace A] in
/-- `embed v ∘ (valuation A) = v` on elements of `A`, where the `ValuativeRel`
instance comes from `ofValuation v`. -/
private lemma embed_comp_valuation_eq {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀) (a : A) :
    letI := ValuativeRel.ofValuation v
    haveI := Valuation.Compatible.ofValuation v
    (ValuativeRel.ValueGroupWithZero.embed v)
      ((ValuativeRel.valuation A) a) = v a := by
  letI := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  change ValuativeRel.ValueGroupWithZero.embed v
    (ValuativeRel.ValueGroupWithZero.mk a
      ⟨1, (ValuativeRel.posSubmonoid A).one_mem⟩) = v a
  rw [ValuativeRel.ValueGroupWithZero.embed_mk]
  simp [map_one]

/-- If `v : Valuation A Γ₀` is continuous, then `Spv.ofValuation v` is continuous. -/
lemma isContinuous_ofValuation_of {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀)
    (hv : v.IsContinuous) : (ofValuation v).IsContinuous := by
  letI : ValuativeRel A := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  intro δ
  have heq : { a : A | (ValuativeRel.valuation A) a < δ } =
      { a : A | v a <
        (ValuativeRel.ValueGroupWithZero.embed v) δ } := by
    ext a
    simp only [Set.mem_setOf_eq, ← embed_comp_valuation_eq v a,
      (ValuativeRel.ValueGroupWithZero.embed_strictMono v).lt_iff_lt.symm]
  exact heq ▸ hv _


/-- If `A` has the discrete topology, then every valuation on `A` is continuous
(Remark 7.8(2) of Wedhorn). -/
theorem cont_eq_univ_of_discreteTopology [DiscreteTopology A] :
    Cont A = Set.univ := by
  ext v
  simp only [mem_cont_iff, Set.mem_univ, iff_true]
  intro γ
  exact isOpen_discrete _

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B]

/-- If `φ : A →+* B` is continuous and `v ∈ Spv B` is continuous, then
`Spv(φ)(v) ∈ Spv A` is continuous (Remark 7.9 of Wedhorn). -/
theorem comap_isContinuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : v.IsContinuous) :
    (Spv.comap φ v).IsContinuous := by
  -- comap φ v = ofValuation ((valuation B).comap φ)
  letI : ValuativeRel B := v.toValuativeRel
  have hkey : Spv.comap φ v =
      ofValuation ((ValuativeRel.valuation B).comap φ) := by
    conv_lhs => rw [show v = ofValuation (ValuativeRel.valuation B)
      from (ofValuation_valuation v).symm]
    exact comap_ofValuation φ (ValuativeRel.valuation B)
  rw [hkey]
  apply isContinuous_ofValuation_of
  intro γ
  change IsOpen (φ ⁻¹' { b : B | (ValuativeRel.valuation B) b < γ })
  exact hφ.isOpen_preimage _ (hv γ)

/-- `Spv(φ)` maps `Cont B` into `Cont A` when `φ` is continuous
(Remark 7.9 of Wedhorn). -/
theorem cont_comap_mapsTo {φ : A →+* B} (hφ : Continuous φ) :
    Set.MapsTo (Spv.comap φ) (Cont B) (Cont A) :=
  fun _ hv ↦ comap_isContinuous hφ hv

end Functoriality

end Spv
