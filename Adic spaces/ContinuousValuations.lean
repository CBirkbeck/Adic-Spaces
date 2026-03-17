/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Ring.Basic
import «Adic spaces».ValuationSpectrum

/-!
# Continuous Valuations and Cont(A)

We define continuous valuations on a topological ring and the subspace `Cont(A)` of the
valuation spectrum `Spv(A)`, following Definition 7.7 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `Valuation.IsContinuous v` : A valuation `v` on a topological ring `A` is continuous if
  `{ a ∈ A | v(a) < γ }` is open for all `γ` in the value group.
* `ValuationSpectrum.IsContinuous v` : A point `v` of `Spv A` is continuous.
* `Cont A` : The set of continuous valuations in `Spv A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.7, Remark 7.8, Remark 7.9
-/

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation `v` on a topological ring `A` is *continuous* if `{ a | v(a) < γ }` is open
for all `γ` (Definition 7.7 of Wedhorn). -/
def IsContinuous [TopologicalSpace A] (v : Valuation A Γ₀) : Prop :=
  ∀ (γ : Γ₀), IsOpen { a : A | v a < γ }

variable (v : Valuation A Γ₀) [TopologicalSpace A]

/-- A valuation is continuous iff `{ a | v(a) < γ }` is open for all units `γ`. -/
lemma isContinuous_iff_units :
    v.IsContinuous ↔ ∀ (γ : Γ₀ˣ), IsOpen { a : A | v a < γ } := by
  constructor
  · exact fun h γ ↦ h γ
  · intro h γ
    by_cases hγ : γ = 0
    · subst hγ; simp [not_lt_zero']
    · exact h (Units.mk0 γ hγ)

/-- If `v` is continuous, then `v.ltAddSubgroup γ` is open for every unit `γ`. -/
lemma IsContinuous.isOpen_ltAddSubgroup (hv : v.IsContinuous) (γ : Γ₀ˣ) :
    IsOpen (v.ltAddSubgroup γ : Set A) :=
  Valuation.coe_ltAddSubgroup v γ ▸ hv γ

end Valuation

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- A point `v` of `Spv A` is *continuous* if the canonical valuation is continuous
(Definition 7.7 of Wedhorn). -/
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
/-- `embedding ∘ embed v ∘ (valuation A) = v` on elements of `A`. -/
private lemma embed_comp_valuation_eq {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀) (a : A) :
    letI := ValuativeRel.ofValuation v
    haveI := Valuation.Compatible.ofValuation v
    MonoidWithZeroHom.ValueGroup₀.embedding
      ((ValuativeRel.ValueGroupWithZero.embed v)
        ((ValuativeRel.valuation A) a)) = v a := by
  letI := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  change MonoidWithZeroHom.ValueGroup₀.embedding
    (ValuativeRel.ValueGroupWithZero.embed v
      (ValuativeRel.ValueGroupWithZero.mk a
        ⟨1, (ValuativeRel.posSubmonoid A).one_mem⟩)) = v a
  simp [ValuativeRel.ValueGroupWithZero.embed_mk, map_one,
    MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]

/-- If `v : Valuation A Γ₀` is continuous, then `ofValuation v` is continuous. -/
lemma isContinuous_ofValuation_of {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀)
    (hv : v.IsContinuous) : (ofValuation v).IsContinuous := by
  letI : ValuativeRel A := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  have h_sm := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := (v : A →*₀ Γ₀))
  intro δ
  have heq : { a : A | (ValuativeRel.valuation A) a < δ } =
      { a : A | v a < MonoidWithZeroHom.ValueGroup₀.embedding
        ((ValuativeRel.ValueGroupWithZero.embed v) δ) } := by
    ext a; simp only [Set.mem_setOf_eq, ← embed_comp_valuation_eq v a]
    exact ⟨fun h ↦ h_sm ((ValuativeRel.ValueGroupWithZero.embed_strictMono v) h),
      fun h ↦ (ValuativeRel.ValueGroupWithZero.embed_strictMono v).lt_iff_lt.mp
        (h_sm.lt_iff_lt.mp h)⟩
  exact heq ▸ hv _

/-- Every valuation on a discrete ring is continuous (Remark 7.8(2) of Wedhorn). -/
theorem cont_eq_univ_of_discreteTopology [DiscreteTopology A] :
    Cont A = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ isOpen_discrete _

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B]

/-- `Spv(φ)` preserves continuity for continuous `φ` (Remark 7.9 of Wedhorn). -/
theorem comap_isContinuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : v.IsContinuous) :
    (comap φ v).IsContinuous := by
  letI : ValuativeRel B := v.toValuativeRel
  have hkey : comap φ v =
      ofValuation ((ValuativeRel.valuation B).comap φ) := by
    conv_lhs => rw [show v = ofValuation (ValuativeRel.valuation B)
      from (ofValuation_valuation v).symm]
    exact comap_ofValuation φ (ValuativeRel.valuation B)
  exact hkey ▸ isContinuous_ofValuation_of _ fun γ ↦ hφ.isOpen_preimage _ (hv γ)

/-- `Spv(φ)` maps `Cont B` into `Cont A` when `φ` is continuous (Remark 7.9). -/
theorem cont_comap_mapsTo {φ : A →+* B} (hφ : Continuous φ) :
    Set.MapsTo (comap φ) (Cont B) (Cont A) :=
  fun _ hv ↦ comap_isContinuous hφ hv

end Functoriality

end ValuationSpectrum
