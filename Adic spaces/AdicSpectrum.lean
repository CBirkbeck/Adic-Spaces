/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ContinuousValuations
import «Adic spaces».GeometricSeries
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# The Adic Spectrum

We define the adic spectrum `Spa(A, A⁺)` of a topological ring `A` with a subring `A⁺`,
following Definition 7.23 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `PlusSubring A` : Typeclass equipping `A` with a designated subring `A⁺`.
* `Spa A Aplus` : The adic spectrum `Spa(A, A⁺)`, the set of continuous valuations on `A`
  that are bounded by `1` on `A⁺`.
* `rationalOpen T s` : A rational subset `R(T/s)` of `Spa(A, A⁺)`
  (Definition 7.29 of Wedhorn).

## Main results

* `isClosed_of_isMaximal_of_isOpen_units` : Maximal ideals are closed when the unit group
  is open.
* `isOpen_units_of_isOpen_topologicallyNilpotent` : The unit group is open when the set of
  topologically nilpotent elements is open (Prop 5.38 consequence).
* `IsTopologicallyNilpotent.mem_of_isMaximal` : Topologically nilpotent elements lie in
  every maximal ideal (Jacobson radical containment).
* `isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent` : Every maximal ideal is open when
  `A°°` is open.
* `exists_mem_spa_supp_eq` : Prop 7.51 (for open maximal ideals via trivial valuation).

## Notation

* `A⁺` (scoped in `Spv`) : The subring of integral elements, via `PlusSubring A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.23, Example 7.26,
  Remark 7.28, Definition 7.29, Proposition 5.38, Proposition 7.51, Proposition 7.52
-/

open Topology Pointwise WithZero

/-! ### Maximal ideals and units in topological rings -/

section MaximalIdealClosed

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- In a topological ring where the set of units is open, every maximal ideal is closed.

The proof uses the fact that the closure of a proper ideal is again proper (since units
are open, their complement — the nonunits — is closed, and the closure stays inside it). -/
theorem isClosed_of_isMaximal_of_isOpen_units
    (hU : IsOpen {a : A | IsUnit a}) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsClosed (𝔪 : Set A) := by
  rw [← closure_eq_iff_isClosed]
  -- It suffices to show 𝔪.closure = 𝔪 as ideals
  have hle : 𝔪 ≤ 𝔪.closure := by
    intro x hx; change x ∈ closure (𝔪 : Set A); exact subset_closure hx
  have hne : 𝔪.closure ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    intro h1
    have : (1 : A) ∈ closure (𝔪 : Set A) := h1
    have : (1 : A) ∈ {a : A | IsUnit a}ᶜ :=
      closure_minimal (fun x hx ↦ mt (Ideal.eq_top_of_isUnit_mem 𝔪 hx)
        (Ideal.IsMaximal.ne_top ‹_›)) hU.isClosed_compl this
    exact this isUnit_one
  rw [← Ideal.coe_closure, show 𝔪.closure = 𝔪 from
    (Ideal.IsMaximal.eq_of_le ‹_› hne hle).symm]

end MaximalIdealClosed

section OpenUnits

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A]

/-- In a complete Hausdorff nonarchimedean ring with linear topology where `A°°` is open,
the set of units is open.

The proof uses Prop 5.38 of Wedhorn: for each unit `u`, the translate `u + A°°` is an open
neighbourhood of `u` in `A×`. Indeed, for `a ∈ A°°`, `u⁻¹a ∈ A°°` (since `A°°` is an ideal),
so `1 + u⁻¹a` is a unit by Prop 5.38, hence `u + a = u(1 + u⁻¹a)` is a unit. -/
theorem isOpen_units_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a}) :
    IsOpen {a : A | IsUnit a} := by
  rw [isOpen_iff_forall_mem_open]
  intro u hu
  refine ⟨(u + ·) '' {a | IsTopologicallyNilpotent a}, ?_, ?_, ?_⟩
  · -- Every u + a with a ∈ A°° is a unit
    rintro x ⟨a, ha, rfl⟩
    change IsUnit (u + a)
    obtain ⟨u', rfl⟩ := (hu : IsUnit u)
    -- u⁻¹a is topologically nilpotent (A°° is an ideal under IsLinearTopology)
    have ha' : IsTopologicallyNilpotent (↑u'⁻¹ * a) := ha.mul_left ↑u'⁻¹
    -- Factor: u + a = u(1 + u⁻¹a)
    have hfact : (↑u' : A) + a = ↑u' * (1 + ↑u'⁻¹ * a) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (↑u' : A) (↑u'⁻¹ : A),
        Units.inv_mul, one_mul]
    rw [hfact]
    exact u'.isUnit.mul ha'.isUnit_one_add
  · -- u + A°° is open (translation of open set)
    exact isOpenMap_add_left u _ hopen
  · -- u ∈ u + A°° (via a = 0)
    exact ⟨0, IsTopologicallyNilpotent.zero, by simp⟩

end OpenUnits

namespace Spv

/-- A commutative ring equipped with a designated subring of integral elements `A⁺`,
as in a Huber pair `(A, A⁺)`. -/
class PlusSubring (A : Type*) [CommRing A] where
  /-- The subring of integral elements `A⁺`. -/
  toSubring : Subring A

/-- The designated subring of integral elements `A⁺`. -/
def ringPlus (A : Type*) [CommRing A] [PlusSubring A] : Subring A :=
  PlusSubring.toSubring

@[inherit_doc ringPlus]
scoped postfix:max "⁺" => ringPlus

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The *adic spectrum* `Spa(A, A⁺)` of a topological ring `A` with subring `A⁺`
(Definition 7.23 of Wedhorn). A point of `Spa(A, A⁺)` is a continuous valuation `v`
on `A` such that `v(f) ≤ 1` for all `f ∈ A⁺`. -/
def Spa (A : Type*) [CommRing A] [TopologicalSpace A] (Aplus : Subring A) : Set (Spv A) :=
  { v ∈ Cont A | ∀ f ∈ Aplus, v.vle f 1 }

/-- `Spa` is antitone in the subring: a larger `A⁺` gives a smaller spectrum. -/
lemma spa_antitone {Aplus Aplus' : Subring A} (h : Aplus ≤ Aplus') :
    Spa A Aplus' ⊆ Spa A Aplus :=
  fun _ hv ↦ ⟨hv.1, fun f hf ↦ hv.2 f (h hf)⟩

variable [PlusSubring A]

@[simp]
lemma mem_spa_iff (v : Spv A) :
    v ∈ Spa A A⁺ ↔ v.IsContinuous ∧ ∀ f ∈ A⁺, v.vle f 1 :=
  Iff.rfl

lemma spa_subset_cont : Spa A A⁺ ⊆ Cont A :=
  fun _ hv ↦ hv.1

lemma vle_one_of_mem_spa {v : Spv A} (hv : v ∈ Spa A A⁺)
    {f : A} (hf : f ∈ A⁺) : v.vle f 1 :=
  hv.2 f hf

lemma spa_eq_cont_inter :
    Spa A A⁺ = Cont A ∩ ⋂ f ∈ (A⁺ : Set A), { v : Spv A | v.vle f 1 } := by
  ext v
  simp only [Spa, Set.mem_inter_iff, mem_cont_iff,
    Set.mem_iInter, Set.mem_setOf_eq]
  rfl

/-- If `A` has the discrete topology, then `Spa(A, A⁺) = { v ∈ Spv A | ∀ f ∈ A⁺, v(f) ≤ 1 }`
(Example 7.26 of Wedhorn, partial). -/
theorem spa_eq_of_discreteTopology [DiscreteTopology A] :
    Spa A A⁺ = { v : Spv A | ∀ f ∈ A⁺, v.vle f 1 } := by
  ext v
  simp only [mem_spa_iff, Set.mem_setOf_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨fun γ ↦ isOpen_discrete _, h⟩⟩

section Prop752

/-! ### Proposition 7.52 of Wedhorn

We characterize elements of `A⁺` and units via the adic spectrum.
-/

omit [TopologicalSpace A] [PlusSubring A] in
/-- If `f` is a unit, then no valuation sends `f` to zero. This is the forward direction
of **Proposition 7.52(2)** of Wedhorn. -/
lemma not_vle_zero_of_isUnit {f : A} (hu : IsUnit f) (v : Spv A) : ¬ v.vle f 0 := by
  letI : ValuativeRel A := v.toValuativeRel
  obtain ⟨u, rfl⟩ := hu
  intro h
  have := ValuativeRel.mul_vle_mul_right h (↑u⁻¹ : A)
  rw [Units.inv_mul, mul_zero] at this
  exact absurd this (ValuativeRel.not_vle.mpr ValuativeRel.zero_vlt_one)

/-- **Proposition 7.51** of Wedhorn (for open maximal ideals): the trivial valuation on the
residue field `A/𝔪` composed with the quotient map gives a point of `Spa(A, A⁺)` with
support `𝔪`. -/
lemma exists_mem_spa_supp_eq (𝔪 : Ideal A) [𝔪.IsMaximal]
    (h𝔪 : IsOpen (𝔪 : Set A)) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔪 := by
  classical
  haveI := Ideal.Quotient.field 𝔪
  let w : Valuation A (ℤᵐ⁰) :=
    (1 : Valuation (A ⧸ 𝔪) _).comap (Ideal.Quotient.mk 𝔪)
  refine ⟨ofValuation w, ⟨?_, ?_⟩, ?_⟩
  · -- Continuity: sublevel sets of the trivial valuation are ∅, 𝔪, or Set.univ
    apply isContinuous_ofValuation_of
    intro γ
    by_cases hγ : γ = 0
    · subst hγ; convert isOpen_empty
      ext a; simp [not_lt_zero']
    · by_cases h1 : (1 : ℤᵐ⁰) < γ
      · convert isOpen_univ; ext a
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, w, Valuation.comap_apply]
        exact lt_of_le_of_lt (Valuation.one_apply_le_one _) h1
      · push_neg at h1
        suffices {a : A | w a < γ} = (𝔪 : Set A) by rw [this]; exact h𝔪
        ext a
        simp only [Set.mem_setOf_eq, w, Valuation.comap_apply]
        constructor
        · intro h
          exact Ideal.Quotient.eq_zero_iff_mem.mp
            (Valuation.one_apply_lt_one_iff.mp (lt_of_lt_of_le h h1))
        · intro ha
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
          exact zero_lt_iff.mpr hγ
  · -- A⁺ condition: the trivial valuation takes values in {0, 1}, all ≤ 1
    intro f hf
    change w f ≤ w 1
    simp only [w, Valuation.comap_apply, map_one]
    exact Valuation.one_apply_le_one _
  · -- Support of trivial valuation = kernel of quotient map = 𝔪
    rw [supp_ofValuation]
    ext a
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply,
      Valuation.one_apply_eq_zero_iff]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- **Proposition 7.52(2)** of Wedhorn: if every maximal ideal of `A` is open and
`v(f) ≠ 0` for all `v ∈ Spa(A, A⁺)`, then `f` is a unit. -/
lemma isUnit_of_forall_not_vle_zero
    (hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → IsOpen (𝔪 : Set A))
    {f : A} (h : ∀ v ∈ Spa A A⁺, ¬ v.vle f 0) : IsUnit f := by
  by_contra hf
  obtain ⟨𝔪, h𝔪, hf𝔪⟩ :=
    Ideal.exists_le_maximal (Ideal.span {f}) (Ideal.span_singleton_ne_top hf)
  haveI := h𝔪
  obtain ⟨v, hv, hsv⟩ := exists_mem_spa_supp_eq 𝔪 (hmax 𝔪 h𝔪)
  exact h v hv ((v.mem_supp_iff f).mp (hsv ▸ hf𝔪 (Ideal.mem_span_singleton_self f)))

end Prop752

/-- A *rational subset* of `Spa(A, A⁺)` (Definition 7.29 of Wedhorn).
`R(T/s) = { v ∈ Spa(A, A⁺) | ∀ t ∈ T, v(t) ≤ v(s) ≠ 0 }`. -/
def rationalOpen (T : Finset A) (s : A) : Set (Spv A) :=
  { v ∈ Spa A A⁺ | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 }

lemma rationalOpen_subset_spa {T : Finset A} {s : A} :
    rationalOpen T s ⊆ Spa A A⁺ :=
  fun _ hv ↦ hv.1

lemma rationalOpen_eq_spa_inter {T : Finset A} (hT : T.Nonempty) (s : A) :
    rationalOpen T s = Spa A A⁺ ∩ ⋂ t ∈ (T : Set A), basicOpen t s := by
  ext v
  simp only [rationalOpen, Set.mem_inter_iff, Set.mem_iInter,
    basicOpen, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, hvT, hvs⟩
    exact ⟨hv, fun t ht ↦ ⟨hvT t ht, hvs⟩⟩
  · rintro ⟨hv, hvT⟩
    obtain ⟨t₀, ht₀⟩ := hT
    exact ⟨hv, fun t ht ↦ (hvT t ht).1, (hvT t₀ ht₀).2⟩

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B] [PlusSubring B]

/-- A continuous ring hom `φ : A →+* B` with `φ(A⁺) ⊆ B⁺` induces
`Spa(φ) : Spa(B, B⁺) → Spa(A, A⁺)` via `Spv.comap` (Remark 7.28 of Wedhorn). -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ)
    (hAB : A⁺ ≤ (B⁺).comap φ)
    {v : Spv B} (hv : v ∈ Spa B B⁺) :
    comap φ v ∈ Spa A A⁺ := by
  refine ⟨comap_isContinuous hφ hv.1, fun f hf ↦ ?_⟩
  have hvle : v.vle (φ f) 1 := hv.2 (φ f) (hAB hf)
  change v.vle (φ f) (φ 1)
  rw [map_one]
  exact hvle

/-- `Spv.comap φ` maps `Spa(B, B⁺)` into `Spa(A, A⁺)` when `φ` is continuous and
`φ(A⁺) ⊆ B⁺` (Remark 7.28 of Wedhorn). -/
theorem spa_comap_mapsTo {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ) :
    Set.MapsTo (comap φ) (Spa B B⁺) (Spa A A⁺) :=
  fun _ hv ↦ comap_mem_spa hφ hAB hv

/-- The continuous map `Spa(φ) : Spa(B, B⁺) → Spa(A, A⁺)` induced by a continuous ring
homomorphism `φ : A →+* B` with `φ(A⁺) ⊆ B⁺` (Remark 7.28 of Wedhorn). -/
def spaComap {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ) :
    C(↥(Spa B B⁺), ↥(Spa A A⁺)) where
  toFun := (spa_comap_mapsTo hφ hAB).restrict _ _ _
  continuous_toFun :=
    (comap_continuous φ).restrict (spa_comap_mapsTo hφ hAB)

end Functoriality

/-! ### Topology on `Cont(A)` and `Spa(A, A⁺)`

Both `Cont(A)` and `Spa(A, A⁺)` carry the subspace topology from `Spv(A)`.
The chain of inclusions `Spa(A, A⁺) ⊆ Cont(A) ⊆ Spv(A)` gives continuous
embeddings (Definition 7.23, Remark 7.28 of Wedhorn).
-/

section SubspaceTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

omit [PlusSubring A] in
/-- The inclusion `↥(Cont A) ↪ Spv A` is a topological embedding. -/
theorem cont_subtypeVal_isEmbedding :
    Topology.IsEmbedding (Subtype.val : ↥(Cont A) → Spv A) :=
  Topology.IsEmbedding.subtypeVal

/-- The inclusion `↥(Spa A A⁺) ↪ Spv A` is a topological embedding. -/
theorem spa_subtypeVal_isEmbedding :
    Topology.IsEmbedding (Subtype.val : ↥(Spa A A⁺) → Spv A) :=
  Topology.IsEmbedding.subtypeVal

/-- The inclusion `↥(Spa A A⁺) → ↥(Cont A)` is continuous. -/
theorem continuous_spa_inclusion :
    Continuous (Set.inclusion spa_subset_cont : ↥(Spa A A⁺) → ↥(Cont A)) :=
  continuous_inclusion spa_subset_cont

/-- The inclusion `↥(Spa A A⁺) ↪ ↥(Cont A)` is a topological embedding.
Both carry the subspace topology from `Spv A`, so the subspace topology
on `Spa(A, A⁺)` relative to `Cont(A)` agrees with the one from `Spv(A)`. -/
theorem spa_inclusion_isEmbedding :
    Topology.IsEmbedding (Set.inclusion spa_subset_cont : ↥(Spa A A⁺) → ↥(Cont A)) :=
  Topology.IsEmbedding.mk
    (Topology.IsInducing.of_comp (continuous_inclusion spa_subset_cont)
      continuous_subtype_val Topology.IsInducing.subtypeVal)
    (Set.inclusion_injective spa_subset_cont)

end SubspaceTopology

end Spv

section TopNilMaximal

/-! ### Topologically nilpotent elements and maximal ideals

In a complete Hausdorff nonarchimedean ring with linear topology, every topologically
nilpotent element lies in every maximal ideal (it is in the Jacobson radical). Combined
with the hypothesis that `A°°` is open, this shows every maximal ideal is open.
-/

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A]

/-- In a complete Hausdorff nonarchimedean ring with linear topology,
every topologically nilpotent element lies in every maximal ideal.

For any `b`, the product `ab` is topologically nilpotent (since `A°°` is an ideal
under `IsLinearTopology`), hence `1 - ab` is a unit by Prop 5.38. This means `a` is
in the Jacobson radical, hence in every maximal ideal. -/
theorem IsTopologicallyNilpotent.mem_of_isMaximal {a : A}
    (ha : IsTopologicallyNilpotent a) (𝔪 : Ideal A) [𝔪.IsMaximal] : a ∈ 𝔪 := by
  by_contra ha𝔪
  have htop : 𝔪 ⊔ Ideal.span {a} = ⊤ := by
    by_contra h
    have heq := Ideal.IsMaximal.eq_of_le ‹_› h le_sup_left
    have ha_mem : a ∈ 𝔪 ⊔ Ideal.span {a} := Submodule.mem_sup.mpr
      ⟨0, 𝔪.zero_mem, a, Ideal.mem_span_singleton_self a, zero_add a⟩
    rw [← heq] at ha_mem; exact ha𝔪 ha_mem
  rw [Ideal.eq_top_iff_one] at htop
  obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.mem_sup.mp htop
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hn
  -- r * a is topologically nilpotent since A°° is an ideal
  have hra : IsTopologicallyNilpotent (r * a) := ha.mul_left r
  -- m = 1 - r * a is a unit by Prop 5.38, but m ∈ 𝔪, contradiction
  have hunit : IsUnit m := by
    rw [show m = 1 - r * a from by rw [← hmn, add_sub_cancel_right]]
    exact hra.isUnit_one_sub
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem 𝔪 hm hunit)

/-- If the set of topologically nilpotent elements is open, then every maximal ideal is open.
Every topologically nilpotent element lies in every maximal ideal (by `mem_of_isMaximal`),
so `𝔪` contains the open neighborhood `A°°` of zero. -/
theorem isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    (𝔪 : Ideal A) [𝔪.IsMaximal] : IsOpen (𝔪 : Set A) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(x + ·) '' {a | IsTopologicallyNilpotent a}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact 𝔪.add_mem hx (ha.mem_of_isMaximal 𝔪)
  · exact isOpenMap_add_left x _ hopen
  · exact ⟨0, IsTopologicallyNilpotent.zero, by simp⟩

end TopNilMaximal

section Prop752Full

/-! ### Proposition 7.52 with f-adic hypotheses -/

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A] [Spv.PlusSubring A]

open Spv

/-- **Proposition 7.51** of Wedhorn: in a complete Hausdorff nonarchimedean ring with linear
topology and open `A°°`, for every maximal ideal `𝔪` there exists `v ∈ Spa(A, A⁺)` with
`supp(v) = 𝔪`. -/
theorem Spv.exists_mem_spa_supp_eq_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔪 :=
  Spv.exists_mem_spa_supp_eq 𝔪
    (isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent hopen 𝔪)

/-- **Proposition 7.52(2)** of Wedhorn with f-adic hypotheses: in a complete Hausdorff
nonarchimedean ring with linear topology and open `A°°`, if `v(f) ≠ 0` for all
`v ∈ Spa(A, A⁺)`, then `f` is a unit. -/
theorem Spv.isUnit_of_forall_not_vle_zero_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    {f : A} (h : ∀ v ∈ Spa A A⁺, ¬ v.vle f 0) : IsUnit f :=
  Spv.isUnit_of_forall_not_vle_zero
    (fun 𝔪 h𝔪 ↦ @isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent
      A _ _ _ _ _ _ _ _ hopen 𝔪 h𝔪)
    h

end Prop752Full
