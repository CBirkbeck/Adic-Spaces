/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Maps
import «Adic spaces».Bounded

/-!
# Huber Rings (f-adic Rings)

We define **Huber rings** (also called **f-adic rings**) and **Tate rings**,
following §6 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `PairOfDefinition A` : A pair of definition `(A₀, I)` for a topological ring `A`,
  consisting of an open subring `A₀` whose subspace topology is `I`-adic for a
  finitely generated ideal `I ⊆ A₀` (Definition 6.1).
* `IsHuberRing A` : A topological ring is a Huber ring if it admits a pair
  of definition.
* `IsTateRing A` : A Huber ring with a topologically nilpotent unit (Definition 6.10).

## Main results

* `PairOfDefinition.pow_isOpen` : Each power `Iⁿ` is open in `A₀`.
* `PairOfDefinition.pow_image_isOpen` : The image of `Iⁿ` in `A` is open.
* `PairOfDefinition.isTopologicallyNilpotent_of_mem` : Elements of `I` are
  topologically nilpotent in `A` (Corollary 6.4(3)).
* `PairOfDefinition.hasBasis_nhds_zero` : The images of `Iⁿ` in `A` form a
  neighborhood basis of `0`.
* `PairOfDefinition.idealOfDefinition_pow_isOpen` : Each power `Jⁿ` of the ideal
  of definition (in `A`) is open.
* `PairOfDefinition.ideal_isOpen_of_nilpotent_le_radical` : Backward direction
  of Lemma 6.6: if all topologically nilpotent elements are in `√𝔞`, then `𝔞`
  is open.
* `PairOfDefinition.isBounded_A₀` : The ring of definition `A₀` is bounded
  (Corollary 6.4(2)).
* `PairOfDefinition.mem_powerBoundedSubring` : Elements of `A₀` are power-bounded:
  `A₀ ⊆ A°`.
* `PairOfDefinition.exists_fg_le_topologicalNilradical` : Connection to the
  `hJ` hypothesis of `OpenIdeals.lean` (Remark 6.7).
* `IsTateRing.isOpen_topologicalNilradical` : In a Tate ring, `A°°` is open
  (Proposition 6.13(1)).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6
-/

/-- A **pair of definition** `(A₀, I)` for a topological ring `A` consists of an
open subring `A₀ ⊆ A` and a finitely generated ideal `I ⊆ A₀` such that the subspace
topology on `A₀` equals the `I`-adic topology (Definition 6.1 of Wedhorn). -/
structure PairOfDefinition (A : Type*) [CommRing A] [TopologicalSpace A] where
  /-- The ring of definition `A₀`, an open subring of `A`. -/
  A₀ : Subring A
  /-- The ideal of definition `I`, an ideal of `A₀`. -/
  I : Ideal A₀
  /-- `A₀` is open in `A`. -/
  isOpen : IsOpen (A₀ : Set A)
  /-- `I` is finitely generated. -/
  fg : I.FG
  /-- The subspace topology on `A₀` is the `I`-adic topology. -/
  isAdic : IsAdic I

/-- A topological ring `A` is a **Huber ring** (or **f-adic ring**) if it admits a
pair of definition (Definition 6.1 of Wedhorn). -/
class IsHuberRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop where
  /-- There exists a pair of definition. -/
  exists_pairOfDefinition : Nonempty (PairOfDefinition A)

/-- A Huber ring is a **Tate ring** if it contains a topologically nilpotent unit
(Definition 6.10 of Wedhorn). -/
class IsTateRing (A : Type*) [CommRing A] [TopologicalSpace A] : Prop
    extends IsHuberRing A where
  /-- There exists a topologically nilpotent unit. -/
  exists_topologicallyNilpotent_unit : ∃ u : Aˣ, IsTopologicallyNilpotent (u : A)

namespace PairOfDefinition

open Filter Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Each power `Iⁿ` is open in `A₀` (in the subspace topology). -/
theorem pow_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen ((P.I ^ n : Ideal P.A₀) : Set P.A₀) :=
  (isAdic_iff.mp P.isAdic).1 n

/-- The image of `Iⁿ` in `A` is open. Since `A₀` is open in `A` and `Iⁿ` is open
in the subspace topology on `A₀`, the image is open in `A`. -/
theorem pow_image_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) :=
  P.isOpen.isOpenMap_subtype_val _ (P.pow_isOpen n)

omit [IsTopologicalRing A] in
/-- Elements of the ideal of definition `I` are topologically nilpotent in `A`
(see Corollary 6.4(3) of Wedhorn). -/
theorem isTopologicallyNilpotent_of_mem (P : PairOfDefinition A) {a : P.A₀}
    (ha : a ∈ P.I) : IsTopologicallyNilpotent (a : A) := by
  have h₀ : IsTopologicallyNilpotent a :=
    P.isAdic.hasBasis_nhds_zero.tendsto_right_iff.mpr fun n _ =>
      Filter.eventually_atTop.mpr ⟨n, fun m hm =>
        Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ha m)⟩
  exact h₀.map (φ := P.A₀.subtype) continuous_subtype_val

/-- The images of `Iⁿ` in `A` form a fundamental system of open neighborhoods of `0`.
Since `A₀` is open and the subspace topology is `I`-adic, the `Iⁿ` form a neighborhood
basis of `0` in the ambient ring `A`. -/
theorem hasBasis_nhds_zero (P : PairOfDefinition A) :
    (𝓝 (0 : A)).HasBasis (fun _ : ℕ => True)
      (fun n => Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) :=
  Filter.HasBasis.mk fun U => by
    constructor
    · intro hU
      have hU' : Subtype.val ⁻¹' U ∈ 𝓝 (0 : ↥P.A₀) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨n, -, hn⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hU'
      exact ⟨n, trivial, (Set.image_mono hn).trans (Set.image_preimage_subset _ _)⟩
    · rintro ⟨n, -, hn⟩
      exact mem_nhds_iff.mpr
        ⟨_, hn, P.pow_image_isOpen n, Set.mem_image_of_mem _ (P.I ^ n).zero_mem⟩

/-! ### Lemma 6.6 of Wedhorn (backward direction) -/

/-- The ideal of `A` generated by the ideal of definition `I ⊆ A₀`. -/
def idealOfDefinition (P : PairOfDefinition A) : Ideal A :=
  Ideal.map P.A₀.subtype P.I

omit [IsTopologicalRing A] in
theorem idealOfDefinition_fg (P : PairOfDefinition A) : P.idealOfDefinition.FG :=
  P.fg.map _

/-- Each power `Jⁿ` of the ideal of definition (in `A`) is open. -/
theorem idealOfDefinition_pow_isOpen (P : PairOfDefinition A) (n : ℕ) :
    IsOpen ((P.idealOfDefinition ^ n : Ideal A) : Set A) := by
  have h_sub : Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) ⊆
      ((P.idealOfDefinition ^ n : Ideal A) : Set A) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [idealOfDefinition, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  change IsOpen ((P.idealOfDefinition ^ n).toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((P.pow_image_isOpen n).mem_nhds (Set.mem_image_of_mem _ (P.I ^ n).zero_mem))
    ((Submodule.coe_toAddSubgroup (P.idealOfDefinition ^ n)).symm ▸ h_sub))

/-- Backward direction of Lemma 6.6 of Wedhorn: in a Huber ring, if every
topologically nilpotent element lies in the radical of an ideal `𝔞`, then `𝔞` is open.

The proof uses the ideal of definition: its generators are topologically nilpotent
(by `isTopologicallyNilpotent_of_mem`), hence in `√𝔞`. Since this ideal is finitely
generated, some power lands inside `𝔞`, and that power contains an open set. -/
theorem ideal_isOpen_of_nilpotent_le_radical (P : PairOfDefinition A) {𝔞 : Ideal A}
    (h : ∀ a : A, IsTopologicallyNilpotent a → a ∈ 𝔞.radical) :
    IsOpen (𝔞 : Set A) := by
  have hJ_le : P.idealOfDefinition ≤ 𝔞.radical := by
    rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun _ hy => h _ (P.isTopologicallyNilpotent_of_mem hy)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ_le P.idealOfDefinition_fg
  have h_sub : Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀) ⊆ (𝔞 : Set A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hm (by rw [idealOfDefinition, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hy)
  change IsOpen (𝔞.toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((P.pow_image_isOpen m).mem_nhds (Set.mem_image_of_mem _ (P.I ^ m).zero_mem))
    ((Submodule.coe_toAddSubgroup 𝔞).symm ▸ h_sub))

/-! ### Corollary 6.4 of Wedhorn -/

/-- The ring of definition `A₀` is bounded in `A`: for every neighborhood `U` of `0`,
there exists a neighborhood `V` of `0` with `A₀ · V ⊆ U`. This holds because `Iⁿ`
is an ideal of `A₀`, so `A₀ · Iⁿ = Iⁿ` (Corollary 6.4(2) of Wedhorn). -/
theorem isBounded_subring (P : PairOfDefinition A) :
    ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), (P.A₀ : Set A) * V ⊆ U := by
  intro U hU
  obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
  refine ⟨_, P.hasBasis_nhds_zero.mem_of_mem trivial (i := n), ?_⟩
  rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
  exact hn ⟨⟨a, ha⟩ * y, Ideal.mul_mem_left _ _ hy, MulMemClass.coe_mul ..⟩

/-- The ring of definition `A₀` is bounded in the sense of `TopologicalRing.IsBounded`
(Corollary 6.4(2) of Wedhorn). -/
theorem isBounded_A₀ (P : PairOfDefinition A) :
    TopologicalRing.IsBounded (P.A₀ : Set A) :=
  P.isBounded_subring

/-- Elements of the ring of definition `A₀` are power-bounded: `A₀ ⊆ A°`
(Corollary 6.4(2) of Wedhorn). Since `A₀` is bounded and `{aⁿ} ⊆ A₀` for `a ∈ A₀`
(because `A₀` is a subring), each `a ∈ A₀` is power-bounded. -/
theorem mem_powerBoundedSubring (P : PairOfDefinition A) {a : A} (ha : a ∈ P.A₀) :
    TopologicalRing.IsPowerBounded a :=
  P.isBounded_A₀.subset (Set.range_subset_iff.mpr fun n => P.A₀.pow_mem ha n)

/-! ### Connection to the topological nilradical (Remark 6.7 of Wedhorn) -/

section LinearTopology

variable [IsLinearTopology A A]

omit [IsTopologicalRing A] in
/-- In a Huber ring with linear topology, the ideal of definition is contained
in the topological nilradical: every element of `J = A · I` is topologically
nilpotent (Remark 6.7 of Wedhorn). -/
theorem idealOfDefinition_le_topologicalNilradical (P : PairOfDefinition A) :
    P.idealOfDefinition ≤ topologicalNilradical A := by
  rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
  exact fun _ hy => IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    (P.isTopologicallyNilpotent_of_mem hy)

/-- In a Huber ring with linear topology, the pair of definition produces the
hypothesis `hJ` needed by `ideal_isOpen_iff_topologicalNilradical_le_radical`
from `OpenIdeals.lean` (connecting HuberRings to OpenIdeals). -/
theorem exists_fg_le_topologicalNilradical (P : PairOfDefinition A) :
    ∃ J : Ideal A, J.FG ∧ J ≤ topologicalNilradical A ∧
      ∀ n : ℕ, IsOpen ((J ^ n : Ideal A) : Set A) :=
  ⟨P.idealOfDefinition, P.idealOfDefinition_fg,
    P.idealOfDefinition_le_topologicalNilradical, P.idealOfDefinition_pow_isOpen⟩

/-- Every topologically nilpotent element lies in the radical of the ideal of
definition (Remark 6.7 of Wedhorn, reverse direction). Since `image(I)` is an
open neighborhood of `0`, the powers `aⁿ` eventually land there.

Together with `idealOfDefinition_le_topologicalNilradical`, this gives
`J ≤ topologicalNilradical A ≤ √J`, so `√J = topologicalNilradical A`
when the topological nilradical is a radical ideal. -/
theorem topologicalNilradical_le_idealOfDefinition_radical (P : PairOfDefinition A) :
    topologicalNilradical A ≤ P.idealOfDefinition.radical := by
  intro a ha
  have ha' := IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ha
  obtain ⟨n, y, hy, hval⟩ := (ha'.eventually
    ((P.pow_image_isOpen 1).mem_nhds (Set.mem_image_of_mem _ (P.I ^ 1).zero_mem))).exists
  exact Ideal.mem_radical_iff.mpr
    ⟨n, by rw [← hval, idealOfDefinition]; exact Ideal.mem_map_of_mem _ (pow_one P.I ▸ hy)⟩

end LinearTopology

/-- The power-bounded subring `A°` is open in any Huber ring (Proposition 6.4(4) of Wedhorn).
Since the ring of definition `A₀ ⊆ A°` is open and `A°` is a subring (hence additive subgroup),
`A°` is open by `AddSubgroup.isOpen_mono`. -/
theorem isOpen_powerBoundedSubring (P : PairOfDefinition A) [IsLinearTopology A A] :
    IsOpen (TopologicalRing.powerBoundedSubring A) := by
  have h_le : P.A₀.toAddSubgroup ≤
      (TopologicalRing.powerBoundedSubring.toSubring A).toAddSubgroup :=
    fun _ ha => P.mem_powerBoundedSubring ha
  have h_open : IsOpen (P.A₀.toAddSubgroup : Set A) := by
    change IsOpen (P.A₀ : Set A); exact P.isOpen
  have := AddSubgroup.isOpen_mono h_le h_open
  rwa [show ((TopologicalRing.powerBoundedSubring.toSubring A).toAddSubgroup : Set A) =
    TopologicalRing.powerBoundedSubring A from rfl] at this

end PairOfDefinition

/-! ### Huber rings are nonarchimedean (Corollary 6.4(1) of Wedhorn) -/

/-- A Huber ring has a nonarchimedean additive group topology: every neighborhood of `0`
contains an open additive subgroup (Corollary 6.4(1) of Wedhorn). -/
instance IsHuberRing.nonarchimedeanAddGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] : NonarchimedeanAddGroup A where
  is_nonarchimedean := by
    obtain ⟨P⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
    intro U hU
    obtain ⟨n, -, hn⟩ := P.hasBasis_nhds_zero.mem_iff.mp hU
    refine ⟨⟨(P.I ^ n).toAddSubgroup.map P.A₀.subtype.toAddMonoidHom, ?_⟩, ?_⟩
    · change IsOpen (Subtype.val '' ((P.I ^ n).toAddSubgroup : Set P.A₀))
      rw [Submodule.coe_toAddSubgroup]; exact P.pow_image_isOpen n
    · change Subtype.val '' ((P.I ^ n).toAddSubgroup : Set P.A₀) ⊆ U
      rw [Submodule.coe_toAddSubgroup]; exact hn

/-! ### Tate rings: A°° is open (Proposition 6.13(1) of Wedhorn) -/

section TateRing

open Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsTateRing A] [IsLinearTopology A A]

/-- In a Tate ring with linear topology, the topological nilradical `A°°` is open
(Proposition 6.13(1) of Wedhorn). The key step is: if `u` is a topologically
nilpotent unit, then `u · A₀` is an open subset of `A°°`, since `u · a` is
topologically nilpotent for every power-bounded `a ∈ A₀`. -/
theorem IsTateRing.isOpen_topologicalNilradical :
    IsOpen ((topologicalNilradical A : Ideal A) : Set A) := by
  obtain ⟨P⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  obtain ⟨u, hu⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hsub : (u : A) • (P.A₀ : Set A) ⊆
      ((topologicalNilradical A : Ideal A) : Set A) := by
    rintro _ ⟨a, ha, rfl⟩
    change (u : A) * a ∈ topologicalNilradical A
    rw [mul_comm]
    exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((P.mem_powerBoundedSubring ha).isTopologicallyNilpotent_mul hu)
  change IsOpen ((topologicalNilradical A).toAddSubgroup : Set A)
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((u.isUnit.isOpenMap_smul _ P.isOpen).mem_nhds ⟨0, P.A₀.zero_mem, smul_zero _⟩)
    ((Submodule.coe_toAddSubgroup (topologicalNilradical A)).symm ▸ hsub))

/-- In a Tate ring with linear topology, the set of topologically nilpotent elements is open.
This is the `Set` version of `isOpen_topologicalNilradical`, matching the hypothesis
used in `AdicSpectrum.lean`. -/
theorem IsTateRing.isOpen_topologicallyNilpotentElements :
    IsOpen (TopologicalRing.topologicallyNilpotentElements A) := by
  convert IsTateRing.isOpen_topologicalNilradical (A := A)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A continuous ring homomorphism from a Tate ring sends the topologically
nilpotent unit to a topologically nilpotent unit in the target. -/
theorem IsTateRing.map_topologicallyNilpotent_unit
    {B : Type*} [CommRing B] [TopologicalSpace B]
    {φ : A →+* B} (hφ : Continuous φ) :
    ∃ v : Bˣ, IsTopologicallyNilpotent (v : B) := by
  obtain ⟨u, hu⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  refine ⟨u.map φ, ?_⟩
  change IsTopologicallyNilpotent (φ u)
  exact hu.map hφ

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A Huber ring that receives a continuous ring hom from a Tate ring is itself Tate
(Remark 6.11 of Wedhorn). The image of the topologically nilpotent unit is again a
topologically nilpotent unit. -/
theorem IsTateRing.of_continuous_map
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {φ : A →+* B} (hφ : Continuous φ) : IsTateRing B where
  exists_topologicallyNilpotent_unit := IsTateRing.map_topologicallyNilpotent_unit hφ

end TateRing

/-! ### Topologically nilpotent elements and the ideal of definition -/

section TopNilAndI

open Filter Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- If `u ∈ A₀` is topologically nilpotent in `A`, then `u^N ∈ I` for some `N`.
This follows because the image of `I` in `A` is an open neighborhood of `0`,
and `u^n → 0`. -/
theorem PairOfDefinition.exists_pow_mem_I (P : PairOfDefinition A)
    {u : A} (hu_mem : u ∈ P.A₀) (hu_nil : IsTopologicallyNilpotent u) :
    ∃ N : ℕ, (⟨u, hu_mem⟩ : P.A₀) ^ N ∈ P.I := by
  have h_nhds : P.A₀.subtype '' ((P.I : Ideal P.A₀) : Set P.A₀) ∈ 𝓝 (0 : A) :=
    (pow_one P.I ▸ P.pow_image_isOpen 1).mem_nhds
      ⟨0, P.I.zero_mem, rfl⟩
  obtain ⟨N, ⟨⟨y, hy_mem⟩, hy_I, hval⟩⟩ := hu_nil.exists_pow_mem_of_mem_nhds h_nhds
  exact ⟨N, by rwa [show (⟨u, hu_mem⟩ : P.A₀) ^ N = ⟨y, hy_mem⟩ from
    Subtype.ext (by simpa [SubmonoidClass.coe_pow] using hval.symm)]⟩

/-- If `u` is a unit in `A`, `u ∈ A₀`, and `u^N ∈ I`, then `I^m ≤ Ideal.span {u_A₀ ^ N}`
for some `m`, where `u_A₀ = ⟨u, hu_mem⟩`.

The key idea: `u` is a unit, so `u^N · A₀` is open in `A` (multiplication by a unit
is a homeomorphism). Since `A₀` is bounded, for large `m` the image of `I^m` in `A`
is contained in `u^N · A₀`, i.e., every element of `I^m` is a multiple of `u^N` in `A₀`. -/
theorem PairOfDefinition.exists_pow_I_le_span_unit (P : PairOfDefinition A)
    {u : Aˣ} (hu_mem : (u : A) ∈ P.A₀) (N : ℕ) :
    ∃ m : ℕ, P.I ^ m ≤ Ideal.span {(⟨(u : A), hu_mem⟩ : P.A₀) ^ N} := by
  -- u^N · A₀ is open since u is a unit
  have h_open : IsOpen ((u ^ N : Aˣ) • (P.A₀ : Set A)) :=
    isOpenMap_smul (u ^ N) _ P.isOpen
  -- By boundedness, image(I^m) ⊆ u^N · A₀ for large m
  obtain ⟨m, -, hm⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (h_open.mem_nhds ⟨0, P.A₀.zero_mem, smul_zero _⟩)
  refine ⟨m, fun x hx => ?_⟩
  -- x ∈ I^m, so (x : A) ∈ image(I^m) ⊆ u^N · A₀
  obtain ⟨b, hb_mem, hb_eq⟩ := hm ⟨x, hx, rfl⟩
  -- hb_eq : ↑(u ^ N) • b = ↑x, i.e., (↑u)^N * b = ↑x
  have hval : (↑x : A) = (↑u) ^ N * b := by
    have : (↑(u ^ N : Aˣ) : A) * b = ↑x := by rw [← smul_eq_mul]; exact hb_eq
    rw [Units.val_pow_eq_pow_val] at this; exact this.symm
  exact (show x = (⟨(u : A), hu_mem⟩ : P.A₀) ^ N * ⟨b, hb_mem⟩ from
    Subtype.ext (by simpa using hval)).symm ▸
    Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end TopNilAndI

/-! ### Radicals of ideals generating the same adic topology -/

section RadicalEquiv

variable {R : Type*} [CommRing R] [TopologicalSpace R]

omit [TopologicalSpace R] in
/-- If `a ∈ I` and `I^m ⊆ (a)` for some `m`, then `I.radical = (a).radical`. -/
theorem Ideal.radical_eq_of_mem_and_pow_le {I : Ideal R} {a : R}
    (ha : a ∈ I) {m : ℕ} (hm : I ^ m ≤ Ideal.span {a}) :
    I.radical = (Ideal.span {a}).radical := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hx
    exact Ideal.mem_radical_iff.mpr ⟨k * m, hm (pow_mul x k m ▸ Ideal.pow_mem_pow hk m)⟩
  · exact Ideal.radical_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

omit [TopologicalSpace R] in
/-- The radical of a principal ideal is unchanged by taking powers of the generator:
`(Ideal.span {a ^ n}).radical = (Ideal.span {a}).radical` for `n ≥ 1`. -/
theorem Ideal.radical_span_pow {a : R} {n : ℕ} (hn : 0 < n) :
    (Ideal.span {a ^ n}).radical = (Ideal.span {a}).radical := by
  rw [← Ideal.span_singleton_pow]
  apply le_antisymm
  · -- radical(span{a}^n) ≤ radical(span{a}): monotonicity
    exact Ideal.radical_mono (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn))
  · -- radical(span{a}) ≤ radical(span{a}^n): if a ∣ x^k then a^n ∣ x^{kn}
    intro x hx
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hx
    exact Ideal.mem_radical_iff.mpr ⟨k * n, pow_mul x k n ▸ Ideal.pow_mem_pow hk n⟩

end RadicalEquiv

/-! ### IsAdic for interleaved ideals (Remark 6.12 of Wedhorn) -/

section InterleavedIsAdic

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- If `J ≤ I` and `I^m ≤ J` for some `m`, and the topology on `A₀` is `I`-adic,
then it is also `J`-adic. The key point: `J` is "interleaved" with `I`, so
`I^{mn} ≤ J^n ≤ I^n`, meaning `J^n` and `I^n` define the same filter. -/
theorem PairOfDefinition.isAdic_of_interleaving (P : PairOfDefinition A)
    {J : Ideal P.A₀} (hJ_le : J ≤ P.I) {m : ℕ} (hI_le : P.I ^ m ≤ J) :
    IsAdic J := by
  -- Interleaving: J^n ≤ I^n and I^{mn} ≤ J^n
  have hJ_pow_le : ∀ n, J ^ n ≤ P.I ^ n := fun n => pow_le_pow_left' hJ_le n
  have hI_pow_le : ∀ n, P.I ^ (m * n) ≤ J ^ n := fun n =>
    pow_mul P.I m n ▸ pow_le_pow_left' hI_le n
  rw [isAdic_iff]
  constructor
  · -- Openness: J^n contains I^{mn} which is open
    intro n
    change IsOpen ((J ^ n).toAddSubgroup : Set P.A₀)
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((P.pow_isOpen (m * n)).mem_nhds (P.I ^ (m * n)).zero_mem)
        ((Submodule.coe_toAddSubgroup (J ^ n)).symm ▸ (hI_pow_le n)))
  · -- Basis: J^n ≤ I^n, and the I^k form a neighborhood basis
    intro s hs
    obtain ⟨k, -, hk⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hs
    exact ⟨k, fun x hx => hk (hJ_pow_le k hx)⟩

end InterleavedIsAdic

/-! ### Power of topologically nilpotent is topologically nilpotent -/

/-- A positive power of a topologically nilpotent element is topologically nilpotent. -/
theorem isTopologicallyNilpotent_pow {A : Type*} [TopologicalSpace A] [MonoidWithZero A]
    {a : A} (ha : IsTopologicallyNilpotent a) {K : ℕ} (hK : 0 < K) :
    IsTopologicallyNilpotent (a ^ K) := by
  change Filter.Tendsto (fun n => (a ^ K) ^ n) Filter.atTop (nhds 0)
  simp_rw [← pow_mul]
  exact ha.comp (Filter.tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left K h)
    (fun b => ⟨b, le_mul_of_one_le_left (Nat.zero_le b) hK⟩))

/-! ### Principal pair of definition -/

section PrincipalPair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Replace the ideal of definition with a principal ideal `span{a}`, given `a ∈ I`
and `I^m ≤ span{a}`. The new pair has the same subring `A₀`. -/
def PairOfDefinition.withPrincipal (P : PairOfDefinition A)
    {a : P.A₀} (ha : a ∈ P.I) {m : ℕ} (hm : P.I ^ m ≤ Ideal.span {a}) :
    PairOfDefinition A where
  A₀ := P.A₀
  I := Ideal.span {a}
  isOpen := P.isOpen
  fg := ⟨{a}, by simp [Finset.coe_singleton]⟩
  isAdic := P.isAdic_of_interleaving
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)) hm

@[simp]
theorem PairOfDefinition.withPrincipal_A₀ (P : PairOfDefinition A)
    {a : P.A₀} (ha : a ∈ P.I) {m : ℕ} (hm : P.I ^ m ≤ Ideal.span {a}) :
    (P.withPrincipal ha hm).A₀ = P.A₀ := rfl

@[simp]
theorem PairOfDefinition.withPrincipal_I (P : PairOfDefinition A)
    {a : P.A₀} (ha : a ∈ P.I) {m : ℕ} (hm : P.I ^ m ≤ Ideal.span {a}) :
    (P.withPrincipal ha hm).I = Ideal.span {a} := rfl

end PrincipalPair

/-! ### Adic homomorphisms (Definition 6.23 of Wedhorn) -/

section AdicHom

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

/-- The restriction of a ring hom `φ : A →+* B` to subrings `A₀` and `B₀`, given that
`φ` maps `A₀` into `B₀`. -/
def PairOfDefinition.restrictRingHom (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀) : PA.A₀ →+* PB.A₀ :=
  (φ.comp PA.A₀.subtype).codRestrict PB.A₀ fun a => h a a.2

/-- A ring homomorphism `φ : A →+* B` between Huber rings is **adic** if there exist
pairs of definition `(A₀, I)` of `A` and `(B₀, J)` of `B` such that `φ(A₀) ⊆ B₀`
and the ideals `φ(I) · B₀` and `J` have the same radical in `B₀`
(Definition 6.23 of Wedhorn). -/
def IsAdicHom [IsHuberRing A] [IsHuberRing B] (φ : A →+* B) : Prop :=
  ∃ (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀),
    (Ideal.map (PA.restrictRingHom PB φ h) PA.I).radical = PB.I.radical

end AdicHom

/-! ### Proposition 6.25 of Wedhorn: continuous from Tate ⟹ adic -/

section Prop625

open Filter Topology Pointwise

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]

/-- The `restrictRingHom` for `withPrincipal` pairs is the same ring hom as for the original
pairs (since `A₀` and `B₀` are unchanged). -/
private theorem restrictRingHom_withPrincipal
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (φ : A →+* B) (h : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    {aA : PA.A₀} (haA : aA ∈ PA.I) {mA : ℕ} (hmA : PA.I ^ mA ≤ Ideal.span {aA})
    {aB : PB.A₀} (haB : aB ∈ PB.I) {mB : ℕ} (hmB : PB.I ^ mB ≤ Ideal.span {aB}) :
    (PA.withPrincipal haA hmA).restrictRingHom (PB.withPrincipal haB hmB) φ h =
    PA.restrictRingHom PB φ h := rfl

/-- **Proposition 6.25 of Wedhorn** (with compatible pairs). A continuous ring homomorphism
from a Tate ring is adic, provided compatible pairs of definition are given.

The full version removes the `h_map` hypothesis using Proposition 6.4(5)
(every bounded open subring is a ring of definition), which allows replacing
`PA.A₀` with `PA.A₀ ∩ φ⁻¹(PB.A₀)`. -/
theorem IsTateRing.isAdicHom_of_continuous_with_pairs
    [IsTateRing A] [IsHuberRing B]
    {φ : A →+* B} (hφ : Continuous φ)
    (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀) : IsAdicHom φ := by
  -- Step 1: top nil unit u in A; φ(u) is top nil in B
  obtain ⟨u, hu_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hv_nil : IsTopologicallyNilpotent (φ u) := hu_nil.map hφ
  -- Step 2: K ≥ 1 with u^K ∈ PA.A₀
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hu_nil (PA.isOpen.mem_nhds PA.A₀.zero_mem))
  set K := max K₀ 1
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hu_K : (u : A) ^ K ∈ PA.A₀ := hK₀ K (le_max_left _ _)
  -- Step 3: L ≥ 1 with (φ u)^L ∈ PB.A₀
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hv_nil (PB.isOpen.mem_nhds PB.A₀.zero_mem))
  set L := max L₀ 1
  have hL_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hv_L : (φ u) ^ L ∈ PB.A₀ := hL₀ L (le_max_left _ _)
  -- Subring elements
  set uK : PA.A₀ := ⟨(u : A) ^ K, hu_K⟩
  set vL : PB.A₀ := ⟨(φ u) ^ L, hv_L⟩
  -- Step 4: N₀ with (u^K)^N₀ ∈ PA.I; set N = N₀ + 1 ≥ 1
  obtain ⟨N₀, hN₀⟩ := PA.exists_pow_mem_I hu_K (isTopologicallyNilpotent_pow hu_nil hK_pos)
  set N := N₀ + 1
  have hN_pos : 0 < N := Nat.succ_pos N₀
  have hN_mem : uK ^ N ∈ PA.I := by
    rw [show N = 1 + N₀ from by omega, pow_add, pow_one]
    exact Ideal.mul_mem_left _ _ hN₀
  -- Step 5: M₀ with (v^L)^M₀ ∈ PB.I; set M = M₀ + 1 ≥ 1
  obtain ⟨M₀, hM₀⟩ := PB.exists_pow_mem_I hv_L (isTopologicallyNilpotent_pow hv_nil hL_pos)
  set M := M₀ + 1
  have hM_pos : 0 < M := Nat.succ_pos M₀
  have hM_mem : vL ^ M ∈ PB.I := by
    rw [show M = 1 + M₀ from by omega, pow_add, pow_one]
    exact Ideal.mul_mem_left _ _ hM₀
  -- Step 6: I^mA ≤ span{uK^N} and I^mB ≤ span{vL^M}
  -- Use exists_pow_I_le_span_unit with units u^K and (u.map φ)^L
  have hu_K_unit_mem : ((u ^ K : Aˣ) : A) ∈ PA.A₀ := by
    rwa [Units.val_pow_eq_pow_val]
  obtain ⟨mA, hmA⟩ := PA.exists_pow_I_le_span_unit hu_K_unit_mem N
  -- Rewrite to use uK (same value, different proof)
  rw [show (⟨((u ^ K : Aˣ) : A), hu_K_unit_mem⟩ : PA.A₀) = uK from
    Subtype.ext (Units.val_pow_eq_pow_val u K)] at hmA
  have hv_L_unit_mem : (((Units.map (φ : A →* B) u) ^ L : Bˣ) : B) ∈ PB.A₀ := by
    rw [Units.val_pow_eq_pow_val, Units.coe_map]; exact hv_L
  obtain ⟨mB, hmB⟩ := PB.exists_pow_I_le_span_unit hv_L_unit_mem M
  -- Rewrite to use vL (same value, different proof)
  rw [show (⟨(((Units.map (φ : A →* B) u) ^ L : Bˣ) : B), hv_L_unit_mem⟩ : PB.A₀) = vL from
    Subtype.ext (by simp [vL, Units.val_pow_eq_pow_val, Units.coe_map])] at hmB
  -- Step 7: Construct new pairs and provide IsAdicHom witness
  refine ⟨PA.withPrincipal hN_mem hmA, PB.withPrincipal hM_mem hmB, h_map, ?_⟩
  -- Unfold the principal ideals, then compute image
  simp only [restrictRingHom_withPrincipal, PairOfDefinition.withPrincipal_I]
  erw [Ideal.map_span, Set.image_singleton]
  -- Goal: radical(span{φ_res(uK^N)}) = radical(span{vL^M})
  set a : PB.A₀ := (PA.restrictRingHom PB φ h_map) (uK ^ N)
  -- Key: a^{LM} = (vL^M)^{KN} (both have underlying value (φ u)^{KNLM} in B)
  have h_agree : a ^ (L * M) = (vL ^ M) ^ (K * N) := Subtype.ext (by
    simp only [a, PairOfDefinition.restrictRingHom, uK, vL, SubmonoidClass.coe_pow,
      RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply,
      Subring.coe_subtype, map_pow, ← pow_mul]
    congr 1; ring)
  have hKN_pos : 0 < K * N := Nat.mul_pos hK_pos hN_pos
  have hLM_pos : 0 < L * M := Nat.mul_pos hL_pos hM_pos
  -- a ∈ radical(span{vL^M}): since a^{LM} = (vL^M)^{KN} ∈ span{vL^M}
  have ha_rad : a ∈ (Ideal.span {vL ^ M}).radical := by
    rw [Ideal.mem_radical_iff]; refine ⟨L * M, ?_⟩; rw [h_agree]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hKN_pos)
    rw [hk]
    exact Ideal.pow_le_self (Nat.succ_ne_zero k)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
  -- vL^M ∈ radical(span{a}): since (vL^M)^{KN} = a^{LM} ∈ span{a}
  have hvL_rad : vL ^ M ∈ (Ideal.span {a}).radical := by
    rw [Ideal.mem_radical_iff]; refine ⟨K * N, ?_⟩; rw [← h_agree]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hLM_pos)
    rw [hk]
    exact Ideal.pow_le_self (Nat.succ_ne_zero k)
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)
  -- Mutual radical containment gives equality
  exact le_antisymm
    (Ideal.radical_le_radical_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_rad)))
    (Ideal.radical_le_radical_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hvL_rad)))

end Prop625
