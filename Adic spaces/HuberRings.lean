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
  rw [show ((P.idealOfDefinition ^ n : Ideal A) : Set A) =
      ((P.idealOfDefinition ^ n).toAddSubgroup : Set A) from
    (Submodule.coe_toAddSubgroup (P.idealOfDefinition ^ n)).symm]
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
  -- Step 1: J = Ideal.map subtype I ≤ √𝔞
  have hJ_le : P.idealOfDefinition ≤ 𝔞.radical := by
    rw [idealOfDefinition, Ideal.map_le_iff_le_comap]
    intro y hy
    exact h _ (P.isTopologicallyNilpotent_of_mem hy)
  -- Step 2: J^m ≤ 𝔞 for some m
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ_le (P.idealOfDefinition_fg)
  -- Step 3: image(I^m) ⊆ J^m ⊆ 𝔞
  have h_sub : Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀) ⊆ (𝔞 : Set A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hm (by rw [idealOfDefinition, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hy)
  -- Step 4: 𝔞 contains an open neighborhood of 0, hence is open
  rw [show (𝔞 : Set A) = (𝔞.toAddSubgroup : Set A) from
    (Submodule.coe_toAddSubgroup 𝔞).symm]
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
  intro y hy
  exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
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
  rw [Ideal.mem_radical_iff]
  have ha' := IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ha
  obtain ⟨n, hn⟩ := (ha'.eventually
    ((P.pow_image_isOpen 1).mem_nhds (Set.mem_image_of_mem _ (P.I ^ 1).zero_mem))).exists
  obtain ⟨y, hy, hval⟩ := hn
  exact ⟨n, by rw [← hval, idealOfDefinition]; exact Ideal.mem_map_of_mem _ (pow_one P.I ▸ hy)⟩

end LinearTopology

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
    · change IsOpen (P.A₀.subtype.toAddMonoidHom '' ((P.I ^ n).toAddSubgroup : Set P.A₀))
      rw [show (⇑P.A₀.subtype.toAddMonoidHom : ↥P.A₀ → A) = Subtype.val from rfl,
        Submodule.coe_toAddSubgroup]
      exact P.pow_image_isOpen n
    · change P.A₀.subtype.toAddMonoidHom '' ((P.I ^ n).toAddSubgroup : Set P.A₀) ⊆ U
      rw [show (⇑P.A₀.subtype.toAddMonoidHom : ↥P.A₀ → A) = Subtype.val from rfl,
        Submodule.coe_toAddSubgroup]
      exact hn

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
  rw [show ((topologicalNilradical A : Ideal A) : Set A) =
      ((topologicalNilradical A).toAddSubgroup : Set A) from
    (Submodule.coe_toAddSubgroup _).symm]
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    ((u.isUnit.isOpenMap_smul _ P.isOpen).mem_nhds ⟨0, P.A₀.zero_mem, smul_zero _⟩)
    ((Submodule.coe_toAddSubgroup (topologicalNilradical A)).symm ▸ hsub))

/-- In a Tate ring with linear topology, the set of topologically nilpotent elements is open.
This is the `Set` version of `isOpen_topologicalNilradical`, matching the hypothesis
used in `AdicSpectrum.lean`. -/
theorem IsTateRing.isOpen_topologicallyNilpotentElements :
    IsOpen (TopologicalRing.topologicallyNilpotentElements A) := by
  convert IsTateRing.isOpen_topologicalNilradical (A := A)

end TateRing
