/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentRefinement

/-!
# Finite Laurent Refinement Trees

A `LaurentTree A` is a finite binary tree whose internal nodes are labelled
by elements of `A`. Applied to a root rational locality datum
`D₀ : RationalLocData A`, the tree describes a finite sequence of Laurent
splittings: each internal node `node f L R` represents the Laurent split at
`f`, whose plus subtree is interpreted starting from `laurentPlusDatum D₀ f`
and whose minus subtree starts from `laurentMinusDatum D₀ f`.

This is the structural carrier of Wedhorn's Lemma 8.34 refinement induction
used for the `IsSheafy` embedding via Lane C.

## Design note

The tree is *unindexed* — `LaurentTree A` does not bake `D₀` into the type.
The reason is strict positivity: an indexed version
`inductive LaurentTree : RationalLocData A → Type` with constructor
`node (f) (L : LaurentTree (laurentPlusDatum D₀ f)) ...` triggers a kernel
positivity violation because `laurentPlusDatum` is `noncomputable` and the
index is computed. The unindexed tree plus an interpretation function gives
the same mathematical content with no kernel objections.

## Main definitions

* `LaurentTree A` — the inductive type.
* `LaurentTree.depth` — the natural-number tree depth.
* `LaurentTree.leaves t D₀` — the list of leaf data when `t` is applied at
  root `D₀`.
* `LaurentTree.Refines t D₀ C` — every leaf data is contained in some piece
  of the rational covering `C`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.34.
-/

namespace ValuationSpectrum

/-- A finite binary tree of Laurent split labels in a commutative ring `A`.
Each `node f L R` represents the Laurent split at element `f ∈ A` with plus
subtree `L` and minus subtree `R`. Leaves carry no label. -/
inductive LaurentTree (A : Type*) : Type _
  | leaf : LaurentTree A
  | node (f : A) (left right : LaurentTree A) : LaurentTree A
  deriving Inhabited

namespace LaurentTree

variable {A : Type*}

/-- The depth (height) of a Laurent refinement tree. A `leaf` has depth `0`,
and `node f L R` has depth `1 + max L.depth R.depth`. -/
def depth : LaurentTree A → ℕ
  | .leaf => 0
  | .node _ L R => 1 + max L.depth R.depth

@[simp] theorem depth_leaf : (leaf : LaurentTree A).depth = 0 := rfl

@[simp] theorem depth_node (f : A) (L R : LaurentTree A) :
    (node f L R).depth = 1 + max L.depth R.depth := rfl

end LaurentTree

section Semantics

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- The list of rational locality data at the leaves when the Laurent tree
`t` is interpreted with root datum `D₀`. A `leaf` contributes `[D₀]`; a
`node f L R` recursively concatenates `L`'s leaves starting at
`laurentPlusDatum D₀ f` and `R`'s leaves starting at
`laurentMinusDatum D₀ f`. -/
noncomputable def LaurentTree.leaves :
    LaurentTree A → RationalLocData A → List (RationalLocData A)
  | .leaf, D₀ => [D₀]
  | .node f L R, D₀ =>
      L.leaves (laurentPlusDatum D₀ f) ++ R.leaves (laurentMinusDatum D₀ f)

@[simp] theorem LaurentTree.leaves_leaf (D₀ : RationalLocData A) :
    (LaurentTree.leaf : LaurentTree A).leaves D₀ = [D₀] := rfl

@[simp] theorem LaurentTree.leaves_node (f : A) (L R : LaurentTree A)
    (D₀ : RationalLocData A) :
    (LaurentTree.node f L R).leaves D₀ =
      L.leaves (laurentPlusDatum D₀ f) ++ R.leaves (laurentMinusDatum D₀ f) :=
  rfl

/-- A Laurent refinement tree `t : LaurentTree A`, applied at root `D₀`,
**refines** a rational covering `C` if every leaf datum is contained in some
piece of `C`. -/
noncomputable def LaurentTree.Refines :
    LaurentTree A → RationalLocData A → RationalCovering A → Prop
  | .leaf, D₀, C => ∃ E ∈ C.covers, rationalOpen D₀.T D₀.s ⊆ rationalOpen E.T E.s
  | .node f L R, D₀, C =>
      L.Refines (laurentPlusDatum D₀ f) C ∧ R.Refines (laurentMinusDatum D₀ f) C

@[simp] theorem LaurentTree.refines_leaf (D₀ : RationalLocData A)
    (C : RationalCovering A) :
    (LaurentTree.leaf : LaurentTree A).Refines D₀ C ↔
      ∃ E ∈ C.covers, rationalOpen D₀.T D₀.s ⊆ rationalOpen E.T E.s := Iff.rfl

@[simp] theorem LaurentTree.refines_node (f : A) (L R : LaurentTree A)
    (D₀ : RationalLocData A) (C : RationalCovering A) :
    (LaurentTree.node f L R).Refines D₀ C ↔
      L.Refines (laurentPlusDatum D₀ f) C ∧ R.Refines (laurentMinusDatum D₀ f) C :=
  Iff.rfl

/-- The list of leaves is always nonempty: every Laurent tree contains at
least one leaf. -/
theorem LaurentTree.leaves_ne_nil (t : LaurentTree A) (D₀ : RationalLocData A) :
    t.leaves D₀ ≠ [] := by
  induction t generalizing D₀ with
  | leaf => simp
  | node f L R ihL _ =>
    simp only [leaves_node]
    intro h
    exact ihL (laurentPlusDatum D₀ f) (List.append_eq_nil_iff.mp h).1

/-- `Refines` rephrased as a `∀ … ∈ leaves` statement, suitable for iterating
over leaves rather than recursing on tree structure. -/
theorem LaurentTree.refines_iff_forall_mem_leaves (t : LaurentTree A)
    (D₀ : RationalLocData A) (C : RationalCovering A) :
    t.Refines D₀ C ↔
      ∀ D ∈ t.leaves D₀, ∃ E ∈ C.covers,
        rationalOpen D.T D.s ⊆ rationalOpen E.T E.s := by
  induction t generalizing D₀ with
  | leaf => simp [LaurentTree.Refines, LaurentTree.leaves]
  | node f L R ihL ihR =>
    simp only [LaurentTree.Refines, LaurentTree.leaves_node, List.mem_append]
    constructor
    · rintro ⟨hL, hR⟩ D hD
      rcases hD with hL' | hR'
      · exact (ihL (laurentPlusDatum D₀ f)).mp hL D hL'
      · exact (ihR (laurentMinusDatum D₀ f)).mp hR D hR'
    · intro h
      refine ⟨(ihL (laurentPlusDatum D₀ f)).mpr ?_,
              (ihR (laurentMinusDatum D₀ f)).mpr ?_⟩
      · intro D hD; exact h D (Or.inl hD)
      · intro D hD; exact h D (Or.inr hD)

/-! ## Tree-induced covering -/

/-- The set of `Spv A` points covered by the leaves of `t` at root `D₀`:
the union of `rationalOpen D.T D.s` over all leaf data `D ∈ t.leaves D₀`. -/
def LaurentTree.leafCover (t : LaurentTree A) (D₀ : RationalLocData A) :
    Set (Spv A) :=
  ⋃ D ∈ t.leaves D₀, rationalOpen D.T D.s

@[simp] theorem LaurentTree.leafCover_leaf (D₀ : RationalLocData A) :
    (LaurentTree.leaf : LaurentTree A).leafCover D₀ = rationalOpen D₀.T D₀.s := by
  simp [LaurentTree.leafCover, LaurentTree.leaves]

theorem LaurentTree.leafCover_node (f : A) (L R : LaurentTree A)
    (D₀ : RationalLocData A) :
    (LaurentTree.node f L R).leafCover D₀ =
      L.leafCover (laurentPlusDatum D₀ f) ∪ R.leafCover (laurentMinusDatum D₀ f) := by
  ext v
  simp only [LaurentTree.leafCover, LaurentTree.leaves_node, Set.mem_iUnion,
    Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨D, hD | hD, hv⟩
    · exact Or.inl ⟨D, hD, hv⟩
    · exact Or.inr ⟨D, hD, hv⟩
  · rintro (⟨D, hD, hv⟩ | ⟨D, hD, hv⟩)
    · exact ⟨D, Or.inl hD, hv⟩
    · exact ⟨D, Or.inr hD, hv⟩

/-- Each leaf of `t` is contained in the root rational open. Proved by
recursion on the tree, using `laurentPlus_subset` and `laurentMinus_subset`
at each Laurent split. -/
theorem LaurentTree.leaf_subset_base (t : LaurentTree A) (D₀ : RationalLocData A) :
    ∀ D ∈ t.leaves D₀, rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s := by
  induction t generalizing D₀ with
  | leaf =>
    intro D hD
    rcases List.mem_singleton.mp (by simpa [LaurentTree.leaves] using hD) with rfl
    exact subset_refl _
  | node f L R ihL ihR =>
    intro D hD
    rcases List.mem_append.mp (by simpa [LaurentTree.leaves_node] using hD) with hL | hR
    · exact (ihL (laurentPlusDatum D₀ f) D hL).trans (laurentPlus_subset D₀ f)
    · exact (ihR (laurentMinusDatum D₀ f) D hR).trans (laurentMinus_subset D₀ f)

/-- The leaves of a Laurent tree cover the base rational open: every point of
`rationalOpen D₀.T D₀.s` lies in some `rationalOpen D.T D.s` for `D ∈ leaves t D₀`.
Proved by recursion on the tree, using `laurentCover_covers` at each Laurent split. -/
theorem LaurentTree.cover_base (t : LaurentTree A) (D₀ : RationalLocData A)
    {v : Spv A} (hv : v ∈ rationalOpen D₀.T D₀.s) :
    ∃ D ∈ t.leaves D₀, v ∈ rationalOpen D.T D.s := by
  induction t generalizing D₀ with
  | leaf =>
    refine ⟨D₀, ?_, hv⟩
    simp [LaurentTree.leaves]
  | node f L R ihL ihR =>
    rcases laurentCover_covers D₀ f v hv with hPlus | hMinus
    · obtain ⟨D, hD, hvD⟩ := ihL (laurentPlusDatum D₀ f) hPlus
      refine ⟨D, ?_, hvD⟩
      simp only [LaurentTree.leaves_node, List.mem_append]
      exact Or.inl hD
    · obtain ⟨D, hD, hvD⟩ := ihR (laurentMinusDatum D₀ f) hMinus
      refine ⟨D, ?_, hvD⟩
      simp only [LaurentTree.leaves_node, List.mem_append]
      exact Or.inr hD

open Classical in
/-- The rational covering of `D₀` induced by the leaves of a Laurent tree.
The covers are the leaves (as a `Finset` via `toFinset`); the `hsubset` and
`hcover` fields are supplied by `leaf_subset_base` and `cover_base`.

Note: `Classical.decEq` is used for `(t.leaves D₀).toFinset`. -/
noncomputable def LaurentTree.toCovering (t : LaurentTree A)
    (D₀ : RationalLocData A) : RationalCovering A where
  base := D₀
  covers := (t.leaves D₀).toFinset
  hsubset D hD := by
    have : D ∈ t.leaves D₀ := by
      simpa [List.mem_toFinset] using hD
    exact t.leaf_subset_base D₀ D this
  hcover v hv := by
    obtain ⟨D, hD, hvD⟩ := t.cover_base D₀ hv
    refine ⟨D, ?_, hvD⟩
    simpa [List.mem_toFinset] using hD

@[simp] theorem LaurentTree.toCovering_base (t : LaurentTree A)
    (D₀ : RationalLocData A) : (t.toCovering D₀).base = D₀ := rfl

open Classical in
@[simp] theorem LaurentTree.toCovering_covers (t : LaurentTree A)
    (D₀ : RationalLocData A) :
    (t.toCovering D₀).covers = (t.leaves D₀).toFinset := rfl

end Semantics

end ValuationSpectrum
