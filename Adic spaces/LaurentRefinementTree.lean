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

/-- Right-branching Laurent tree built from a list of split elements.
At each step, the head element splits, the plus subtree is a leaf, and
the recursion continues on the minus side. -/
def ofRightBranchList : List A → LaurentTree A
  | [] => LaurentTree.leaf
  | f :: rest => LaurentTree.node f LaurentTree.leaf (ofRightBranchList rest)

@[simp] theorem ofRightBranchList_nil :
    (ofRightBranchList ([] : List A)) = LaurentTree.leaf := rfl

@[simp] theorem ofRightBranchList_cons (f : A) (rest : List A) :
    ofRightBranchList (f :: rest) =
      LaurentTree.node f LaurentTree.leaf (ofRightBranchList rest) := rfl

/-- The depth of `ofRightBranchList L` equals the length of `L`. -/
theorem depth_ofRightBranchList (L : List A) :
    (ofRightBranchList L).depth = L.length := by
  induction L with
  | nil => simp
  | cons f rest ih =>
    simp [ofRightBranchList, depth, ih, Nat.add_comm]

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
/-- The Finset of leaves of a Laurent tree, defined recursively via
`Finset.union` (separately from `LaurentTree.toCovering`).

At a `leaf`, the covers is the singleton `{D₀}`; at a `node f L R`, the
covers is the union of the L-subtree's covers and the R-subtree's covers.

This recursive Finset form makes the node-case covers
**definitionally** equal to a `Finset.union`, essential for the
`Homeomorph.piFinsetUnion`-based proof of the FLAT node-case inducing
theorem. Recovered via `LaurentTree.toCoveringCovers_eq_leaves_toFinset`. -/
noncomputable def LaurentTree.toCoveringCovers :
    LaurentTree A → RationalLocData A → Finset (RationalLocData A)
  | .leaf, D₀ => {D₀}
  | .node f L R, D₀ =>
      toCoveringCovers L (laurentPlusDatum D₀ f) ∪
      toCoveringCovers R (laurentMinusDatum D₀ f)

@[simp] theorem LaurentTree.toCoveringCovers_leaf (D₀ : RationalLocData A) :
    (LaurentTree.leaf : LaurentTree A).toCoveringCovers D₀ = {D₀} := rfl

open Classical in
@[simp] theorem LaurentTree.toCoveringCovers_node (f : A)
    (L R : LaurentTree A) (D₀ : RationalLocData A) :
    (LaurentTree.node f L R).toCoveringCovers D₀ =
      L.toCoveringCovers (laurentPlusDatum D₀ f) ∪
      R.toCoveringCovers (laurentMinusDatum D₀ f) := rfl

open Classical in
/-- The recursive `toCoveringCovers` equals the `toFinset` of the leaves
list (the two ways to compute the leaf Finset agree, by
`List.toFinset_append`). -/
theorem LaurentTree.toCoveringCovers_eq_leaves_toFinset
    (t : LaurentTree A) (D₀ : RationalLocData A) :
    t.toCoveringCovers D₀ = (t.leaves D₀).toFinset := by
  induction t generalizing D₀ with
  | leaf => simp [LaurentTree.leaves, LaurentTree.toCoveringCovers]
  | node f L R ihL ihR =>
    simp [LaurentTree.toCoveringCovers, LaurentTree.leaves, ihL, ihR,
      List.toFinset_append]

theorem LaurentTree.mem_toCoveringCovers_iff_mem_leaves
    (t : LaurentTree A) (D₀ : RationalLocData A) (D : RationalLocData A) :
    D ∈ t.toCoveringCovers D₀ ↔ D ∈ t.leaves D₀ := by
  classical
  rw [t.toCoveringCovers_eq_leaves_toFinset, List.mem_toFinset]

/-- Each element of `toCoveringCovers` is contained in the base rational
open (analogue of `leaf_subset_base` but for the recursive Finset). -/
theorem LaurentTree.toCoveringCovers_subset_base (t : LaurentTree A)
    (D₀ : RationalLocData A) (D : RationalLocData A)
    (hD : D ∈ t.toCoveringCovers D₀) :
    rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s :=
  t.leaf_subset_base D₀ D ((t.mem_toCoveringCovers_iff_mem_leaves D₀ D).mp hD)

/-- The recursive `toCoveringCovers` covers the base. -/
theorem LaurentTree.toCoveringCovers_cover_base (t : LaurentTree A)
    (D₀ : RationalLocData A) {v : Spv A}
    (hv : v ∈ rationalOpen D₀.T D₀.s) :
    ∃ D ∈ t.toCoveringCovers D₀, v ∈ rationalOpen D.T D.s := by
  classical
  obtain ⟨D, hD, hvD⟩ := t.cover_base D₀ hv
  exact ⟨D, (t.mem_toCoveringCovers_iff_mem_leaves D₀ D).mpr hD, hvD⟩

/-- The rational covering of `D₀` induced by the leaves of a Laurent tree.
Uses `toCoveringCovers` (the recursive Finset form) for the covers field. -/
noncomputable def LaurentTree.toCovering (t : LaurentTree A)
    (D₀ : RationalLocData A) : RationalCovering A where
  base := D₀
  covers := t.toCoveringCovers D₀
  hsubset := t.toCoveringCovers_subset_base D₀
  hcover := fun _ hv => t.toCoveringCovers_cover_base D₀ hv

@[simp] theorem LaurentTree.toCovering_base (t : LaurentTree A)
    (D₀ : RationalLocData A) : (t.toCovering D₀).base = D₀ := rfl

@[simp] theorem LaurentTree.toCovering_covers (t : LaurentTree A)
    (D₀ : RationalLocData A) :
    (t.toCovering D₀).covers = t.toCoveringCovers D₀ := rfl

@[simp] theorem LaurentTree.toCovering_leaf_covers (D₀ : RationalLocData A) :
    ((LaurentTree.leaf : LaurentTree A).toCovering D₀).covers = {D₀} := rfl

open Classical in
@[simp] theorem LaurentTree.toCovering_node_covers (f : A)
    (L R : LaurentTree A) (D₀ : RationalLocData A) :
    ((LaurentTree.node f L R).toCovering D₀).covers =
      (L.toCovering (laurentPlusDatum D₀ f)).covers ∪
      (R.toCovering (laurentMinusDatum D₀ f)).covers := rfl

/-! ## Leaf-leaf disjointness (the base case of T-LAURENT-LEAF-DISJOINT)

For a Laurent split at element `f` in a domain `A`, when both `L` and `R`
are the trivial trees `LaurentTree.leaf`, the leaf sets are simply
`{plus}` and `{minus}` (singletons). These are disjoint exactly when
`plus ≠ minus`, which holds under the standard hypothesis
`¬IsUnit (D₀.canonicalMap f) ∧ D₀.s ≠ 0` via T277. -/
open Classical in
theorem LaurentTree.leaves_disjoint_of_leaf_leaf
    [IsDomain A] (D₀ : RationalLocData A) (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hs : D₀.s ≠ 0) :
    Disjoint
      ((LaurentTree.leaf : LaurentTree A).leaves (laurentPlusDatum D₀ f)).toFinset
      ((LaurentTree.leaf : LaurentTree A).leaves
        (laurentMinusDatum D₀ f)).toFinset := by
  -- Both leaves are singletons; the disjoint reduces to plus ≠ minus.
  have h_plus : ((LaurentTree.leaf : LaurentTree A).leaves
      (laurentPlusDatum D₀ f)).toFinset = {laurentPlusDatum D₀ f} := by
    simp [LaurentTree.leaves_leaf]
  have h_minus : ((LaurentTree.leaf : LaurentTree A).leaves
      (laurentMinusDatum D₀ f)).toFinset = {laurentMinusDatum D₀ f} := by
    simp [LaurentTree.leaves_leaf]
  rw [h_plus, h_minus, Finset.disjoint_singleton]
  exact laurentPlus_ne_laurentMinus_of_nonunit D₀ f hf_nonunit hs

/-! ## Right-branching tree leaf enumeration

The right-branching tree `ofRightBranchList [f₁, ..., fₙ]` interpreted at
`D₀` yields a depth-`n` chain of Laurent splits, with the plus piece at
each level a leaf and the minus side continuing. We give the explicit
leaf enumeration. -/

/-- An auxiliary recursive base sequence: starting from `D₀`, walk down
the minus side via `f₁, f₂, ..., fₙ`. The `k`-th entry is
`laurentMinusDatum^k D₀ f₁..fₖ`. -/
noncomputable def LaurentTree.minusChain :
    RationalLocData A → List A → List (RationalLocData A)
  | D₀, [] => [D₀]
  | D₀, f :: rest =>
      D₀ :: minusChain (laurentMinusDatum D₀ f) rest

@[simp] theorem LaurentTree.minusChain_nil (D₀ : RationalLocData A) :
    LaurentTree.minusChain D₀ ([] : List A) = [D₀] := rfl

@[simp] theorem LaurentTree.minusChain_cons (D₀ : RationalLocData A)
    (f : A) (rest : List A) :
    LaurentTree.minusChain D₀ (f :: rest) =
      D₀ :: LaurentTree.minusChain (laurentMinusDatum D₀ f) rest := rfl

/-- The minus-chain has length `L.length + 1`. -/
theorem LaurentTree.minusChain_length (D₀ : RationalLocData A) (L : List A) :
    (LaurentTree.minusChain D₀ L).length = L.length + 1 := by
  induction L generalizing D₀ with
  | nil => simp
  | cons f rest ih =>
    simp [LaurentTree.minusChain, ih]

/-- The plus-pieces enumerated along the minus-chain. Each entry is
`laurentPlusDatum (minusBase k) f_{k+1}` where `minusBase k` is the
minus-chain entry after applying the first `k` splits. -/
noncomputable def LaurentTree.plusOfMinusChain :
    RationalLocData A → List A → List (RationalLocData A)
  | _, [] => []
  | D₀, f :: rest =>
      laurentPlusDatum D₀ f ::
        plusOfMinusChain (laurentMinusDatum D₀ f) rest

@[simp] theorem LaurentTree.plusOfMinusChain_nil (D₀ : RationalLocData A) :
    LaurentTree.plusOfMinusChain D₀ ([] : List A) = [] := rfl

@[simp] theorem LaurentTree.plusOfMinusChain_cons (D₀ : RationalLocData A)
    (f : A) (rest : List A) :
    LaurentTree.plusOfMinusChain D₀ (f :: rest) =
      laurentPlusDatum D₀ f ::
        LaurentTree.plusOfMinusChain (laurentMinusDatum D₀ f) rest := rfl

/-- The terminal minus-datum after walking down the chain `L = [f₁, ..., fₙ]`
from `D₀`: it equals `laurentMinusDatum (laurentMinusDatum ... D₀ f₁ ...) fₙ`,
i.e. the last `laurentMinusDatum` in the chain. We define it recursively
so it interacts cleanly with `leaves_ofRightBranchList`. -/
noncomputable def LaurentTree.terminalMinus :
    RationalLocData A → List A → RationalLocData A
  | D₀, [] => D₀
  | D₀, f :: rest => LaurentTree.terminalMinus (laurentMinusDatum D₀ f) rest

@[simp] theorem LaurentTree.terminalMinus_nil (D₀ : RationalLocData A) :
    LaurentTree.terminalMinus D₀ ([] : List A) = D₀ := rfl

@[simp] theorem LaurentTree.terminalMinus_cons (D₀ : RationalLocData A)
    (f : A) (rest : List A) :
    LaurentTree.terminalMinus D₀ (f :: rest) =
      LaurentTree.terminalMinus (laurentMinusDatum D₀ f) rest := rfl

/-- Explicit leaf enumeration for the right-branching tree:
`leaves (ofRightBranchList L) D₀` equals the list of plus-pieces along
the minus chain, appended with the terminal minus datum. -/
theorem LaurentTree.leaves_ofRightBranchList
    (D₀ : RationalLocData A) (L : List A) :
    (LaurentTree.ofRightBranchList L).leaves D₀ =
      LaurentTree.plusOfMinusChain D₀ L ++ [LaurentTree.terminalMinus D₀ L] := by
  induction L generalizing D₀ with
  | nil =>
    simp [LaurentTree.ofRightBranchList,
      LaurentTree.plusOfMinusChain, LaurentTree.terminalMinus]
  | cons f rest ih =>
    simp [LaurentTree.ofRightBranchList, LaurentTree.leaves,
      LaurentTree.plusOfMinusChain, LaurentTree.terminalMinus, ih]

/-! ## Basic existence: trees refining specific covers

For specific structured covers we can exhibit explicit refining trees.
These are the building blocks; the general Wedhorn 8.34 construction
combines them via iterated splitting. -/

/-- The trivial Laurent tree `leaf` refines any covering containing the
base datum `D₀` in its `covers`. -/
theorem LaurentTree.leaf_refines_singleton (D₀ : RationalLocData A)
    (C : RationalCovering A) (hcovers : D₀ ∈ C.covers) :
    (LaurentTree.leaf : LaurentTree A).Refines D₀ C := by
  refine ⟨D₀, hcovers, ?_⟩
  exact subset_refl _

/-- The depth-1 Laurent tree `node f leaf leaf` at root `D₀` refines the
Laurent cover `laurentCovering D₀ f`: the plus-leaf datum is
`laurentPlusDatum D₀ f` (a piece of `laurentCovering`'s covers), and
the minus-leaf datum is `laurentMinusDatum D₀ f` (the other piece). -/
theorem LaurentTree.node_leaf_leaf_refines_laurentCovering
    (D₀ : RationalLocData A) (f : A) :
    (LaurentTree.node f LaurentTree.leaf LaurentTree.leaf).Refines
      D₀ (laurentCovering D₀ f) := by
  refine ⟨?_, ?_⟩
  · -- L = leaf at laurentPlusDatum D₀ f refines: pick laurentPlusDatum
    refine ⟨laurentPlusDatum D₀ f, ?_, subset_refl _⟩
    simp [laurentCovering]
  · -- R = leaf at laurentMinusDatum D₀ f refines: pick laurentMinusDatum
    refine ⟨laurentMinusDatum D₀ f, ?_, subset_refl _⟩
    simp [laurentCovering]

/-- **Refinement transitivity at the cover level**: if every piece of
`C` is contained in some piece of `C'`, then `t.Refines D₀ C` implies
`t.Refines D₀ C'`. -/
theorem LaurentTree.Refines.mono (t : LaurentTree A) (D₀ : RationalLocData A)
    {C C' : RationalCovering A}
    (hCC' : ∀ E ∈ C.covers, ∃ E' ∈ C'.covers,
      rationalOpen E.T E.s ⊆ rationalOpen E'.T E'.s)
    (h : t.Refines D₀ C) :
    t.Refines D₀ C' := by
  rw [LaurentTree.refines_iff_forall_mem_leaves] at h ⊢
  intro D hD
  obtain ⟨E, hE, hDE⟩ := h D hD
  obtain ⟨E', hE', hEE'⟩ := hCC' E hE
  exact ⟨E', hE', hDE.trans hEE'⟩

/-- **Node combinator**: if `L` refines `C` from `laurentPlusDatum D₀ f`
and `R` refines `C` from `laurentMinusDatum D₀ f`, then `node f L R`
refines `C` from `D₀`. (Definitional from `LaurentTree.refines_node`.) -/
theorem LaurentTree.node_refines_of_subtrees_refine
    (f : A) (L R : LaurentTree A) (D₀ : RationalLocData A)
    (C : RationalCovering A)
    (hL : L.Refines (laurentPlusDatum D₀ f) C)
    (hR : R.Refines (laurentMinusDatum D₀ f) C) :
    (LaurentTree.node f L R).Refines D₀ C :=
  ⟨hL, hR⟩

/-- **Right-branching refinement**: given a list `L = [f₁, ..., fₙ]` of
split elements and a `C`-refinement witness for each plus-piece and the
terminal minus-piece, the right-branching tree refines `C`. -/
theorem LaurentTree.ofRightBranchList_refines (D₀ : RationalLocData A)
    (L : List A) (C : RationalCovering A)
    (h_plus : ∀ D ∈ LaurentTree.plusOfMinusChain D₀ L,
      ∃ E ∈ C.covers, rationalOpen D.T D.s ⊆ rationalOpen E.T E.s)
    (h_terminal : ∃ E ∈ C.covers,
      rationalOpen (LaurentTree.terminalMinus D₀ L).T
                   (LaurentTree.terminalMinus D₀ L).s ⊆
      rationalOpen E.T E.s) :
    (LaurentTree.ofRightBranchList L).Refines D₀ C := by
  rw [LaurentTree.refines_iff_forall_mem_leaves, leaves_ofRightBranchList]
  intro D hD
  rcases List.mem_append.mp hD with hPlus | hTerm
  · exact h_plus D hPlus
  · rcases List.mem_singleton.mp hTerm with rfl
    exact h_terminal

end Semantics

end ValuationSpectrum
