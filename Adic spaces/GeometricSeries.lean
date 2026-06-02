/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Geometric Series in Nonarchimedean Rings

We prove **Proposition 5.38** of [Wedhorn, *Adic Spaces*]: in a complete Hausdorff
nonarchimedean topological ring, every topologically nilpotent element `a` yields a unit
`1 - a` (via the geometric series `∑ aⁿ`).

## Main results

* `IsTopologicallyNilpotent.summable_pow` : The geometric series `∑ aⁿ` converges.
* `IsTopologicallyNilpotent.neg` : `-a` is topologically nilpotent.
* `IsTopologicallyNilpotent.isUnit_one_sub` : `1 - a` is a unit (**Prop 5.38**).
* `IsTopologicallyNilpotent.isUnit_one_add` : `1 + a` is a unit (corollary).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 5.38
-/

open Filter Topology

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]

omit [T2Space A] [IsTopologicalRing A] in
/-- The geometric series `∑ aⁿ` converges for a topologically nilpotent element `a`
in a complete nonarchimedean ring. -/
theorem IsTopologicallyNilpotent.summable_pow {a : A} (ha : IsTopologicallyNilpotent a) :
    Summable (a ^ · : ℕ → A) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact ha

/-- **Proposition 5.38** of Wedhorn: in a complete Hausdorff nonarchimedean ring,
`1 - a` is a unit for every topologically nilpotent `a`, with inverse `∑ aⁿ`. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 - a) :=
  .of_mul_eq_one _ ha.summable_pow.one_sub_mul_tsum_pow

omit [T2Space A] [CompleteSpace A] [IsTopologicalRing A] [IsUniformAddGroup A] in
/-- The negation of a topologically nilpotent element is topologically nilpotent. -/
theorem IsTopologicallyNilpotent.neg {a : A}
    (ha : IsTopologicallyNilpotent a) : IsTopologicallyNilpotent (-a) := by
  intro U hU
  obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  refine (ha.eventually (V.isOpen.mem_nhds V.zero_mem')).mono fun n hn ↦ hVU ?_
  change (-a) ^ n ∈ (V : Set A)
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow]; exact hn
  · rw [ho.neg_pow]; exact V.neg_mem' hn

/-- Corollary of Prop 5.38: `1 + a` is a unit for topologically nilpotent `a`. -/
theorem IsTopologicallyNilpotent.isUnit_one_add {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 + a) := by
  rw [← sub_neg_eq_add]
  exact ha.neg.isUnit_one_sub

/-! ### Matrix Nakayama (topologically nilpotent matrices)

For BGR §3.7.2/1 (Remark 8.29 / Lemma 8.31) one needs `1 - B` to be a unit when `B` is an
`n × n` matrix all of whose entries are topologically nilpotent. Because `A` is commutative we
reduce to the scalar `isUnit_one_sub` via the determinant: `det (1 - B) = 1 - t` with `t`
topologically nilpotent (every monomial of the expansion other than the constant `1` carries a
topologically nilpotent entry of `B`), and `Matrix.isUnit_iff_isUnit_det` lifts the result back.
This is the correct form of "Nakayama 1.2.4/6": the topologically nilpotent *elements* of a Tate
ring generate the unit ideal, so the ideal-theoretic Nakayama is vacuous; the matrix/determinant
form is what BGR's Prop 1 actually uses. -/

/-- The complement `1 - det (1 - B)` is topologically nilpotent when every entry of `B` is.
Expanding `det (1 - B)`, the identity permutation contributes `∏ᵢ (1 - Bᵢᵢ) = 1 - (top. nilp.)`
and every other permutation contributes a product containing an off-diagonal `-Bᵢⱼ` factor
(topologically nilpotent); topological nilpotence is closed under the relevant products and finite
sums. -/
theorem IsTopologicallyNilpotent.one_sub_det_one_sub_matrix
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsTopologicallyNilpotent (1 - (1 - B).det) := by
  sorry

/-- **Matrix Nakayama** (BGR Lemma 1.2.4/6, the form used in §3.7.2/1): for a complete Hausdorff
nonarchimedean commutative ring `A`, if every entry of an `n × n` matrix `B` is topologically
nilpotent then `1 - B` is invertible. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub_matrix
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n A)
    (hB : ∀ i j, IsTopologicallyNilpotent (B i j)) :
    IsUnit (1 - B) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simpa using (IsTopologicallyNilpotent.one_sub_det_one_sub_matrix B hB).isUnit_one_sub

