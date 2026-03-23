/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PseudoUniformizer
import «Adic spaces».Uniform
import «Adic spaces».StructureSheaf
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Perfectoid Rings and Fields

We define **perfectoid rings** and **perfectoid fields** following Scholze's
*Perfectoid Spaces* (2012), Definition 3.5.

## Main definitions

* `IsPerfectoidRing p A` : A Tate ring `A` is perfectoid (for a prime `p`) if it is
  complete, separated, uniform, and admits a pseudo-uniformizer `ϖ` such that `ϖ^p | p`
  in `A°` and the Frobenius is surjective on `A°/ϖ`.
* `IsPerfectoidField p K` : A perfectoid field is a perfectoid ring that is also a field.

## Implementation notes

The Frobenius surjectivity condition is expressed directly as:
for all power-bounded `x`, there exists power-bounded `y` and `z` with `x = y^p + ϖ·z`
and `z` power-bounded. This avoids forming the quotient ring `A°/ϖ` and establishing
`CharP` on it, which would require considerable typeclass infrastructure.

The condition `ϖ^p | p` is expressed as: there exists a power-bounded `c` with
`(p : A) = c * ϖ^p`. This says `p/ϖ^p ∈ A°`, which is the standard formulation.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], Definition 3.5
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7
-/

open TopologicalRing ValuationSpectrum

universe u

/-! ### Perfectoid rings -/

/-- A Tate ring `A` is a **perfectoid ring** (for a prime `p`) if:

1. `A` is complete and separated (T₀),
2. `A` is uniform (A° is bounded),
3. there exists a pseudo-uniformizer `ϖ` that is power-bounded, such that `ϖ^p | p`
   in `A°` (i.e., `p = c · ϖ^p` for some power-bounded `c`), and
4. the `p`-th power (Frobenius) map is surjective on `A°/ϖ` (i.e., for every
   power-bounded `x`, there exist power-bounded `y, z` with `x = y^p + ϖ · z`).

(Scholze, *Perfectoid Spaces*, Definition 3.5) -/
class IsPerfectoidRing (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] : Prop
    extends IsTateRing A where
  /-- The ring is complete with respect to its uniform structure. -/
  complete : CompleteSpace A
  /-- The topology is T₀ (separated). -/
  t0 : T0Space A
  /-- The ring is uniform: `A°` is bounded. -/
  uniform : IsUniform A
  /-- There exists a pseudo-uniformizer `ϖ` that is power-bounded, with `ϖ^p | p` in `A°`
  and Frobenius surjective on `A°/ϖ`. -/
  exists_pseudoUniformizer :
    ∃ (ϖ : PseudoUniformizer A),
      -- ϖ is power-bounded
      IsPowerBounded (ϖ.val : A) ∧
      -- ϖ^p divides p in A°: there exists power-bounded c with p = c · ϖ^p
      (∃ c : A, IsPowerBounded c ∧ (p : A) = c * ((ϖ.val : A) ^ p)) ∧
      -- Frobenius is surjective on A°/ϖ: for every power-bounded x,
      -- there exist power-bounded y, z with x = y^p + ϖ · z
      (∀ x : A, IsPowerBounded x →
        ∃ y : A, IsPowerBounded y ∧
          ∃ z : A, IsPowerBounded z ∧ x = y ^ p + (ϖ.val : A) * z)

/-! ### Perfectoid fields -/

/-- A **perfectoid field** is a field that is also a perfectoid ring
(Scholze, *Perfectoid Spaces*, Definition 3.5). -/
class IsPerfectoidField (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [UniformSpace K] [IsLinearTopology K K] : Prop
    extends IsPerfectoidRing p K where

/-! ### Basic properties -/

namespace IsPerfectoidRing

/-- Extract a pseudo-uniformizer with the perfectoid property from a perfectoid ring. -/
noncomputable def perfectoidPseudoUniformizer (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    PseudoUniformizer A :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose

/-- The perfectoid pseudo-uniformizer is power-bounded. -/
theorem perfectoidPseudoUniformizer_isPowerBounded (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    IsPowerBounded ((perfectoidPseudoUniformizer p A).val : A) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.1

/-- The perfectoid pseudo-uniformizer satisfies ϖ^p | p. -/
theorem perfectoidPseudoUniformizer_divides_p (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∃ c : A, IsPowerBounded c ∧
      (p : A) = c * (((perfectoidPseudoUniformizer p A).val : A) ^ p) :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.2.1

/-- Frobenius is surjective on A°/ϖ for the perfectoid pseudo-uniformizer. -/
theorem perfectoidPseudoUniformizer_frobenius_surj (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] :
    ∀ x : A, IsPowerBounded x →
      ∃ y : A, IsPowerBounded y ∧
        ∃ z : A, IsPowerBounded z ∧
          x = y ^ p + ((perfectoidPseudoUniformizer p A).val : A) * z :=
  (IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)).choose_spec.2.2

/-! ### p-adic completeness of A° -/

/-- **The power-bounded subring of a perfectoid ring is `p`-adically complete.**

Mathematically, this follows from three facts:
1. The `(p)`-adic filtration `p^n · A°` is cofinal with the `ϖ`-adic filtration
   (since `p = c · ϖ^p` with `c, ϖ ∈ A°`).
2. The `ϖ`-adic topology on `A°` agrees with the subspace topology from `A`.
3. `A°` is complete in the subspace topology (it is closed in the complete ring `A`).

The proof of `IsHausdorff` uses: if `x ∈ p^n A°` for all `n`, then
`x ∈ ϖ^{np} · A°` for all `n`, and since `ϖ` is top. nilpotent and `A°` is
bounded, `x` is in every neighborhood of `0`, hence `x = 0` by T₀.

The proof of `IsPrecomplete` uses: a `p`-adic Cauchy sequence is also Cauchy
in the subspace topology (by the cofinality above), hence converges in `A°`.

(Scholze, *Perfectoid Spaces*, implicit in §3) -/
private abbrev PBSubring (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] := ↥(powerBoundedSubring.toSubring A)

private abbrev pIdeal (p : ℕ) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :=
  Ideal.span {(p : PBSubring A)}

/-- **IsHausdorff**: `⋂_n p^n A° = {0}`.

If `x ∈ p^n A°` for all `n`, then `(x : A) = (c·ϖ^p)^n · yₙ` for power-bounded
`yₙ`. Since `ϖ` is topologically nilpotent and `A°` is bounded, `(x : A)` is in
every neighborhood of 0, hence `(x : A) = 0` by T₀. -/
private theorem isHausdorff_pIdeal (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsHausdorff (pIdeal p A) (PBSubring A) := by
  constructor
  intro x hx
  -- Extract perfectoid data: ϖ (top. nilp. unit), c (power-bounded), p = c * ϖ^p
  obtain ⟨ϖ, hϖ_pb, ⟨c, hc_pb, hpc⟩, _⟩ :=
    IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)
  -- x ∈ (Ideal.span {p})^n • ⊤ for all n, i.e., p^n | x in A°
  have hx_mem : ∀ n : ℕ, (x : A) ∈ (Set.range (fun y : PBSubring A => (p : A) ^ n * (y : A))) := by
    intro n
    have := (SModEq.sub_mem.mp (hx n))
    simp only [sub_zero] at this
    -- x ∈ (Ideal.span {p})^n • ⊤ in A°, i.e. p^n ∣ x in A°
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by push_cast [hy]; ring⟩
  -- Show (x : A) is in every neighborhood of 0
  -- Using: (x : A) = (c * ϖ^p)^n * y_n, A° is bounded, ϖ top. nilp.
  have hx_zero : (x : A) = 0 := by
    -- Show 0 ∈ closure {(x : A)}, hence x = 0 by T₁ (from T₀ + UniformSpace)
    haveI := IsPerfectoidRing.t0 (p := p) (A := A)
    haveI := IsPerfectoidRing.uniform (p := p) (A := A)
    suffices h_mem_nhds : ∀ U ∈ nhds (0 : A), (x : A) ∈ U by
      have h0 : (0 : A) ∈ closure ({(x : A)} : Set A) :=
        mem_closure_iff_nhds.mpr fun U hU => ⟨(x : A), h_mem_nhds U hU, Set.mem_singleton _⟩
      rwa [IsClosed.closure_eq isClosed_singleton, Set.mem_singleton_iff, eq_comm] at h0
    intro U hU
    -- A° is bounded: ∃ V ∈ nhds 0, A° * V ⊆ U
    obtain ⟨V, hV, hAV⟩ :=
      IsUniform.isBounded_powerBounded (A := A) U hU
    -- ϖ^p is topologically nilpotent (since ϖ is, and (ϖ^p)^n = ϖ^{pn} → 0)
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hϖp_tn : IsTopologicallyNilpotent ((ϖ.val : A) ^ p) := by
      rw [IsTopologicallyNilpotent]; simp_rw [← pow_mul]
      exact (ϖ.property).comp
        (Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.mul_le_mul_left p h)
          fun b => ⟨b, Nat.le_mul_of_pos_left _ hp_pos⟩)
    -- c^n is power-bounded for all n (A° is a subring, c ∈ A°)
    have hcn_pb : ∀ m : ℕ, IsPowerBounded (c ^ m) := by
      intro m; induction m with
      | zero => simpa using isPowerBounded_one
      | succ k ih => simpa [pow_succ] using isPowerBounded_mul ih hc_pb
    -- Pick n with (ϖ^p)^n ∈ V
    obtain ⟨n, hn⟩ := hϖp_tn.exists_pow_mem_of_mem_nhds hV
    -- (x : A) = (p : A)^n * y for some y ∈ A°
    obtain ⟨y, hy⟩ := hx_mem n
    -- c^n * y ∈ A° (product of power-bounded elements)
    have hcy_pb : IsPowerBounded (c ^ n * (y : A)) := isPowerBounded_mul (hcn_pb n) y.property
    -- Rewrite: (x : A) = (c * ϖ^p)^n * y = (c^n * y) * (ϖ^p)^n
    have hx_eq : (x : A) = c ^ n * (y : A) * ((ϖ.val : A) ^ p) ^ n := by
      rw [← hy, hpc]; ring
    -- (c^n * y) * (ϖ^p)^n ∈ A° * V ⊆ U
    rw [hx_eq]; exact hAV (Set.mul_mem_mul hcy_pb hn)
  -- Conclude x = 0 in A°
  exact Subtype.val_injective hx_zero

/-- **IsPrecomplete**: `p`-adic Cauchy sequences in `A°` converge. -/
private theorem isPrecomplete_pIdeal (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsPrecomplete (pIdeal p A) (PBSubring A) := by
  sorry

instance instIsAdicComplete (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
    IsAdicComplete (pIdeal p A) (PBSubring A) :=
  { toIsHausdorff := isHausdorff_pIdeal p A
    toIsPrecomplete := isPrecomplete_pIdeal p A }

/-! ### Sorry'd deep theorems -/

/-- **Perfectoid rings are stably uniform** (Scholze, *Perfectoid Spaces*, Theorem 5.2).

This is a deep result: the key step is to show that for any rational localization
`R(T/s)` of a perfectoid ring, the completed localization is again uniform. The
proof goes through almost mathematics and tilting. -/
theorem toIsStablyUniform (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [HasRestrictionMaps A] :
    IsStablyUniform A := sorry

/-- **Perfectoid rings are sheafy** (Scholze, *Perfectoid Spaces*, Theorem 6.3).

This follows from stable uniformity: Buzzard--Verberkmoes showed that stably
uniform Tate rings are sheafy. -/
theorem toIsSheafy (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]
    [PlusSubring A] [HasRestrictionMaps A] :
    IsSheafy A := sorry

end IsPerfectoidRing
