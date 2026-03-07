/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».AdicSpectrum
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.LinearTopology

/-!
# Affinoid Rings

We define **bounded subsets**, **power-bounded elements**, **topologically nilpotent elements**,
and **rings of integral elements** for topological rings, following §5 and Definition 7.14 of
[Wedhorn, *Adic Spaces*].

We then prove several results from Proposition 5.30 and Remark 7.15:
* `A°` is a subring of `A` that is integrally closed (Proposition 5.30(3)–(4)).
* Any ring of integral elements is contained in `A°` (Remark 7.15(1)).
* An open, integrally closed subring contains all topologically nilpotent elements
  (Remark 7.15(2), forward direction).

## Main definitions

* `TopologicalRing.IsBounded S` : A subset `S` of a topological ring is bounded if for every
  neighbourhood `U` of `0`, there exists a neighbourhood `V` of `0` with `S * V ⊆ U`
  (Definition 5.27 of Wedhorn).
* `TopologicalRing.IsPowerBounded a` : An element `a` is power-bounded if `{aⁿ | n ∈ ℕ}` is
  bounded (Definition 5.27 of Wedhorn).
* `TopologicalRing.powerBoundedSubring A` : The set `A°` of all power-bounded elements.
* `TopologicalRing.topologicallyNilpotentElements A` : The set `A°°` of all topologically
  nilpotent elements.
* `Spv.IsRingOfIntegralElements B` : The subring `B` is a ring of integral elements
  (Definition 7.14(1) of Wedhorn).
* `Spv.IsAffinoidRing A` : The pair `(A, A⁺)` is an affinoid ring
  (Definition 7.14 of Wedhorn).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 5.25, Definition 5.27,
  Proposition 5.30, Definition 7.14, Remark 7.15
-/

open Filter Topology Pointwise Polynomial

namespace TopologicalRing

/-! ### Bounded subsets -/

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A subset `S` of a topological ring is *bounded* if for every neighbourhood `U` of `0`,
there exists a neighbourhood `V` of `0` such that `S * V ⊆ U` (Definition 5.27 of Wedhorn). -/
def IsBounded (S : Set A) : Prop :=
  ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), S * V ⊆ U

/-- A subset of a bounded set is bounded. -/
theorem IsBounded.subset {S T : Set A} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦ let ⟨V, hV, hSV⟩ := hS U hU; ⟨V, hV, (Set.mul_subset_mul_right hTS).trans hSV⟩

/-- The empty set is bounded. -/
theorem isBounded_empty : IsBounded (∅ : Set A) :=
  fun U _ ↦ ⟨Set.univ, univ_mem, by simp [Set.empty_mul]⟩

/-- The singleton `{0}` is bounded. -/
theorem isBounded_singleton_zero : IsBounded ({0} : Set A) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by
    obtain ⟨a, ha, _, _, rfl⟩ := Set.mem_mul.mp hx
    rw [Set.mem_singleton_iff.mp ha, zero_mul]; exact mem_of_mem_nhds hU⟩

/-- The pair `{0, 1}` is bounded. -/
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set A) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [zero_mul]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp ha, one_mul]⟩

/-- The union of two bounded sets is bounded (Remark 5.28(3) of Wedhorn). -/
theorem IsBounded.union {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  intro U hU
  obtain ⟨V₁, hV₁, hSV⟩ := hS U hU; obtain ⟨V₂, hV₂, hTV⟩ := hT U hU
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  rw [Set.union_mul]; exact Set.union_subset
    ((Set.mul_subset_mul_left Set.inter_subset_left).trans hSV)
    ((Set.mul_subset_mul_left Set.inter_subset_right).trans hTV)

/-- The product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU; obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, by calc S * T * V = T * (S * V) := by rw [mul_comm S T, mul_assoc]
    _ ⊆ T * W := Set.mul_subset_mul_left hSV
    _ ⊆ U := hTW⟩

/-- Every singleton is bounded in a topological ring (Remark 5.28(1) of Wedhorn). -/
theorem isBounded_singleton [IsTopologicalRing A] (a : A) : IsBounded ({a} : Set A) := by
  intro U hU
  refine ⟨(a * ·) ⁻¹' U,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simp [hU]), ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩; rwa [Set.mem_singleton_iff.mp hb]

/-! ### Power-bounded elements -/

/-- An element `a` of a topological ring is *power-bounded* if the set `{aⁿ | n ∈ ℕ}` is
bounded (Definition 5.27 of Wedhorn). -/
def IsPowerBounded (a : A) : Prop :=
  IsBounded (Set.range (a ^ · : ℕ → A))

/-- The set `A°` of all power-bounded elements in a topological ring. -/
def powerBoundedSubring (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsPowerBounded a}

/-- `0` is power-bounded. -/
theorem isPowerBounded_zero : IsPowerBounded (0 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩
  rcases n with _ | n <;> simp [zero_pow (Nat.succ_ne_zero _)]

/-- `1` is power-bounded. -/
theorem isPowerBounded_one : IsPowerBounded (1 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩; simp

/-- `-a` is power-bounded if `a` is (Proposition 5.30(3) of Wedhorn, partial). -/
theorem isPowerBounded_neg [IsTopologicalRing A] {a : A} (ha : IsPowerBounded a) :
    IsPowerBounded (-a) := by
  apply (((isBounded_singleton (-1)).union (isBounded_singleton 1)).mul ha).subset
  rintro _ ⟨n, rfl⟩; change (-a) ^ n ∈ _; rw [neg_pow]
  exact Set.mul_mem_mul (by rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp [hk, pow_succ]) ⟨n, rfl⟩

/-- `a * b` is power-bounded if `a` and `b` are (Proposition 5.30(3) of Wedhorn, partial). -/
theorem isPowerBounded_mul {a b : A}
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  apply (ha.mul hb).subset; rintro _ ⟨n, rfl⟩
  change (a * b) ^ n ∈ _; rw [mul_pow]; exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

/-- In a non-archimedean topological ring, the sum of two power-bounded elements is
power-bounded (Proposition 5.30(3) of Wedhorn). The non-archimedean hypothesis
(`IsLinearTopology`) is essential: in `ℝ`, `A° = [-1,1]` is not closed under addition. -/
theorem isPowerBounded_add [IsTopologicalRing A] [IsLinearTopology A A]
    {a b : A} (ha : IsPowerBounded a) (hb : IsPowerBounded b) :
    IsPowerBounded (a + b) := by
  have hS := ha.mul hb
  intro U hU
  obtain ⟨J, hJ, hJU⟩ := (IsLinearTopology.hasBasis_open_ideal (R := A)).mem_iff.mp hU
  obtain ⟨V, hV, hSV⟩ := hS (J : Set A) (hJ.mem_nhds J.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, v, hv, rfl⟩
  apply hJU; change (a + b) ^ n * v ∈ _; rw [add_pow, Finset.sum_mul]
  refine Submodule.sum_mem J fun m _ => ?_
  rw [show a ^ m * b ^ (n - m) * ↑(n.choose m) * v =
      ↑(n.choose m) * (a ^ m * b ^ (n - m) * v) from by ring]
  exact Ideal.mul_mem_left J _ (hSV (Set.mul_mem_mul (Set.mul_mem_mul ⟨m, rfl⟩ ⟨n - m, rfl⟩) hv))

/-- `A°` is a subring of `A` in a non-archimedean topological ring
(Proposition 5.30(3) of Wedhorn). -/
def powerBoundedSubring.toSubring (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] : Subring A where
  carrier := powerBoundedSubring A
  mul_mem' ha hb := isPowerBounded_mul ha hb
  one_mem' := isPowerBounded_one
  add_mem' ha hb := isPowerBounded_add ha hb
  zero_mem' := isPowerBounded_zero
  neg_mem' ha := isPowerBounded_neg ha

/-! ### Topologically nilpotent elements -/

/-- The set `A°°` of all topologically nilpotent elements (Definition 5.25 of Wedhorn). -/
def topologicallyNilpotentElements (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsTopologicallyNilpotent a}

/-- A topologically nilpotent element is power-bounded (Remark 5.28(4) of Wedhorn).
The proof splits `{aⁿ}` into a finite head (handled by continuity of each `aⁱ * ·`) and a
tail converging to `0` (handled by continuity of multiplication at `(0, 0)`). -/
theorem IsTopologicallyNilpotent.isPowerBounded [IsTopologicalRing A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsPowerBounded a := by
  intro U hU
  have hmul : (fun p : A × A => p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hmul
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hmul
  have hev := ha.eventually hU₁; rw [Filter.Eventually, Filter.mem_atTop_sets] at hev
  obtain ⟨N, hN⟩ := hev
  have hfin (i : Fin N) : ∃ V ∈ 𝓝 (0 : A), {a ^ (i : ℕ)} * V ⊆ U := by
    refine ⟨(a ^ (i : ℕ) * ·) ⁻¹' U,
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simp [hU]), ?_⟩
    rintro _ ⟨b, hb, c, hc, rfl⟩; rwa [Set.mem_singleton_iff.mp hb]
  choose V hV_mem hV_sub using hfin
  refine ⟨U₂ ∩ ⋂ i, V i, inter_mem hU₂ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx; obtain ⟨_, ⟨n, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩ (Set.mem_mul.mpr ⟨a ^ n, rfl, c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, rfl⟩)
  · exact hprod (Set.mk_mem_prod (hN n (by omega)) hc.1)

/-- `A°°` is contained in `A°` (Remark 5.28(4) of Wedhorn). -/
theorem topologicallyNilpotentElements_subset_powerBoundedSubring [IsTopologicalRing A] :
    topologicallyNilpotentElements A ⊆ powerBoundedSubring A :=
  fun _ ha ↦ IsTopologicallyNilpotent.isPowerBounded ha

/-! ### Proposition 5.30 — A° is integrally closed -/

omit [TopologicalSpace A] in
/-- If `aⁿ ∈ B` for some positive `n`, then `a` is integral over `B`. -/
theorem isIntegral_of_pow_mem (B : Subring A) {a : A} {n : ℕ} (hn : 0 < n)
    (ha : a ^ n ∈ B) : IsIntegral (↥B) a :=
  ⟨X ^ n - C ⟨a ^ n, ha⟩, monic_X_pow_sub_C _ (by omega), by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]; rfl⟩

/-- The sum of two bounded sets is bounded. -/
theorem IsBounded.add [IsTopologicalRing A] {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S + T) := by
  intro U hU
  have hadd : (fun p : A × A => p.1 + p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_add.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hadd
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hadd
  obtain ⟨V₁, hV₁, hSV⟩ := hS U₁ hU₁; obtain ⟨V₂, hV₂, hTV⟩ := hT U₂ hU₂
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, fun _ hx => ?_⟩
  obtain ⟨_, ⟨s₀, hs₀, t₀, ht₀, rfl⟩, v, hv, rfl⟩ := Set.mem_mul.mp hx
  rw [add_mul]; exact hprod (Set.mk_mem_prod
    (hSV (Set.mul_mem_mul hs₀ (Set.mem_of_mem_inter_left hv)))
    (hTV (Set.mul_mem_mul ht₀ (Set.mem_of_mem_inter_right hv))))

/-- A finite sum of bounded sets is bounded. -/
theorem isBounded_finset_sum [IsTopologicalRing A] {ι : Type*} (s : Finset ι)
    (f : ι → Set A) (hf : ∀ i ∈ s, IsBounded (f i)) :
    IsBounded (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isBounded_singleton_zero
  | insert _ _ hni ih => rw [Finset.sum_insert hni]; exact
      (hf _ (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- `A°` is integrally closed in `A`: if `a` is integral over `A°` (viewed as a subring),
then `a ∈ A°` (Proposition 5.30(4) of Wedhorn, partial).

This partial result shows: if `a` is integral over a bounded subring `B`,
then `a` is power-bounded. The full Prop 5.30(4) requires that `A°` is a subring
(Prop 5.30(3)). -/
theorem IsBounded.isPowerBounded_of_isIntegral [IsTopologicalRing A] {B : Subring A}
    (hB : IsBounded (B : Set A)) {a : A} (ha : IsIntegral (↥B) a) :
    IsPowerBounded a := by
  obtain ⟨p, hp_monic, hp_eval⟩ := ha
  set N := p.natDegree; set S := ∑ i ∈ Finset.range N, (B : Set A) * {a ^ i} with hS_def
  refine (isBounded_finset_sum (Finset.range N) (fun i => (B : Set A) * {a ^ i})
    fun i _ => hB.mul (isBounded_singleton _)).subset ?_
  rintro _ ⟨n, rfl⟩
  have hp_rel : a ^ N = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ i) := by
    have h := hp_eval; rw [eval₂_eq_sum_range, Finset.sum_range_succ] at h
    simp only [hp_monic.coeff_natDegree, map_one, one_mul] at h
    rw [add_comm] at h; exact eq_neg_of_add_eq_zero_left h
  -- Reduce to: every a^n is a B-linear combination of {1, a, ..., a^(N-1)}
  suffices key : ∀ n, ∃ c : ℕ → ↥B, a ^ n = ∑ j ∈ Finset.range N, (c j : A) * a ^ j by
    change a ^ n ∈ S; obtain ⟨c, hc⟩ := key n; rw [hc, hS_def]
    exact Set.finset_sum_mem_finset_sum _ _ _ fun j _ => Set.mul_mem_mul (Subtype.coe_prop _) rfl
  by_cases hN : N = 0
  · intro n; refine ⟨0, ?_⟩; simp only [hN, Finset.range_zero, Finset.sum_empty]
    have h1 : (1 : A) = 0 := by simpa [hN] using hp_rel
    induction n with
    | zero => simpa using h1
    | succ m ihm => rw [pow_succ, ihm, zero_mul]
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
  by_cases hn : n < N
  · -- Base: a^n = δ_{n,j} * a^j
    classical exact ⟨fun j => if j = n then 1 else 0, by
      rw [Finset.sum_congr rfl fun j _ => show ((if j = n then (1 : ↥B) else 0 : ↥B) : A) *
          a ^ j = (if j = n then 1 else 0) * a ^ j from by congr 1; exact apply_ite _ _ _ _]
      simp [Finset.sum_ite_eq', Finset.mem_range.mpr hn]⟩
  · -- Inductive: use monic relation and substitute IH for each a^(i+(n-N))
    push_neg at hn
    choose d hd using fun i (hi : i ∈ Finset.range N) =>
      ih (i + (n - N)) (by rw [Finset.mem_range] at hi; omega)
    refine ⟨fun j => -(∑ i ∈ (Finset.range N).attach, p.coeff ↑i * d ↑i i.2 j), ?_⟩
    have step : a ^ n = -(∑ i ∈ (Finset.range N).attach,
        (p.coeff (i : ℕ) : A) * ∑ j ∈ Finset.range N, (d ↑i i.2 j : A) * a ^ j) := by
      calc a ^ n = a ^ (n - N) * a ^ N := by rw [← pow_add, Nat.sub_add_cancel hn]
        _ = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ (i + (n - N))) := by
            rw [hp_rel, mul_neg, neg_inj, Finset.mul_sum]; congr 1
            ext i; rw [mul_comm (a ^ (n - N)), mul_assoc, ← pow_add]
        _ = _ := by rw [← Finset.sum_attach]; congr 1
                    exact Finset.sum_congr rfl fun i _ => by rw [hd ↑i i.2]
    rw [step]; simp_rw [Finset.mul_sum]
    rw [show -(∑ x ∈ (Finset.range N).attach, ∑ x_1 ∈ Finset.range N,
          (p.coeff (x : ℕ) : A) * ((d ↑x x.2 x_1 : A) * a ^ x_1)) =
        -(∑ j ∈ Finset.range N, ∑ i ∈ (Finset.range N).attach,
          (p.coeff (i : ℕ) : A) * ((d ↑i i.2 j : A) * a ^ j)) from
      congr_arg Neg.neg (Finset.sum_comm ..),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; simp only [Finset.sum_mul, neg_mul]; congr 1
    exact Finset.sum_congr rfl fun ⟨i, _⟩ _ => by ring

end TopologicalRing

namespace Spv

section IntegralElements

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A subring `B` of a topological ring `A` is a *ring of integral elements*
(Definition 7.14(1) of Wedhorn) if:
1. `B` is open in `A`,
2. `B` is integrally closed in `A` (every `a ∈ A` integral over `B` lies in `B`),
3. `B ⊆ A°` (every element of `B` is power-bounded). -/
structure IsRingOfIntegralElements (B : Subring A) : Prop where
  /-- `B` is open in `A`. -/
  isOpen : IsOpen (B : Set A)
  /-- `B` is integrally closed in `A`. -/
  isIntegrallyClosed : ∀ a : A, IsIntegral (↥B) a → a ∈ B
  /-- `B ⊆ A°`. -/
  subset_powerBounded : (B : Set A) ⊆ TopologicalRing.powerBoundedSubring A

/-! ### Remark 7.15 -/

/-- Any ring of integral elements is contained in `A°` (Remark 7.15(1) of Wedhorn).
In particular, `A°` is the *largest* ring of integral elements. -/
theorem IsRingOfIntegralElements.le_powerBoundedSubring {B : Subring A}
    (hB : IsRingOfIntegralElements B) :
    (B : Set A) ⊆ TopologicalRing.powerBoundedSubring A :=
  hB.subset_powerBounded

/-- An open, integrally closed subring contains all topologically nilpotent elements
(Remark 7.15(2) of Wedhorn, forward direction: open ⟹ contains `A°°`).

If `B` is open in `A` and integrally closed, and `a` is topologically nilpotent, then
`aⁿ → 0` implies `aⁿ ∈ B` for large `n`, so `a` is integral over `B`, hence `a ∈ B`. -/
theorem topologicallyNilpotent_mem_of_isOpen_integrallyClosed
    (B : Subring A) (hB_open : IsOpen (B : Set A))
    (hB_ic : ∀ a : A, IsIntegral (↥B) a → a ∈ B)
    {a : A} (ha : IsTopologicallyNilpotent a) : a ∈ B := by
  have hB_nhds : (B : Set A) ∈ 𝓝 (0 : A) := hB_open.mem_nhds B.zero_mem
  obtain ⟨n, hn_mem, hn_ge⟩ := (ha.eventually hB_nhds |>.and
    (Filter.eventually_ge_atTop 1)).exists
  exact hB_ic a (TopologicalRing.isIntegral_of_pow_mem B (by omega) hn_mem)

/-- A ring of integral elements contains all topologically nilpotent elements
(consequence of Remark 7.15(2)). -/
theorem IsRingOfIntegralElements.topologicallyNilpotentElements_subset {B : Subring A}
    (hB : IsRingOfIntegralElements B) :
    TopologicalRing.topologicallyNilpotentElements A ⊆ (B : Set A) :=
  fun _ ha ↦ topologicallyNilpotent_mem_of_isOpen_integrallyClosed B hB.isOpen
    hB.isIntegrallyClosed ha

variable [PlusSubring A]

/-- A pair `(A, A⁺)` is an *affinoid ring* (Definition 7.14 of Wedhorn) if `A⁺` is a ring
of integral elements. -/
def IsAffinoidRing (A : Type*) [CommRing A] [TopologicalSpace A] [PlusSubring A] : Prop :=
  IsRingOfIntegralElements (A⁺)

end IntegralElements

end Spv
