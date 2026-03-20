/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.LinearTopology

/-!
# Bounded Subsets and Power-Bounded Elements

We define **bounded subsets**, **power-bounded elements**, and **topologically nilpotent
elements** for topological rings, following §5 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `TopologicalRing.IsBounded S` : A subset `S` of a topological ring is bounded if for every
  neighbourhood `U` of `0`, there exists a neighbourhood `V` of `0` with `S * V ⊆ U`
  (Definition 5.27 of Wedhorn).
* `TopologicalRing.IsPowerBounded a` : An element `a` is power-bounded if `{aⁿ | n ∈ ℕ}` is
  bounded (Definition 5.27 of Wedhorn).
* `TopologicalRing.powerBoundedSubring A` : The set `A°` of all power-bounded elements.
* `TopologicalRing.topologicallyNilpotentElements A` : The set `A°°` of all topologically
  nilpotent elements.

## Main results

* `IsBounded.subset` : Subsets of bounded sets are bounded.
* `IsBounded.union` : Union of bounded sets is bounded.
* `IsBounded.mul` : Product of bounded sets is bounded.
* `IsBounded.add` : Sum of bounded sets is bounded.
* `isPowerBounded_add` : In a non-archimedean ring, the sum of power-bounded elements is
  power-bounded (Proposition 5.30(3) of Wedhorn).
* `powerBoundedSubring.toSubring` : `A°` is a subring in a non-archimedean ring
  (Proposition 5.30(3) of Wedhorn).
* `IsTopologicallyNilpotent.isPowerBounded` : Topologically nilpotent implies power-bounded
  (Remark 5.28(4) of Wedhorn).
* `IsPowerBounded.isTopologicallyNilpotent_mul` : Product of power-bounded and topologically
  nilpotent is topologically nilpotent (Remark 5.28(5) of Wedhorn).
* `IsTopologicallyNilpotent.of_pow` : `A°°` is radical: if `a^m ∈ A°°` then `a ∈ A°°`
  (Proposition 5.30(4) of Wedhorn).
* `IsBounded.isPowerBounded_of_isIntegral` : `A°` is integrally closed
  (Proposition 5.30(4) of Wedhorn).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 5.25, Definition 5.27,
  Proposition 5.30
-/

open Filter Topology Pointwise Polynomial

namespace TopologicalRing

/-! ### Bounded subsets -/

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A subset is bounded if for every nhd `U` of `0`, some nhd `V` satisfies `S * V ⊆ U`. -/
def IsBounded (S : Set A) : Prop :=
  ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A), S * V ⊆ U

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set A} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  fun U hU ↦ let ⟨V, hV, hSV⟩ := hS U hU; ⟨V, hV, (Set.mul_subset_mul_right hTS).trans hSV⟩

/-- The empty set is bounded. -/
theorem isBounded_empty : IsBounded (∅ : Set A) :=
  fun U _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- The singleton `{0}` is bounded. -/
theorem isBounded_singleton_zero : IsBounded ({0} : Set A) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by
    obtain ⟨a, rfl, _, _, rfl⟩ := Set.mem_mul.mp hx; simp [mem_of_mem_nhds hU]⟩

/-- The pair `{0, 1}` is bounded. -/
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set A) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [zero_mul]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp ha, one_mul]⟩

/-- Union of two bounded sets is bounded (Remark 5.28(3)). -/
theorem IsBounded.union {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  intro U hU
  obtain ⟨V₁, hV₁, hSV⟩ := hS U hU; obtain ⟨V₂, hV₂, hTV⟩ := hT U hU
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
  rw [Set.union_mul]; exact Set.union_subset
    ((Set.mul_subset_mul_left Set.inter_subset_left).trans hSV)
    ((Set.mul_subset_mul_left Set.inter_subset_right).trans hTV)

/-- Product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  intro U hU
  obtain ⟨W, hW, hTW⟩ := hT U hU; obtain ⟨V, hV, hSV⟩ := hS W hW
  exact ⟨V, hV, mul_comm S T ▸ mul_assoc T S V ▸ (Set.mul_subset_mul_left hSV).trans hTW⟩

/-- Every singleton is bounded (Remark 5.28(1)). -/
theorem isBounded_singleton [IsTopologicalRing A] (a : A) : IsBounded ({a} : Set A) := by
  intro U hU
  refine ⟨(a * ·) ⁻¹' U,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simp [hU]), ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩; rwa [Set.mem_singleton_iff.mp hb]

/-- Every finite subset is bounded (Remark 5.28(1)). -/
theorem isBounded_finite [IsTopologicalRing A] {S : Set A} (hS : S.Finite) :
    IsBounded S := by
  refine @Set.Finite.induction_on A (fun s _ ↦ IsBounded s) S hS ?_ ?_
  · exact isBounded_empty
  · intro a s _ _ ih; exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

/-! ### Power-bounded elements -/

/-- An element is power-bounded if `{aⁿ | n}` is bounded (Definition 5.27). -/
def IsPowerBounded (a : A) : Prop :=
  IsBounded (Set.range (a ^ · : ℕ → A))

/-- The set `A°` of all power-bounded elements. -/
def powerBoundedSubring (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsPowerBounded a}

/-- `0` is power-bounded. -/
theorem isPowerBounded_zero : IsPowerBounded (0 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩
  rcases n with _ | n <;> simp [zero_pow]

/-- `1` is power-bounded. -/
theorem isPowerBounded_one : IsPowerBounded (1 : A) := by
  apply isBounded_pair_zero_one.subset; rintro _ ⟨n, rfl⟩; simp

/-- `-a` is power-bounded if `a` is (Prop 5.30(3)). -/
theorem isPowerBounded_neg [IsTopologicalRing A] {a : A} (ha : IsPowerBounded a) :
    IsPowerBounded (-a) := by
  apply (((isBounded_singleton (-1)).union (isBounded_singleton 1)).mul ha).subset
  rintro _ ⟨n, rfl⟩; change (-a) ^ n ∈ _; rw [neg_pow]
  exact Set.mul_mem_mul (by rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
    simp [hk, pow_succ]) ⟨n, rfl⟩

/-- `a * b` is power-bounded if `a` and `b` are (Prop 5.30(3)). -/
theorem isPowerBounded_mul {a b : A}
    (ha : IsPowerBounded a) (hb : IsPowerBounded b) : IsPowerBounded (a * b) := by
  apply (ha.mul hb).subset; rintro _ ⟨n, rfl⟩
  simp only [mul_pow]; exact Set.mul_mem_mul ⟨n, rfl⟩ ⟨n, rfl⟩

/-- Sum of two power-bounded elements is power-bounded in a nonarchimedean ring (Prop 5.30(3)). -/
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
  refine Submodule.sum_mem J fun m _ ↦ ?_
  rw [show a ^ m * b ^ (n - m) * ↑(n.choose m) * v =
      ↑(n.choose m) * (a ^ m * b ^ (n - m) * v) by ring]
  exact Ideal.mul_mem_left J _ (hSV (Set.mul_mem_mul (Set.mul_mem_mul ⟨m, rfl⟩ ⟨n - m, rfl⟩) hv))

/-- `A°` is a subring in a nonarchimedean topological ring (Prop 5.30(3)). -/
def powerBoundedSubring.toSubring (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] : Subring A where
  carrier := powerBoundedSubring A
  mul_mem' := isPowerBounded_mul
  one_mem' := isPowerBounded_one
  add_mem' := isPowerBounded_add
  zero_mem' := isPowerBounded_zero
  neg_mem' := isPowerBounded_neg

/-! ### Topologically nilpotent elements -/

/-- The set `A°°` of all topologically nilpotent elements (Definition 5.25). -/
def topologicallyNilpotentElements (A : Type*) [CommRing A] [TopologicalSpace A] : Set A :=
  {a : A | IsTopologicallyNilpotent a}

/-- Topologically nilpotent implies power-bounded (Remark 5.28(4)). -/
theorem IsTopologicallyNilpotent.isPowerBounded [IsTopologicalRing A] {a : A}
    (ha : IsTopologicallyNilpotent a) : IsPowerBounded a := by
  intro U hU
  have hmul : (fun p : A × A ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_mul.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hmul
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hmul
  obtain ⟨N, hN⟩ := (ha.eventually hU₁).exists_forall_of_atTop
  have hfin (i : Fin N) : ∃ V ∈ 𝓝 (0 : A), {a ^ (i : ℕ)} * V ⊆ U :=
    isBounded_singleton (a ^ (i : ℕ)) U hU
  choose V hV_mem hV_sub using hfin
  refine ⟨U₂ ∩ ⋂ i, V i, inter_mem hU₂ (Filter.iInter_mem.mpr hV_mem), ?_⟩
  intro x hx; obtain ⟨_, ⟨n, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.mp hx
  by_cases hn : n < N
  · exact hV_sub ⟨n, hn⟩ (Set.mem_mul.mpr ⟨a ^ n, rfl, c, Set.mem_iInter.mp hc.2 ⟨n, hn⟩, rfl⟩)
  · exact hprod (Set.mk_mem_prod (hN n (by omega)) hc.1)

/-- `A°°` is contained in `A°` (Remark 5.28(4)). -/
theorem topologicallyNilpotentElements_subset_powerBoundedSubring [IsTopologicalRing A] :
    topologicallyNilpotentElements A ⊆ powerBoundedSubring A :=
  fun _ ↦ IsTopologicallyNilpotent.isPowerBounded

/-- Product of power-bounded and topologically nilpotent is topologically nilpotent. -/
theorem IsPowerBounded.isTopologicallyNilpotent_mul [IsTopologicalRing A] {a b : A}
    (ha : IsPowerBounded a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) := by
  intro U hU; obtain ⟨V, hV, hSV⟩ := ha U hU
  rw [Filter.mem_map]; exact Filter.mem_of_superset (Filter.mem_map.mp (hb hV)) fun n hn ↦
    show (a * b) ^ n ∈ U from mul_pow a b n ▸ hSV (Set.mul_mem_mul ⟨n, rfl⟩ hn)

/-- `A°°` is radical: `a ^ m ∈ A°°` implies `a ∈ A°°` (Prop 5.30(4)). -/
theorem IsTopologicallyNilpotent.of_pow [IsTopologicalRing A] {a : A} {m : ℕ} (hm : 0 < m)
    (ha : IsTopologicallyNilpotent (a ^ m)) : IsTopologicallyNilpotent a := by
  have hfin : IsBounded (Set.range fun i : Fin m ↦ a ^ (i : ℕ)) :=
    isBounded_finite (Set.finite_range _)
  intro U hU
  obtain ⟨V, hV, hSV⟩ := hfin U hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (ha hV)
  refine Filter.mem_atTop_sets.mpr ⟨m * N, fun n hn ↦ ?_⟩
  rw [Set.mem_preimage, show a ^ n = a ^ (n % m) * (a ^ m) ^ (n / m) by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]]
  exact hSV (Set.mul_mem_mul ⟨⟨n % m, Nat.mod_lt n hm⟩, rfl⟩
    (hN _ ((Nat.le_div_iff_mul_le hm).mpr (by linarith))))

/-! ### Proposition 5.30 — A° is integrally closed -/

omit [TopologicalSpace A] in
/-- `aⁿ ∈ B` for positive `n` implies `a` is integral over `B`. -/
theorem isIntegral_of_pow_mem (B : Subring A) {a : A} {n : ℕ} (hn : 0 < n)
    (ha : a ^ n ∈ B) : IsIntegral (↥B) a :=
  ⟨X ^ n - C ⟨a ^ n, ha⟩, monic_X_pow_sub_C _ (by omega), by
    simp [sub_eq_zero]; rfl⟩

/-- Sum of two bounded sets is bounded. -/
theorem IsBounded.add [IsTopologicalRing A] {S T : Set A}
    (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S + T) := by
  intro U hU
  have hadd : (fun p : A × A ↦ p.1 + p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_add.continuousAt.preimage_mem_nhds (by simp [hU])
  rw [nhds_prod_eq] at hadd
  obtain ⟨U₁, hU₁, U₂, hU₂, hprod⟩ := Filter.mem_prod_iff.mp hadd
  obtain ⟨V₁, hV₁, hSV⟩ := hS U₁ hU₁; obtain ⟨V₂, hV₂, hTV⟩ := hT U₂ hU₂
  refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, fun _ hx ↦ ?_⟩
  obtain ⟨_, ⟨s₀, hs₀, t₀, ht₀, rfl⟩, v, hv, rfl⟩ := Set.mem_mul.mp hx
  rw [add_mul]; exact hprod (Set.mk_mem_prod
    (hSV (Set.mul_mem_mul hs₀ hv.1))
    (hTV (Set.mul_mem_mul ht₀ hv.2)))

/-- A finite sum of bounded sets is bounded. -/
theorem isBounded_finset_sum [IsTopologicalRing A] {ι : Type*} (s : Finset ι)
    (f : ι → Set A) (hf : ∀ i ∈ s, IsBounded (f i)) :
    IsBounded (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isBounded_singleton_zero
  | insert _ _ hni ih => rw [Finset.sum_insert hni]; exact
      (hf _ (Finset.mem_insert_self _ _)).add (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

omit [TopologicalSpace A] in
/-- Strong induction: every power `a ^ n` is a `B`-linear combination of `a ^ 0, …, a ^ (N-1)`,
given that `a ^ N` satisfies the monic relation `hp_rel`. Requires `N ≠ 0`. -/
private theorem pow_eq_lincomb_of_monic_rel {B : Subring A} {a : A} {N : ℕ}
    {p : (↥B)[X]} (_hN : N ≠ 0)
    (hp_rel : a ^ N = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ i)) :
    ∀ n, ∃ c : ℕ → ↥B, a ^ n = ∑ j ∈ Finset.range N, (c j : A) * a ^ j := by
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
  by_cases hn : n < N
  · classical exact ⟨fun j ↦ if j = n then 1 else 0, by
      simp [apply_ite (Subtype.val), Finset.sum_ite_eq', Finset.mem_range.mpr hn]⟩
  · push_neg at hn
    choose d hd using fun i (hi : i ∈ Finset.range N) ↦
      ih (i + (n - N)) (by rw [Finset.mem_range] at hi; omega)
    refine ⟨fun j ↦ -(∑ i ∈ (Finset.range N).attach, p.coeff ↑i * d ↑i i.2 j), ?_⟩
    have step : a ^ n = -(∑ i ∈ (Finset.range N).attach,
        (p.coeff (i : ℕ) : A) * ∑ j ∈ Finset.range N, (d ↑i i.2 j : A) * a ^ j) := by
      calc a ^ n = a ^ (n - N) * a ^ N := by rw [← pow_add, Nat.sub_add_cancel hn]
        _ = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ (i + (n - N))) := by
            rw [hp_rel, mul_neg, neg_inj, Finset.mul_sum]; congr 1
            ext i; rw [mul_comm (a ^ (n - N)), mul_assoc, ← pow_add]
        _ = _ := by rw [← Finset.sum_attach]; congr 1
                    exact Finset.sum_congr rfl fun i _ ↦ by rw [hd ↑i i.2]
    rw [step]; simp_rw [Finset.mul_sum]
    rw [neg_inj.mpr (Finset.sum_comm ..), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast; simp only [Finset.sum_mul, neg_mul]; congr 1
    exact Finset.sum_congr rfl fun ⟨i, _⟩ _ ↦ by ring

/-- `A°` is integrally closed: integral over bounded implies power-bounded (Prop 5.30(4)). -/
theorem IsBounded.isPowerBounded_of_isIntegral [IsTopologicalRing A] {B : Subring A}
    (hB : IsBounded (B : Set A)) {a : A} (ha : IsIntegral (↥B) a) :
    IsPowerBounded a := by
  obtain ⟨p, hp_monic, hp_eval⟩ := ha
  set N := p.natDegree; set S := ∑ i ∈ Finset.range N, (B : Set A) * {a ^ i} with hS_def
  refine (isBounded_finset_sum (Finset.range N) (fun i ↦ (B : Set A) * {a ^ i})
    fun i _ ↦ hB.mul (isBounded_singleton _)).subset ?_
  rintro _ ⟨n, rfl⟩
  have hp_rel : a ^ N = -(∑ i ∈ Finset.range N, (p.coeff i : A) * a ^ i) := by
    have h := hp_eval; rw [eval₂_eq_sum_range, Finset.sum_range_succ] at h
    rw [hp_monic.coeff_natDegree, map_one, one_mul, add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  suffices key : ∀ n, ∃ c : ℕ → ↥B, a ^ n = ∑ j ∈ Finset.range N, (c j : A) * a ^ j by
    change a ^ n ∈ S; obtain ⟨c, hc⟩ := key n; rw [hc, hS_def]
    exact Set.finset_sum_mem_finset_sum _ _ _ fun j _ ↦ Set.mul_mem_mul (Subtype.coe_prop _) rfl
  by_cases hN : N = 0
  · intro n; refine ⟨0, ?_⟩; simp only [hN, Finset.range_zero, Finset.sum_empty]
    have h1 : (1 : A) = 0 := by simpa [hN] using hp_rel
    induction n with
    | zero => simpa using h1
    | succ m ihm => rw [pow_succ, ihm, zero_mul]
  exact pow_eq_lincomb_of_monic_rel hN hp_rel

end TopologicalRing
