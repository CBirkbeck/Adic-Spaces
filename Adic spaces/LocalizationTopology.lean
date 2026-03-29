/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».HuberRings
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# Localization Topology for Huber Rings

We construct the non-archimedean ring topology on `Localization.Away s` following §8.1 of Wedhorn.

## Main definitions

* `ValuationSpectrum.divByS t s` : The element `t/s` in `Localization.Away s`.
* `ValuationSpectrum.locSubring P T s` : The ring of definition `D = A₀[t₁/s, …, tₙ/s]`.
* `ValuationSpectrum.locIdeal P T s` : The ideal of definition `J = I · D` in `D`.
* `ValuationSpectrum.locNhd P T s n` : The `n`-th neighborhood `image(Jⁿ)` in `Aₛ`.
* `ValuationSpectrum.locBasis P T s` : The `RingSubgroupsBasis` structure.
* `ValuationSpectrum.locTopology P T s` : The resulting topology on `Aₛ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1
-/

open PairOfDefinition Pointwise

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The ring of definition `D` -/

/-- The element `t/s` in `Localization.Away s`. -/
noncomputable def divByS (t s : A) : Localization.Away s :=
  IsLocalization.mk' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

omit [TopologicalSpace A] in
/-- When `s = 1`, the fraction `t/1` equals `algebraMap t`. -/
theorem divByS_eq_algebraMap (t : A) :
    divByS t (1 : A) = algebraMap A (Localization.Away (1 : A)) t := by
  unfold divByS
  exact IsLocalization.mk'_one (M := Submonoid.powers (1 : A))
    (S := Localization.Away (1 : A)) t

/-- The ring of definition `D = A₀[t₁/s, …, tₙ/s]` of `Localization.Away s`
(§8.1 of Wedhorn). -/
noncomputable def locSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Subring (Localization.Away s) :=
  Subring.closure
    ((algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ∪
     Set.range (fun t : T ↦ divByS (t : A) s))

/-- The image of `A₀` under `algebraMap` is contained in `D`. -/
theorem algebraMap_A₀_subset_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) :
    (algebraMap A (Localization.Away s)) '' (P.A₀ : Set A) ⊆
      (locSubring P T s : Set (Localization.Away s)) :=
  Set.subset_union_left.trans Subring.subset_closure

/-- Each element `t/s` (for `t ∈ T`) belongs to `D`. -/
theorem divByS_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {t : A} (ht : t ∈ T) :
    divByS t s ∈ locSubring P T s :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

/-- An element of `A₀` maps into `D` under `algebraMap`. -/
theorem algebraMap_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {a : A} (ha : a ∈ P.A₀) :
    algebraMap A (Localization.Away s) a ∈ locSubring P T s :=
  algebraMap_A₀_subset_locSubring P T s ⟨a, ha, rfl⟩

/-! ### The ideal of definition `J` -/

/-- The ring homomorphism `A₀ →+* D` induced by `algebraMap`, restricted to codomain `D`. -/
noncomputable def algebraMapD (P : PairOfDefinition A) (T : Finset A)
    (s : A) : P.A₀ →+* (locSubring P T s) :=
  ((algebraMap A (Localization.Away s)).comp P.A₀.subtype).codRestrict
    (locSubring P T s)
    (fun a ↦ algebraMap_A₀_subset_locSubring P T s ⟨a, a.property, rfl⟩)

/-- The ideal of definition `J = I · D` in `D`. -/
noncomputable def locIdeal (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Ideal (locSubring P T s) :=
  Ideal.map (algebraMapD P T s) P.I

/-- The ideal of definition `J` is finitely generated. -/
theorem locIdeal_fg (P : PairOfDefinition A) (T : Finset A) (s : A) :
    (locIdeal P T s).FG :=
  P.fg.map _

/-! ### The neighborhood basis -/

/-- The `n`-th neighborhood of `0` in `Localization.Away s`: the image of `Jⁿ` in `Aₛ`. -/
noncomputable def locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : AddSubgroup (Localization.Away s) :=
  ((locIdeal P T s) ^ n).toAddSubgroup.map
    (locSubring P T s).subtype.toAddMonoidHom

/-- The neighborhoods are antitone: `m ≤ n → locNhd n ≤ locNhd m`. -/
theorem locNhd_antitone (P : PairOfDefinition A) (T : Finset A) (s : A) :
    Antitone (locNhd P T s) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

/-- `0 ∈ locNhd n` for all `n`. -/
theorem zero_mem_locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : (0 : Localization.Away s) ∈ locNhd P T s n :=
  ⟨0, (locIdeal P T s ^ n).zero_mem, map_zero _⟩

/-! ### The `RingSubgroupsBasis` -/

section Basis

variable [IsTopologicalRing A]

omit [IsTopologicalRing A] in
private theorem locNhd_mul (P : PairOfDefinition A) (T : Finset A)
    (s : A) (i : ℕ) :
    ∃ j, (locNhd P T s j : Set (Localization.Away s)) *
      (locNhd P T s j : Set (Localization.Away s)) ⊆
        (locNhd P T s i : Set (Localization.Away s)) := by
  refine ⟨i, ?_⟩
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  exact ⟨d₁ * d₂, Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (locIdeal P T s) i i ▸ Ideal.mul_mem_mul hd₁ hd₂),
    MulMemClass.coe_mul ..⟩

omit [IsTopologicalRing A] in
/-- Multiplying `1/s` by an element of `J^N` lands in the localization subring `D`. -/
private theorem locNhd_invS_mem (P : PairOfDefinition A) (T : Finset A) (s : A)
    (N : ℕ) (hN : ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    {d : locSubring P T s} (hd : d ∈ locIdeal P T s ^ N) :
    divByS 1 s * ↑d ∈ locSubring P T s := by
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I ^ N), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦ divByS 1 s * ↑d ∈ locSubring P T s)
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    change divByS 1 s * algebraMap A _ ↑b ∈ _
    rw [show divByS 1 s * algebraMap A (Localization.Away s) ↑b = divByS (↑b) s from by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers s) (S := Localization.Away s)
        (↑b : A), ← IsLocalization.mk'_mul, one_mul, mul_one]]
    exact hN b hb
  · simp [(locSubring P T s).zero_mem]
  · intro d1 d2 _ _ h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locSubring P T s).add_mem h1 h2
  · intro r d1 _ h1
    rw [show (↑(r • d1) : Localization.Away s) = ↑r * ↑d1 from MulMemClass.coe_mul ..,
        mul_left_comm]
    exact (locSubring P T s).mul_mem r.property h1

omit [IsTopologicalRing A] in
/-- Multiplying `1/s` by an element of `locNhd (n + N)` lands in `locNhd n`. -/
private theorem locNhd_invS_step (P : PairOfDefinition A) (T : Finset A) (s : A)
    (N : ℕ) (hN : ∀ b : P.A₀, b ∈ P.I ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    (n : ℕ) (y : Localization.Away s)
    (hy : y ∈ locNhd P T s (n + N)) : divByS 1 s * y ∈ locNhd P T s n := by
  obtain ⟨d, hd, rfl⟩ := hy
  change divByS 1 s * ↑d ∈ locNhd P T s n
  rw [Nat.add_comm, pow_add] at hd
  refine Submodule.mul_induction_on hd ?_ ?_
  · intro a ha b hb
    change divByS 1 s * (↑a * ↑b) ∈ locNhd P T s n
    rw [← mul_assoc]
    exact ⟨⟨divByS 1 s * ↑a, locNhd_invS_mem P T s N hN ha⟩ * b, Ideal.mul_mem_left _ _ hb,
      MulMemClass.coe_mul ..⟩
  · intro y1 y2 h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s n).add_mem h1 h2

/-- Multiplying `algebraMap a` by an element of a suitable `locNhd j` lands in `locNhd i`. -/
private theorem locNhd_algMap_step (P : PairOfDefinition A) (T : Finset A) (s : A)
    (i : ℕ) (a : A) :
    ∃ j, ∀ y ∈ locNhd P T s j,
      algebraMap A (Localization.Away s) a * y ∈ locNhd P T s i := by
  obtain ⟨m₀, -, hm₀⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (continuous_const_mul a |>.continuousAt.preimage_mem_nhds
      (by rw [mul_zero]; exact P.hasBasis_nhds_zero.mem_of_mem trivial (i := i)))
  refine ⟨m₀, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  change algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.I ^ m₀), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦
    algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i) ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hval⟩ := hm₀ ⟨b, hb, rfl⟩
    change algebraMap A _ a * algebraMap A _ ↑b ∈ _
    rw [← map_mul, show a * (↑b : A) = ↑c from hval.symm]
    exact ⟨algebraMapD P T s c,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc, rfl⟩
  · simp [(locNhd P T s i).zero_mem]
  · intro d1 d2 _ _ h1 h2
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s i).add_mem h1 h2
  · intro r d1 _ h1
    rw [show (↑(r • d1) : Localization.Away s) = ↑r * ↑d1 from MulMemClass.coe_mul ..,
        mul_left_comm]
    obtain ⟨e, he, he_eq⟩ := h1
    exact ⟨r * e, Ideal.mul_mem_left _ r he,
      congrArg ((↑r : Localization.Away s) * ·) he_eq⟩

/-- **Left multiplication continuity** for the localization topology (Wedhorn §5.51, §8.1). -/
theorem locNhd_leftMul (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (x : Localization.Away s) (i : ℕ) :
    ∃ j, (locNhd P T s j : Set (Localization.Away s)) ⊆
      (x * ·) ⁻¹' (locNhd P T s i : Set (Localization.Away s)) := by
  obtain ⟨N, hN⟩ := hopen
  induction x using Localization.induction_on with
  | H p =>
    obtain ⟨a, ⟨_, k, rfl⟩⟩ := p
    induction k generalizing a with
    | zero =>
      simp only [pow_zero]
      obtain ⟨j, hj⟩ := locNhd_algMap_step P T s i a
      exact ⟨j, fun _ hy ↦ hj _ hy⟩
    | succ k ih =>
      have hk1 : s ^ (k + 1) ∈ Submonoid.powers s := ⟨k + 1, rfl⟩
      have hk : s ^ k ∈ Submonoid.powers s := ⟨k, rfl⟩
      have hdecomp : Localization.mk a ⟨s ^ (k + 1), hk1⟩ =
          Localization.mk a ⟨s ^ k, hk⟩ * divByS 1 s := by
        rw [divByS, ← Localization.mk_eq_mk', Localization.mk_mul, mul_one]
        congr 1; exact Subtype.ext (pow_succ s k)
      obtain ⟨j₁, hj₁⟩ := ih a
      refine ⟨j₁ + N, fun y hy ↦ ?_⟩
      simp only [Set.mem_preimage]
      rw [hdecomp, mul_assoc]
      exact hj₁ (locNhd_invS_step P T s N hN j₁ _ hy)

/-- The `RingSubgroupsBasis` for the localization topology on `Aₛ`. -/
noncomputable def locBasis (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    RingSubgroupsBasis (locNhd P T s) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (locNhd_antitone P T s (le_max_left i j))
        (locNhd_antitone P T s (le_max_right i j))⟩)
    (locNhd_mul P T s)
    (locNhd_leftMul P T s hopen)

/-- The localization topology on `Localization.Away s` with `0`-neighborhoods `{image(Jⁿ)}`. -/
@[reducible] noncomputable def locTopology (P : PairOfDefinition A) (T : Finset A)
    (s : A) (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    TopologicalSpace (Localization.Away s) :=
  (locBasis P T s hopen).topology

end Basis

/-! ### Universal property of the localization topology (Wedhorn §5.51)

The localization topology is the coarsest ring topology on `Localization.Away s`
making `algebraMap : A → Localization.Away s` continuous. Equivalently: if `τ` is
any ring topology making `algebraMap` continuous, then `locTopology P T s hopen ≤ τ`.

**Proof idea:** Under a ring topology `τ` with `algebraMap` continuous:
- `algebraMap(val(P.I^n))` is a `τ`-neighborhood of 0 (continuous preimage).
- `locSubring P T s` generates the ring, and multiplication is `τ`-continuous.
- Each `locNhd P T s n` (image of `(locIdeal)^n`) is contained in a `τ`-neighborhood
  because it's an ideal of `locSubring` times the `algebraMap(val(P.I^n))` generators.

This requires showing that `locSubring P T s` is `τ`-bounded, which follows from
`algebraMap(P.A₀)` being bounded (continuous image of bounded set) and `{divByS t s}`
being finite. -/

section UniversalProperty

variable [IsTopologicalRing A]

/-- **Universal property of `locTopology`** (Wedhorn §5.51): a ring homomorphism FROM
`(Localization.Away s, locTopology)` is continuous if `algebraMap` is continuous
for the TARGET topology.

Given a ring homomorphism `f : Localization.Away s →+* B` into a topological ring `B`,
if `f ∘ algebraMap : A → B` is continuous, then `f` is continuous from `locTopology`
to the topology on `B`. This is because the localization topology is the coarsest
ring topology making `algebraMap` continuous.

**Key sub-facts used:**
1. `algebraMap(val(P.I^n))` is small under `f` (by continuity of `f ∘ algebraMap`).
2. `val(P.I^n) * P.A₀ ⊆ val(P.I^n)` (ideal absorption in the ring of definition).
3. `locNhd_leftMul`-type argument for `f(divByS t s)`: each such element is fixed,
   and continuity of multiplication in `B` absorbs finitely many factors.
4. `locNhd n = image of Ideal.map algebraMapD (P.I^n)`, and elements of this ideal
   are sums of `algebraMapD(b) * r` for `b ∈ P.I^n, r ∈ locSubring`. Since `r` is
   a polynomial in `algebraMap(P.A₀)` (absorbed by sub-fact 2) and `{divByS t s}`
   (absorbed by sub-fact 3), the `f`-image lands in a neighborhood of 0 in `B`.

**Wedhorn reference:** Proposition 5.51, Remark 5.33, Section 8.1. -/
theorem locTopology_continuous_lift {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (f : Localization.Away s →+* B)
    (hf_alg : Continuous (f.comp (algebraMap A (Localization.Away s)))) :
    @Continuous _ _ (locTopology P T s hopen) _ f := by
  -- It suffices to show f is continuous at 0 (since f is a group hom).
  -- For each neighborhood U of 0 in B, we need f⁻¹(U) to contain some locNhd n.
  -- Since f ∘ algebraMap is continuous, algebraMap⁻¹(f⁻¹(U)) ∈ nhds(0, A).
  -- So val(P.I^k) ⊆ algebraMap⁻¹(f⁻¹(U)) for some k, meaning
  -- f(algebraMap(val(P.I^k))) ⊆ U.
  -- Then locNhd n (for n ≥ k) maps under f into a neighborhood of 0 in B,
  -- using ideal absorption (sub-fact 2) and continuity of multiplication in B
  -- for the divByS factors (sub-fact 3).
  sorry

end UniversalProperty

/-! ### The `hopen` condition for `s = 1` -/

/-- The `hopen` condition holds trivially when `s = 1`. -/
theorem hopen_away_one (P : PairOfDefinition A) (T : Finset A) :
    ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) (1 : A) ∈ locSubring P T (1 : A) :=
  ⟨0, fun b _ ↦ by rw [divByS_eq_algebraMap]; exact algebraMap_mem_locSubring P T 1 b.2⟩

/-! ### Remark 8.3 infrastructure: `D = A₀` when `s = 1`, `T = {1}` -/

/-- When `T = {1}` and `s = 1`, `D = A₀.map (algebraMap A Aₛ)`. -/
theorem locSubring_singleton_one (P : PairOfDefinition A) :
    locSubring P {1} (1 : A) =
      P.A₀.map (algebraMap A (Localization.Away (1 : A))) := by
  unfold locSubring
  have h_range : Set.range (fun t : ({1} : Finset A) ↦
      divByS (↑t : A) (1 : A)) ⊆
      (algebraMap A (Localization.Away (1 : A))) '' (P.A₀ : Set A) := by
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    simp only [Finset.mem_singleton] at ht; subst ht
    exact ⟨1, P.A₀.one_mem, (divByS_eq_algebraMap (1 : A)).symm ▸ rfl⟩
  rw [Set.union_eq_left.mpr h_range, ← Subring.coe_map]
  exact Subring.closure_eq _

/-- `algebraMapD` is surjective when `T = {1}` and `s = 1`. -/
theorem algebraMapD_surjective_one (P : PairOfDefinition A) :
    Function.Surjective (algebraMapD P {1} (1 : A)) := by
  intro ⟨x, hx⟩
  rw [locSubring_singleton_one] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩

section Remark83Topology

variable [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- The localization neighborhoods at `s = 1`, `T = {1}` are the images of `I^n`. -/
theorem locNhd_singleton_one_eq (P : PairOfDefinition A) (n : ℕ) :
    (locNhd P {1} (1 : A) n : Set (Localization.Away (1 : A))) =
      (algebraMap A (Localization.Away (1 : A))) ''
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) := by
  ext x; constructor
  · rintro ⟨d, hd, rfl⟩
    rw [locIdeal, ← Ideal.map_pow] at hd
    haveI : RingHomSurjective (algebraMapD P {1} (1 : A)) := ⟨algebraMapD_surjective_one P⟩
    rw [Ideal.map_eq_submodule_map] at hd
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hd
    exact ⟨↑b, ⟨b, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨algebraMapD P {1} 1 b,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb, rfl⟩

/-- At `s = 1`, `T = {1}`, the localization topology has the same `0`-neighborhood basis as `A`. -/
theorem locTopology_hasBasis_singleton_one (P : PairOfDefinition A) :
    letI := locTopology P {1} (1 : A) (hopen_away_one P {1})
    (nhds (0 : Localization.Away (1 : A))).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (algebraMap A (Localization.Away (1 : A))) ''
        (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀))) :=
  (locBasis P {1} 1 (hopen_away_one P {1})).hasBasis_nhds_zero.congr
    (fun _ ↦ Iff.rfl) (fun n _ ↦ locNhd_singleton_one_eq P n)

end Remark83Topology

end ValuationSpectrum
